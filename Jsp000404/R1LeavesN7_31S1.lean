import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5048000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_R_s0_x1_x1_x1_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2249 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2576 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2850 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2852 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2853 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2854 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2855 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 5 (by decide) (by decide) with h2856 | h2856
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2857 | h2857
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2858 | h2858
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2859 | h2859
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2860 | h2860
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2861 | h2861
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2862 | h2862
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2863 | h2863
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2864 | h2864
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2865 | h2865
                    · linarith only [h2852, h2865, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2867 | h2867
                      · linarith only [h2249, h2856, h2858, h2864, h2865, h2867, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2869 | h2869
                        · linarith only [h2249, h2856, h2858, h2864, h2865, h2867, h2869, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                        · rcases h0bigk with h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c
                          · have p2871_0 := h2871c.1
                            have p2871_1 := h2871c.2.1
                            have p2871_2 := h2871c.2.2.1
                            have p2871_3 := h2871c.2.2.2
                            linarith only [hlam, p2871_0]
                          · have p2871_0 := h2871c.1
                            have p2871_1 := h2871c.2.1
                            have p2871_2 := h2871c.2.2.1
                            have p2871_3 := h2871c.2.2.2
                            linarith only [h0, hlam, p2871_1]
                          · have p2871_0 := h2871c.1
                            have p2871_1 := h2871c.2.1
                            have p2871_2 := h2871c.2.2.1
                            have p2871_3 := h2871c.2.2.2
                            linarith only [h2249, hlam, p2871_0]
                          · have p2871_0 := h2871c.1
                            have p2871_1 := h2871c.2.1
                            have p2871_2 := h2871c.2.2.1
                            have p2871_3 := h2871c.2.2.2
                            linarith only [h2576, hlam, p2871_1]
                          · have p2871_0 := h2871c.1
                            have p2871_1 := h2871c.2.1
                            have p2871_2 := h2871c.2.2.1
                            have p2871_3 := h2871c.2.2.2
                            linarith only [h2850, hlam, p2871_1]
                          · have p2871_0 := h2871c.1
                            have p2871_1 := h2871c.2.1
                            have p2871_2 := h2871c.2.2.1
                            have p2871_3 := h2871c.2.2.2
                            rcases p2871_3 (m.d 0 1) (by simp) with h2877 | h2877
                            · linarith only [h0, h2877, hlam]
                            · rcases p2871_3 (m.d 0 2) (by simp) with h2879 | h2879
                              · rcases p2871_3 (m.d 0 3) (by simp) with h2880 | h2880
                                · linarith only [h2852, h2880, hlam]
                                · linarith only [h2249, h2880, hlam]
                              · linarith only [h0, h2879, hlam]
                          · have p2871_0 := h2871c.1
                            have p2871_1 := h2871c.2.1
                            have p2871_2 := h2871c.2.2.1
                            have p2871_3 := h2871c.2.2.2
                            linarith only [hlam, p2871_0]
                          · have p2871_0 := h2871c.1
                            have p2871_1 := h2871c.2.1
                            have p2871_2 := h2871c.2.2.1
                            have p2871_3 := h2871c.2.2.2
                            linarith only [h0, h2855, h2857, h2865, h2869, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2871_1]
                          · have p2871_0 := h2871c.1
                            have p2871_1 := h2871c.2.1
                            have p2871_2 := h2871c.2.2.1
                            have p2871_3 := h2871c.2.2.2
                            linarith only [h0, h2857, h2864, h2865, h2869, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2871_1]
                          · have p2871_0 := h2871c.1
                            have p2871_1 := h2871c.2.1
                            have p2871_2 := h2871c.2.2.1
                            have p2871_3 := h2871c.2.2.2
                            linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p2871_1, u5ehi0]
                          · have p2871_0 := h2871c.1
                            have p2871_1 := h2871c.2.1
                            have p2871_2 := h2871c.2.2.1
                            have p2871_3 := h2871c.2.2.2
                            rcases p2871_3 (m.d 0 1) (by simp) with h2888 | h2888
                            · linarith only [h2249, h2888, hlam]
                            · rcases p2871_3 (m.d 0 2) (by simp) with h2890 | h2890
                              · rcases p2871_3 (m.d 0 3) (by simp) with h2891 | h2891
                                · rcases p2871_3 (m.d 0 4) (by simp) with h2892 | h2892
                                  · linarith only [h2855, h2892, hlam]
                                  · linarith only [h2576, h2892, hlam]
                                · linarith only [h2249, h2891, hlam]
                              · linarith only [h0, h2890, hlam]
                          · have p2871_0 := h2871c.1
                            have p2871_1 := h2871c.2.1
                            have p2871_2 := h2871c.2.2.1
                            have p2871_3 := h2871c.2.2.2
                            linarith only [h2852, hlam, p2871_1]
                          · have p2871_0 := h2871c.1
                            have p2871_1 := h2871c.2.1
                            have p2871_2 := h2871c.2.2.1
                            have p2871_3 := h2871c.2.2.2
                            linarith only [hlam, p2871_0]
                          · have p2871_0 := h2871c.1
                            have p2871_1 := h2871c.2.1
                            have p2871_2 := h2871c.2.2.1
                            have p2871_3 := h2871c.2.2.2
                            linarith only [h2857, h2864, h2865, h2869, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p2871_1]
                          · have p2871_0 := h2871c.1
                            have p2871_1 := h2871c.2.1
                            have p2871_2 := h2871c.2.2.1
                            have p2871_3 := h2871c.2.2.2
                            linarith only [h2249, h2857, h2858, h2864, h2865, h2869, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2871_1]
                          · have p2871_0 := h2871c.1
                            have p2871_1 := h2871c.2.1
                            have p2871_2 := h2871c.2.2.1
                            have p2871_3 := h2871c.2.2.2
                            rcases p2871_3 (m.d 0 1) (by simp) with h2901 | h2901
                            · linarith only [h2576, h2901, hlam]
                            · rcases p2871_3 (m.d 0 2) (by simp) with h2903 | h2903
                              · rcases p2871_3 (m.d 0 3) (by simp) with h2904 | h2904
                                · rcases p2871_3 (m.d 0 4) (by simp) with h2905 | h2905
                                  · rcases p2871_3 (m.d 0 5) (by simp) with h2906 | h2906
                                    · linarith only [h2857, h2906, hlam]
                                    · linarith only [h2850, h2906, hlam]
                                  · linarith only [h2576, h2905, hlam]
                                · linarith only [h2249, h2904, hlam]
                              · linarith only [h0, h2903, hlam]
                          · have p2871_0 := h2871c.1
                            have p2871_1 := h2871c.2.1
                            have p2871_2 := h2871c.2.2.1
                            have p2871_3 := h2871c.2.2.2
                            linarith only [h2853, hlam, p2871_0]
                          · have p2871_0 := h2871c.1
                            have p2871_1 := h2871c.2.1
                            have p2871_2 := h2871c.2.2.1
                            have p2871_3 := h2871c.2.2.2
                            linarith only [h2855, hlam, p2871_0]
                          · have p2871_0 := h2871c.1
                            have p2871_1 := h2871c.2.1
                            have p2871_2 := h2871c.2.2.1
                            have p2871_3 := h2871c.2.2.2
                            linarith only [hlam, p2871_0]
                          · have p2871_0 := h2871c.1
                            have p2871_1 := h2871c.2.1
                            have p2871_2 := h2871c.2.2.1
                            have p2871_3 := h2871c.2.2.2
                            linarith only [h2576, h2857, h2858, h2861, h2864, h2865, h2869, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2871_1]
                          · have p2871_0 := h2871c.1
                            have p2871_1 := h2871c.2.1
                            have p2871_2 := h2871c.2.2.1
                            have p2871_3 := h2871c.2.2.2
                            rcases p2871_3 (m.d 0 1) (by simp) with h2916 | h2916
                            · linarith only [h2850, h2916, hlam]
                            · rcases p2871_3 (m.d 0 2) (by simp) with h2918 | h2918
                              · rcases p2871_3 (m.d 0 3) (by simp) with h2919 | h2919
                                · rcases p2871_3 (m.d 0 4) (by simp) with h2920 | h2920
                                  · rcases p2871_3 (m.d 0 5) (by simp) with h2921 | h2921
                                    · rcases h2bigk with h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c
                                      · have p2922_0 := h2922c.1
                                        have p2922_1 := h2922c.2.1
                                        have p2922_2 := h2922c.2.2.1
                                        have p2922_3 := h2922c.2.2.2
                                        linarith only [hlam, p2922_0]
                                      · have p2922_0 := h2922c.1
                                        have p2922_1 := h2922c.2.1
                                        have p2922_2 := h2922c.2.2.1
                                        have p2922_3 := h2922c.2.2.2
                                        linarith only [h0, hlam, p2922_1]
                                      · have p2922_0 := h2922c.1
                                        have p2922_1 := h2922c.2.1
                                        have p2922_2 := h2922c.2.2.1
                                        have p2922_3 := h2922c.2.2.2
                                        rcases p2922_3 (m.d 0 2) (by simp) with h2925 | h2925
                                        · rcases p2922_3 (m.d 1 2) (by simp) with h2926 | h2926
                                          · rcases p2922_3 (m.d 2 3) (by simp) with h2927 | h2927
                                            · linarith only [h2927, hlam, p2922_0]
                                            · rcases p2922_3 (m.d 2 4) (by simp) with h2929 | h2929
                                              · linarith only [h2853, h2929, hlam]
                                              · rcases p2922_3 (m.d 2 5) (by simp) with h2931 | h2931
                                                · linarith only [h2854, h2931, hlam]
                                                · linarith only [h2865, h2931, hlam]
                                          · linarith only [h2858, h2926, hlam]
                                        · linarith only [h2925, hlam, p2922_0]
                                      · have p2922_0 := h2922c.1
                                        have p2922_1 := h2922c.2.1
                                        have p2922_2 := h2922c.2.2.1
                                        have p2922_3 := h2922c.2.2.2
                                        rcases p2922_3 (m.d 0 2) (by simp) with h2936 | h2936
                                        · rcases p2922_3 (m.d 1 2) (by simp) with h2937 | h2937
                                          · rcases p2922_3 (m.d 2 3) (by simp) with h2938 | h2938
                                            · linarith only [h2852, h2938, hlam]
                                            · linarith only [h2864, h2938, hlam]
                                          · linarith only [h2859, h2937, hlam]
                                        · linarith only [h2936, hlam, p2922_0]
                                      · have p2922_0 := h2922c.1
                                        have p2922_1 := h2922c.2.1
                                        have p2922_2 := h2922c.2.2.1
                                        have p2922_3 := h2922c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p2922_1, u5ehi2]
                                      · have p2922_0 := h2922c.1
                                        have p2922_1 := h2922c.2.1
                                        have p2922_2 := h2922c.2.2.1
                                        have p2922_3 := h2922c.2.2.2
                                        linarith only [h2852, h2864, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2922_1]
                                      · have p2922_0 := h2922c.1
                                        have p2922_1 := h2922c.2.1
                                        have p2922_2 := h2922c.2.2.1
                                        have p2922_3 := h2922c.2.2.2
                                        linarith only [hlam, p2922_0]
                                      · have p2922_0 := h2922c.1
                                        have p2922_1 := h2922c.2.1
                                        have p2922_2 := h2922c.2.2.1
                                        have p2922_3 := h2922c.2.2.2
                                        rcases p2922_3 (m.d 0 2) (by simp) with h2946 | h2946
                                        · linarith only [h0, h2946, hlam]
                                        · linarith only [h2852, h2946, hlam]
                                      · have p2922_0 := h2922c.1
                                        have p2922_1 := h2922c.2.1
                                        have p2922_2 := h2922c.2.2.1
                                        have p2922_3 := h2922c.2.2.2
                                        rcases p2922_3 (m.d 0 2) (by simp) with h2949 | h2949
                                        · linarith only [h0, h2949, hlam]
                                        · linarith only [h2853, h2949, hlam]
                                      · have p2922_0 := h2922c.1
                                        have p2922_1 := h2922c.2.1
                                        have p2922_2 := h2922c.2.2.1
                                        have p2922_3 := h2922c.2.2.2
                                        linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p2922_1, u5ehi2]
                                      · have p2922_0 := h2922c.1
                                        have p2922_1 := h2922c.2.1
                                        have p2922_2 := h2922c.2.2.1
                                        have p2922_3 := h2922c.2.2.2
                                        linarith only [h2852, hlam, p2922_0]
                                      · have p2922_0 := h2922c.1
                                        have p2922_1 := h2922c.2.1
                                        have p2922_2 := h2922c.2.2.1
                                        have p2922_3 := h2922c.2.2.2
                                        linarith only [h2858, hlam, p2922_0]
                                      · have p2922_0 := h2922c.1
                                        have p2922_1 := h2922c.2.1
                                        have p2922_2 := h2922c.2.2.1
                                        have p2922_3 := h2922c.2.2.2
                                        linarith only [hlam, p2922_0]
                                      · have p2922_0 := h2922c.1
                                        have p2922_1 := h2922c.2.1
                                        have p2922_2 := h2922c.2.2.1
                                        have p2922_3 := h2922c.2.2.2
                                        linarith only [h2865, h2869, hc24, hc45, hlam, hphi, p2922_1]
                                      · have p2922_0 := h2922c.1
                                        have p2922_1 := h2922c.2.1
                                        have p2922_2 := h2922c.2.2.1
                                        have p2922_3 := h2922c.2.2.2
                                        linarith only [h2865, hlam, p2922_0]
                                      · have p2922_0 := h2922c.1
                                        have p2922_1 := h2922c.2.1
                                        have p2922_2 := h2922c.2.2.1
                                        have p2922_3 := h2922c.2.2.2
                                        linarith only [h2853, hlam, p2922_0]
                                      · have p2922_0 := h2922c.1
                                        have p2922_1 := h2922c.2.1
                                        have p2922_2 := h2922c.2.2.1
                                        have p2922_3 := h2922c.2.2.2
                                        linarith only [h2859, hlam, p2922_0]
                                      · have p2922_0 := h2922c.1
                                        have p2922_1 := h2922c.2.1
                                        have p2922_2 := h2922c.2.2.1
                                        have p2922_3 := h2922c.2.2.2
                                        linarith only [h2864, hlam, p2922_1]
                                      · have p2922_0 := h2922c.1
                                        have p2922_1 := h2922c.2.1
                                        have p2922_2 := h2922c.2.2.1
                                        have p2922_3 := h2922c.2.2.2
                                        linarith only [hlam, p2922_0]
                                      · have p2922_0 := h2922c.1
                                        have p2922_1 := h2922c.2.1
                                        have p2922_2 := h2922c.2.2.1
                                        have p2922_3 := h2922c.2.2.2
                                        linarith only [h2867, hlam, p2922_1]
                                      · have p2922_0 := h2922c.1
                                        have p2922_1 := h2922c.2.1
                                        have p2922_2 := h2922c.2.2.1
                                        have p2922_3 := h2922c.2.2.2
                                        linarith only [h2854, hlam, p2922_0]
                                      · have p2922_0 := h2922c.1
                                        have p2922_1 := h2922c.2.1
                                        have p2922_2 := h2922c.2.2.1
                                        have p2922_3 := h2922c.2.2.2
                                        linarith only [h2860, hlam, p2922_0]
                                      · have p2922_0 := h2922c.1
                                        have p2922_1 := h2922c.2.1
                                        have p2922_2 := h2922c.2.2.1
                                        have p2922_3 := h2922c.2.2.2
                                        linarith only [h0, h2854, h2864, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2922_1]
                                      · have p2922_0 := h2922c.1
                                        have p2922_1 := h2922c.2.1
                                        have p2922_2 := h2922c.2.2.1
                                        have p2922_3 := h2922c.2.2.2
                                        rcases p2922_3 (m.d 0 2) (by simp) with h2966 | h2966
                                        · rcases p2922_3 (m.d 1 2) (by simp) with h2967 | h2967
                                          · rcases p2922_3 (m.d 2 3) (by simp) with h2968 | h2968
                                            · linarith only [h2865, h2968, hlam]
                                            · linarith only [h2864, h2968, hlam]
                                          · linarith only [h2859, h2967, hlam]
                                        · linarith only [h2853, h2966, hlam]
                                      · have p2922_0 := h2922c.1
                                        have p2922_1 := h2922c.2.1
                                        have p2922_2 := h2922c.2.2.1
                                        have p2922_3 := h2922c.2.2.2
                                        linarith only [hlam, p2922_0]
                                    · linarith only [h2850, h2921, hlam]
                                  · linarith only [h2576, h2920, hlam]
                                · linarith only [h2249, h2919, hlam]
                              · linarith only [h0, h2918, hlam]
                          · have p2871_0 := h2871c.1
                            have p2871_1 := h2871c.2.1
                            have p2871_2 := h2871c.2.2.1
                            have p2871_3 := h2871c.2.2.2
                            linarith only [h2854, hlam, p2871_1]
                          · have p2871_0 := h2871c.1
                            have p2871_1 := h2871c.2.1
                            have p2871_2 := h2871c.2.2.1
                            have p2871_3 := h2871c.2.2.2
                            linarith only [h2856, hlam, p2871_0]
                          · have p2871_0 := h2871c.1
                            have p2871_1 := h2871c.2.1
                            have p2871_2 := h2871c.2.2.1
                            have p2871_3 := h2871c.2.2.2
                            linarith only [h2857, hlam, p2871_1]
                          · have p2871_0 := h2871c.1
                            have p2871_1 := h2871c.2.1
                            have p2871_2 := h2871c.2.2.1
                            have p2871_3 := h2871c.2.2.2
                            linarith only [hlam, p2871_0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2982 | h2982
                    · linarith only [h2864, h2982, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2984 | h2984
                      · linarith only [h0, h2853, h2984, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2986 | h2986
                        · linarith only [h2249, h2855, h2858, h2986, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                        · rcases h0bigk with h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c
                          · have p2988_0 := h2988c.1
                            have p2988_1 := h2988c.2.1
                            have p2988_2 := h2988c.2.2.1
                            have p2988_3 := h2988c.2.2.2
                            linarith only [hlam, p2988_0]
                          · have p2988_0 := h2988c.1
                            have p2988_1 := h2988c.2.1
                            have p2988_2 := h2988c.2.2.1
                            have p2988_3 := h2988c.2.2.2
                            linarith only [h0, hlam, p2988_1]
                          · have p2988_0 := h2988c.1
                            have p2988_1 := h2988c.2.1
                            have p2988_2 := h2988c.2.2.1
                            have p2988_3 := h2988c.2.2.2
                            linarith only [h2249, hlam, p2988_0]
                          · have p2988_0 := h2988c.1
                            have p2988_1 := h2988c.2.1
                            have p2988_2 := h2988c.2.2.1
                            have p2988_3 := h2988c.2.2.2
                            linarith only [h2576, hlam, p2988_1]
                          · have p2988_0 := h2988c.1
                            have p2988_1 := h2988c.2.1
                            have p2988_2 := h2988c.2.2.1
                            have p2988_3 := h2988c.2.2.2
                            linarith only [h2850, hlam, p2988_1]
                          · have p2988_0 := h2988c.1
                            have p2988_1 := h2988c.2.1
                            have p2988_2 := h2988c.2.2.1
                            have p2988_3 := h2988c.2.2.2
                            rcases p2988_3 (m.d 0 1) (by simp) with h2994 | h2994
                            · linarith only [h0, h2994, hlam]
                            · rcases p2988_3 (m.d 0 2) (by simp) with h2996 | h2996
                              · rcases p2988_3 (m.d 0 3) (by simp) with h2997 | h2997
                                · linarith only [h2852, h2997, hlam]
                                · linarith only [h2249, h2997, hlam]
                              · linarith only [h0, h2996, hlam]
                          · have p2988_0 := h2988c.1
                            have p2988_1 := h2988c.2.1
                            have p2988_2 := h2988c.2.2.1
                            have p2988_3 := h2988c.2.2.2
                            linarith only [hlam, p2988_0]
                          · have p2988_0 := h2988c.1
                            have p2988_1 := h2988c.2.1
                            have p2988_2 := h2988c.2.2.1
                            have p2988_3 := h2988c.2.2.2
                            linarith only [h0, h2855, h2864, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2988_1]
                          · have p2988_0 := h2988c.1
                            have p2988_1 := h2988c.2.1
                            have p2988_2 := h2988c.2.2.1
                            have p2988_3 := h2988c.2.2.2
                            linarith only [h0, h2857, h2864, h2986, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2988_1]
                          · have p2988_0 := h2988c.1
                            have p2988_1 := h2988c.2.1
                            have p2988_2 := h2988c.2.2.1
                            have p2988_3 := h2988c.2.2.2
                            linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p2988_1, u5ehi0]
                          · have p2988_0 := h2988c.1
                            have p2988_1 := h2988c.2.1
                            have p2988_2 := h2988c.2.2.1
                            have p2988_3 := h2988c.2.2.2
                            rcases p2988_3 (m.d 0 1) (by simp) with h3005 | h3005
                            · linarith only [h2249, h3005, hlam]
                            · rcases p2988_3 (m.d 0 2) (by simp) with h3007 | h3007
                              · rcases p2988_3 (m.d 0 3) (by simp) with h3008 | h3008
                                · rcases p2988_3 (m.d 0 4) (by simp) with h3009 | h3009
                                  · linarith only [h2855, h3009, hlam]
                                  · linarith only [h2576, h3009, hlam]
                                · linarith only [h2249, h3008, hlam]
                              · linarith only [h0, h3007, hlam]
                          · have p2988_0 := h2988c.1
                            have p2988_1 := h2988c.2.1
                            have p2988_2 := h2988c.2.2.1
                            have p2988_3 := h2988c.2.2.2
                            linarith only [h2852, hlam, p2988_1]
                          · have p2988_0 := h2988c.1
                            have p2988_1 := h2988c.2.1
                            have p2988_2 := h2988c.2.2.1
                            have p2988_3 := h2988c.2.2.2
                            linarith only [hlam, p2988_0]
                          · have p2988_0 := h2988c.1
                            have p2988_1 := h2988c.2.1
                            have p2988_2 := h2988c.2.2.1
                            have p2988_3 := h2988c.2.2.2
                            linarith only [h2857, h2864, h2986, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2988_1]
                          · have p2988_0 := h2988c.1
                            have p2988_1 := h2988c.2.1
                            have p2988_2 := h2988c.2.2.1
                            have p2988_3 := h2988c.2.2.2
                            linarith only [h2249, h2857, h2858, h2864, h2986, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2988_1]
                          · have p2988_0 := h2988c.1
                            have p2988_1 := h2988c.2.1
                            have p2988_2 := h2988c.2.2.1
                            have p2988_3 := h2988c.2.2.2
                            rcases p2988_3 (m.d 0 1) (by simp) with h3018 | h3018
                            · linarith only [h2576, h3018, hlam]
                            · rcases p2988_3 (m.d 0 2) (by simp) with h3020 | h3020
                              · rcases p2988_3 (m.d 0 3) (by simp) with h3021 | h3021
                                · rcases p2988_3 (m.d 0 4) (by simp) with h3022 | h3022
                                  · rcases p2988_3 (m.d 0 5) (by simp) with h3023 | h3023
                                    · linarith only [h2857, h3023, hlam]
                                    · linarith only [h2850, h3023, hlam]
                                  · linarith only [h2576, h3022, hlam]
                                · linarith only [h2249, h3021, hlam]
                              · linarith only [h0, h3020, hlam]
                          · have p2988_0 := h2988c.1
                            have p2988_1 := h2988c.2.1
                            have p2988_2 := h2988c.2.2.1
                            have p2988_3 := h2988c.2.2.2
                            linarith only [h2853, hlam, p2988_0]
                          · have p2988_0 := h2988c.1
                            have p2988_1 := h2988c.2.1
                            have p2988_2 := h2988c.2.2.1
                            have p2988_3 := h2988c.2.2.2
                            linarith only [h2855, hlam, p2988_0]
                          · have p2988_0 := h2988c.1
                            have p2988_1 := h2988c.2.1
                            have p2988_2 := h2988c.2.2.1
                            have p2988_3 := h2988c.2.2.2
                            linarith only [hlam, p2988_0]
                          · have p2988_0 := h2988c.1
                            have p2988_1 := h2988c.2.1
                            have p2988_2 := h2988c.2.2.1
                            have p2988_3 := h2988c.2.2.2
                            linarith only [h2857, h2864, h2986, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2988_1]
                          · have p2988_0 := h2988c.1
                            have p2988_1 := h2988c.2.1
                            have p2988_2 := h2988c.2.2.1
                            have p2988_3 := h2988c.2.2.2
                            rcases p2988_3 (m.d 0 1) (by simp) with h3033 | h3033
                            · linarith only [h2850, h3033, hlam]
                            · rcases p2988_3 (m.d 0 2) (by simp) with h3035 | h3035
                              · rcases p2988_3 (m.d 0 3) (by simp) with h3036 | h3036
                                · rcases p2988_3 (m.d 0 4) (by simp) with h3037 | h3037
                                  · rcases p2988_3 (m.d 0 5) (by simp) with h3038 | h3038
                                    · rcases h2bigk with h3039c | h3039c | h3039c | h3039c | h3039c | h3039c | h3039c | h3039c | h3039c | h3039c | h3039c | h3039c | h3039c | h3039c | h3039c | h3039c | h3039c | h3039c | h3039c | h3039c | h3039c | h3039c | h3039c | h3039c | h3039c
                                      · have p3039_0 := h3039c.1
                                        have p3039_1 := h3039c.2.1
                                        have p3039_2 := h3039c.2.2.1
                                        have p3039_3 := h3039c.2.2.2
                                        linarith only [hlam, p3039_0]
                                      · have p3039_0 := h3039c.1
                                        have p3039_1 := h3039c.2.1
                                        have p3039_2 := h3039c.2.2.1
                                        have p3039_3 := h3039c.2.2.2
                                        linarith only [h0, hlam, p3039_1]
                                      · have p3039_0 := h3039c.1
                                        have p3039_1 := h3039c.2.1
                                        have p3039_2 := h3039c.2.2.1
                                        have p3039_3 := h3039c.2.2.2
                                        linarith only [h2852, h2855, h2857, h2864, h2986, hlam, p3039_2]
                                      · have p3039_0 := h3039c.1
                                        have p3039_1 := h3039c.2.1
                                        have p3039_2 := h3039c.2.2.1
                                        have p3039_3 := h3039c.2.2.2
                                        rcases p3039_3 (m.d 0 2) (by simp) with h3043 | h3043
                                        · rcases p3039_3 (m.d 1 2) (by simp) with h3044 | h3044
                                          · rcases p3039_3 (m.d 2 3) (by simp) with h3045 | h3045
                                            · linarith only [h2852, h3045, hlam]
                                            · rcases p3039_3 (m.d 2 4) (by simp) with h3047 | h3047
                                              · linarith only [h3047, hlam, p3039_0]
                                              · rcases p3039_3 (m.d 2 5) (by simp) with h3049 | h3049
                                                · linarith only [h2854, h3049, hlam]
                                                · linarith only [h2984, h3049, hlam]
                                          · linarith only [h2859, h3044, hlam]
                                        · linarith only [h3043, hlam, p3039_0]
                                      · have p3039_0 := h3039c.1
                                        have p3039_1 := h3039c.2.1
                                        have p3039_2 := h3039c.2.2.1
                                        have p3039_3 := h3039c.2.2.2
                                        linarith only [hc02, hlam, hphi, ht0b, ht5b, p3039_1, u5ehi2]
                                      · have p3039_0 := h3039c.1
                                        have p3039_1 := h3039c.2.1
                                        have p3039_2 := h3039c.2.2.1
                                        have p3039_3 := h3039c.2.2.2
                                        linarith only [h2852, h2855, h2857, h2864, h2986, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3039_1]
                                      · have p3039_0 := h3039c.1
                                        have p3039_1 := h3039c.2.1
                                        have p3039_2 := h3039c.2.2.1
                                        have p3039_3 := h3039c.2.2.2
                                        linarith only [hlam, p3039_0]
                                      · have p3039_0 := h3039c.1
                                        have p3039_1 := h3039c.2.1
                                        have p3039_2 := h3039c.2.2.1
                                        have p3039_3 := h3039c.2.2.2
                                        linarith only [h0, h2852, h2855, h2857, h2864, h2986, hlam, p3039_2]
                                      · have p3039_0 := h3039c.1
                                        have p3039_1 := h3039c.2.1
                                        have p3039_2 := h3039c.2.2.1
                                        have p3039_3 := h3039c.2.2.2
                                        rcases p3039_3 (m.d 0 2) (by simp) with h3058 | h3058
                                        · linarith only [h0, h3058, hlam]
                                        · linarith only [h2853, h3058, hlam]
                                      · have p3039_0 := h3039c.1
                                        have p3039_1 := h3039c.2.1
                                        have p3039_2 := h3039c.2.2.1
                                        have p3039_3 := h3039c.2.2.2
                                        linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p3039_1, u5ehi2]
                                      · have p3039_0 := h3039c.1
                                        have p3039_1 := h3039c.2.1
                                        have p3039_2 := h3039c.2.2.1
                                        have p3039_3 := h3039c.2.2.2
                                        linarith only [h2852, hlam, p3039_0]
                                      · have p3039_0 := h3039c.1
                                        have p3039_1 := h3039c.2.1
                                        have p3039_2 := h3039c.2.2.1
                                        have p3039_3 := h3039c.2.2.2
                                        linarith only [h2858, hlam, p3039_0]
                                      · have p3039_0 := h3039c.1
                                        have p3039_1 := h3039c.2.1
                                        have p3039_2 := h3039c.2.2.1
                                        have p3039_3 := h3039c.2.2.2
                                        linarith only [hlam, p3039_0]
                                      · have p3039_0 := h3039c.1
                                        have p3039_1 := h3039c.2.1
                                        have p3039_2 := h3039c.2.2.1
                                        have p3039_3 := h3039c.2.2.2
                                        linarith only [h2864, hlam, p3039_0]
                                      · have p3039_0 := h3039c.1
                                        have p3039_1 := h3039c.2.1
                                        have p3039_2 := h3039c.2.2.1
                                        have p3039_3 := h3039c.2.2.2
                                        linarith only [h2982, hlam, p3039_0]
                                      · have p3039_0 := h3039c.1
                                        have p3039_1 := h3039c.2.1
                                        have p3039_2 := h3039c.2.2.1
                                        have p3039_3 := h3039c.2.2.2
                                        linarith only [h2853, hlam, p3039_0]
                                      · have p3039_0 := h3039c.1
                                        have p3039_1 := h3039c.2.1
                                        have p3039_2 := h3039c.2.2.1
                                        have p3039_3 := h3039c.2.2.2
                                        linarith only [h2859, hlam, p3039_0]
                                      · have p3039_0 := h3039c.1
                                        have p3039_1 := h3039c.2.1
                                        have p3039_2 := h3039c.2.2.1
                                        have p3039_3 := h3039c.2.2.2
                                        linarith only [h2852, h2855, h2857, h2864, h2986, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3039_1]
                                      · have p3039_0 := h3039c.1
                                        have p3039_1 := h3039c.2.1
                                        have p3039_2 := h3039c.2.2.1
                                        have p3039_3 := h3039c.2.2.2
                                        linarith only [hlam, p3039_0]
                                      · have p3039_0 := h3039c.1
                                        have p3039_1 := h3039c.2.1
                                        have p3039_2 := h3039c.2.2.1
                                        have p3039_3 := h3039c.2.2.2
                                        linarith only [h2984, hlam, p3039_1]
                                      · have p3039_0 := h3039c.1
                                        have p3039_1 := h3039c.2.1
                                        have p3039_2 := h3039c.2.2.1
                                        have p3039_3 := h3039c.2.2.2
                                        linarith only [h2854, hlam, p3039_0]
                                      · have p3039_0 := h3039c.1
                                        have p3039_1 := h3039c.2.1
                                        have p3039_2 := h3039c.2.2.1
                                        have p3039_3 := h3039c.2.2.2
                                        linarith only [h2860, hlam, p3039_0]
                                      · have p3039_0 := h3039c.1
                                        have p3039_1 := h3039c.2.1
                                        have p3039_2 := h3039c.2.2.1
                                        have p3039_3 := h3039c.2.2.2
                                        rcases p3039_3 (m.d 0 2) (by simp) with h3074 | h3074
                                        · rcases p3039_3 (m.d 1 2) (by simp) with h3075 | h3075
                                          · rcases p3039_3 (m.d 2 3) (by simp) with h3076 | h3076
                                            · linarith only [h2982, h3076, hlam]
                                            · rcases p3039_3 (m.d 2 4) (by simp) with h3078 | h3078
                                              · linarith only [h2984, h3078, hlam]
                                              · linarith only [h2864, h3078, hlam]
                                          · linarith only [h2858, h3075, hlam]
                                        · linarith only [h2852, h3074, hlam]
                                      · have p3039_0 := h3039c.1
                                        have p3039_1 := h3039c.2.1
                                        have p3039_2 := h3039c.2.2.1
                                        have p3039_3 := h3039c.2.2.2
                                        rcases p3039_3 (m.d 0 2) (by simp) with h3083 | h3083
                                        · rcases p3039_3 (m.d 1 2) (by simp) with h3084 | h3084
                                          · rcases p3039_3 (m.d 2 3) (by simp) with h3085 | h3085
                                            · linarith only [h2982, h3085, hlam]
                                            · rcases p3039_3 (m.d 2 4) (by simp) with h3087 | h3087
                                              · linarith only [h2984, h3087, hlam]
                                              · rcases p3039_3 (m.d 2 5) (by simp) with h3089 | h3089
                                                · rcases h3bigk with h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c
                                                  · have p3090_0 := h3090c.1
                                                    have p3090_1 := h3090c.2.1
                                                    have p3090_2 := h3090c.2.2.1
                                                    have p3090_3 := h3090c.2.2.2
                                                    linarith only [hlam, p3090_0]
                                                  · have p3090_0 := h3090c.1
                                                    have p3090_1 := h3090c.2.1
                                                    have p3090_2 := h3090c.2.2.1
                                                    have p3090_3 := h3090c.2.2.2
                                                    linarith only [h2249, hlam, p3090_1]
                                                  · have p3090_0 := h3090c.1
                                                    have p3090_1 := h3090c.2.1
                                                    have p3090_2 := h3090c.2.2.1
                                                    have p3090_3 := h3090c.2.2.2
                                                    linarith only [h2856, h2864, h2982, hlam, p3039_1, p3090_2]
                                                  · have p3090_0 := h3090c.1
                                                    have p3090_1 := h3090c.2.1
                                                    have p3090_2 := h3090c.2.2.1
                                                    have p3090_3 := h3090c.2.2.2
                                                    rcases p3090_3 (m.d 0 3) (by simp) with h3094 | h3094
                                                    · rcases p3090_3 (m.d 1 3) (by simp) with h3095 | h3095
                                                      · rcases p3090_3 (m.d 2 3) (by simp) with h3096 | h3096
                                                        · linarith only [h2852, h3096, hlam]
                                                        · rcases p3090_3 (m.d 3 4) (by simp) with h3098 | h3098
                                                          · linarith only [h3098, hlam, p3090_0]
                                                          · rcases p3090_3 (m.d 3 5) (by simp) with h3100 | h3100
                                                            · linarith only [h2856, h3100, hlam]
                                                            · linarith only [h2986, h3100, hlam]
                                                      · linarith only [h2861, h3095, hlam]
                                                    · linarith only [h3094, hlam, p3090_0]
                                                  · have p3090_0 := h3090c.1
                                                    have p3090_1 := h3090c.2.1
                                                    have p3090_2 := h3090c.2.2.1
                                                    have p3090_3 := h3090c.2.2.2
                                                    linarith only [h2864, h2982, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3039_1, p3090_1]
                                                  · have p3090_0 := h3090c.1
                                                    have p3090_1 := h3090c.2.1
                                                    have p3090_2 := h3090c.2.2.1
                                                    have p3090_3 := h3090c.2.2.2
                                                    linarith only [h2855, h2857, h2858, h2864, h2982, h2986, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3039_1, p3090_1]
                                                  · have p3090_0 := h3090c.1
                                                    have p3090_1 := h3090c.2.1
                                                    have p3090_2 := h3090c.2.2.1
                                                    have p3090_3 := h3090c.2.2.2
                                                    linarith only [hlam, p3090_0]
                                                  · have p3090_0 := h3090c.1
                                                    have p3090_1 := h3090c.2.1
                                                    have p3090_2 := h3090c.2.2.1
                                                    have p3090_3 := h3090c.2.2.2
                                                    linarith only [h2249, h2855, h2857, h2864, h2982, h2986, hlam, p3039_1, p3090_2]
                                                  · have p3090_0 := h3090c.1
                                                    have p3090_1 := h3090c.2.1
                                                    have p3090_2 := h3090c.2.2.1
                                                    have p3090_3 := h3090c.2.2.2
                                                    rcases p3090_3 (m.d 0 3) (by simp) with h3109 | h3109
                                                    · linarith only [h2249, h3109, hlam]
                                                    · linarith only [h2855, h3109, hlam]
                                                  · have p3090_0 := h3090c.1
                                                    have p3090_1 := h3090c.2.1
                                                    have p3090_2 := h3090c.2.2.1
                                                    have p3090_3 := h3090c.2.2.2
                                                    linarith only [h2864, h2982, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3039_1, p3090_1]
                                                  · have p3090_0 := h3090c.1
                                                    have p3090_1 := h3090c.2.1
                                                    have p3090_2 := h3090c.2.2.1
                                                    have p3090_3 := h3090c.2.2.2
                                                    linarith only [h2852, hlam, p3090_0]
                                                  · have p3090_0 := h3090c.1
                                                    have p3090_1 := h3090c.2.1
                                                    have p3090_2 := h3090c.2.2.1
                                                    have p3090_3 := h3090c.2.2.2
                                                    linarith only [h2858, hlam, p3090_0]
                                                  · have p3090_0 := h3090c.1
                                                    have p3090_1 := h3090c.2.1
                                                    have p3090_2 := h3090c.2.2.1
                                                    have p3090_3 := h3090c.2.2.2
                                                    linarith only [hlam, p3090_0]
                                                  · have p3090_0 := h3090c.1
                                                    have p3090_1 := h3090c.2.1
                                                    have p3090_2 := h3090c.2.2.1
                                                    have p3090_3 := h3090c.2.2.2
                                                    linarith only [h2864, hlam, p3090_0]
                                                  · have p3090_0 := h3090c.1
                                                    have p3090_1 := h3090c.2.1
                                                    have p3090_2 := h3090c.2.2.1
                                                    have p3090_3 := h3090c.2.2.2
                                                    linarith only [h2982, hlam, p3090_0]
                                                  · have p3090_0 := h3090c.1
                                                    have p3090_1 := h3090c.2.1
                                                    have p3090_2 := h3090c.2.2.1
                                                    have p3090_3 := h3090c.2.2.2
                                                    linarith only [h2855, hlam, p3090_0]
                                                  · have p3090_0 := h3090c.1
                                                    have p3090_1 := h3090c.2.1
                                                    have p3090_2 := h3090c.2.2.1
                                                    have p3090_3 := h3090c.2.2.2
                                                    linarith only [h2861, hlam, p3090_0]
                                                  · have p3090_0 := h3090c.1
                                                    have p3090_1 := h3090c.2.1
                                                    have p3090_2 := h3090c.2.2.1
                                                    have p3090_3 := h3090c.2.2.2
                                                    linarith only [h2855, h2857, h2986, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3090_1]
                                                  · have p3090_0 := h3090c.1
                                                    have p3090_1 := h3090c.2.1
                                                    have p3090_2 := h3090c.2.2.1
                                                    have p3090_3 := h3090c.2.2.2
                                                    linarith only [hlam, p3090_0]
                                                  · have p3090_0 := h3090c.1
                                                    have p3090_1 := h3090c.2.1
                                                    have p3090_2 := h3090c.2.2.1
                                                    have p3090_3 := h3090c.2.2.2
                                                    linarith only [h2986, hlam, p3090_1]
                                                  · have p3090_0 := h3090c.1
                                                    have p3090_1 := h3090c.2.1
                                                    have p3090_2 := h3090c.2.2.1
                                                    have p3090_3 := h3090c.2.2.2
                                                    linarith only [h2856, hlam, p3090_0]
                                                  · have p3090_0 := h3090c.1
                                                    have p3090_1 := h3090c.2.1
                                                    have p3090_2 := h3090c.2.2.1
                                                    have p3090_3 := h3090c.2.2.2
                                                    linarith only [h2862, hlam, p3090_0]
                                                  · have p3090_0 := h3090c.1
                                                    have p3090_1 := h3090c.2.1
                                                    have p3090_2 := h3090c.2.2.1
                                                    have p3090_3 := h3090c.2.2.2
                                                    rcases p3090_3 (m.d 0 3) (by simp) with h3125 | h3125
                                                    · rcases p3090_3 (m.d 1 3) (by simp) with h3126 | h3126
                                                      · rcases p3090_3 (m.d 2 3) (by simp) with h3127 | h3127
                                                        · linarith only [h3127, hlam, p3090_0]
                                                        · rcases p3090_3 (m.d 3 4) (by simp) with h3129 | h3129
                                                          · linarith only [h2986, h3129, hlam]
                                                          · linarith only [h2864, h3129, hlam]
                                                      · linarith only [h2858, h3126, hlam]
                                                    · linarith only [h2852, h3125, hlam]
                                                  · have p3090_0 := h3090c.1
                                                    have p3090_1 := h3090c.2.1
                                                    have p3090_2 := h3090c.2.2.1
                                                    have p3090_3 := h3090c.2.2.2
                                                    linarith only [h2864, hc23, hc35, hlam, hphi, p3090_1]
                                                  · have p3090_0 := h3090c.1
                                                    have p3090_1 := h3090c.2.1
                                                    have p3090_2 := h3090c.2.2.1
                                                    have p3090_3 := h3090c.2.2.2
                                                    linarith only [hlam, p3090_0]
                                                · linarith only [h2984, h3089, hlam]
                                          · linarith only [h2859, h3084, hlam]
                                        · linarith only [h2853, h3083, hlam]
                                      · have p3039_0 := h3039c.1
                                        have p3039_1 := h3039c.2.1
                                        have p3039_2 := h3039c.2.2.1
                                        have p3039_3 := h3039c.2.2.2
                                        linarith only [hlam, p3039_0]
                                    · linarith only [h2850, h3038, hlam]
                                  · linarith only [h2576, h3037, hlam]
                                · linarith only [h2249, h3036, hlam]
                              · linarith only [h0, h3035, hlam]
                          · have p2988_0 := h2988c.1
                            have p2988_1 := h2988c.2.1
                            have p2988_2 := h2988c.2.2.1
                            have p2988_3 := h2988c.2.2.2
                            linarith only [h2854, hlam, p2988_1]
                          · have p2988_0 := h2988c.1
                            have p2988_1 := h2988c.2.1
                            have p2988_2 := h2988c.2.2.1
                            have p2988_3 := h2988c.2.2.2
                            linarith only [h2856, hlam, p2988_0]
                          · have p2988_0 := h2988c.1
                            have p2988_1 := h2988c.2.1
                            have p2988_2 := h2988c.2.2.1
                            have p2988_3 := h2988c.2.2.2
                            linarith only [h2857, hlam, p2988_1]
                          · have p2988_0 := h2988c.1
                            have p2988_1 := h2988c.2.1
                            have p2988_2 := h2988c.2.2.1
                            have p2988_3 := h2988c.2.2.2
                            linarith only [hlam, p2988_0]
                · linarith only [h2249, h2576, h2855, h2857, h2858, h2863, hc01, hc12, hlam, hphi]
              · linarith only [h2249, h2856, h2862, hlam]
            · linarith only [h2249, h2856, h2861, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
          · linarith only [h0, h2852, h2856, h2860, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
        · linarith only [h0, h2852, h2855, h2857, h2859, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
      · linarith only [h0, h2852, h2855, h2857, h2858, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3154 | h3154
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3155 | h3155
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3156 | h3156
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3157 | h3157
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3158 | h3158
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3159 | h3159
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3160 | h3160
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3161 | h3161
                    · linarith only [h2852, h3161, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3163 | h3163
                      · linarith only [h2857, h3160, h3161, h3163, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3165 | h3165
                        · linarith only [h2249, h2855, h2857, h3154, h3165, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                        · rcases h0bigk with h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [hlam, p3167_0]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [h0, hlam, p3167_1]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [h2249, hlam, p3167_0]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [h2576, hlam, p3167_1]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [h2850, hlam, p3167_1]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            rcases p3167_3 (m.d 0 1) (by simp) with h3173 | h3173
                            · linarith only [h0, h3173, hlam]
                            · rcases p3167_3 (m.d 0 2) (by simp) with h3175 | h3175
                              · rcases p3167_3 (m.d 0 3) (by simp) with h3176 | h3176
                                · linarith only [h2852, h3176, hlam]
                                · linarith only [h2249, h3176, hlam]
                              · linarith only [h0, h3175, hlam]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [hlam, p3167_0]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [h0, h2856, h3160, h3161, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3167_1]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            rcases p3167_3 (m.d 0 1) (by simp) with h3182 | h3182
                            · linarith only [h0, h3182, hlam]
                            · rcases p3167_3 (m.d 0 2) (by simp) with h3184 | h3184
                              · rcases p3167_3 (m.d 0 3) (by simp) with h3185 | h3185
                                · linarith only [h2852, h3185, hlam]
                                · linarith only [h2855, h3185, hlam]
                              · linarith only [h2853, h3184, hlam]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p3167_1, u5ehi0]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            rcases p3167_3 (m.d 0 1) (by simp) with h3190 | h3190
                            · linarith only [h2249, h3190, hlam]
                            · rcases p3167_3 (m.d 0 2) (by simp) with h3192 | h3192
                              · rcases p3167_3 (m.d 0 3) (by simp) with h3193 | h3193
                                · rcases p3167_3 (m.d 0 4) (by simp) with h3194 | h3194
                                  · linarith only [h2855, h3194, hlam]
                                  · linarith only [h2576, h3194, hlam]
                                · linarith only [h2249, h3193, hlam]
                              · linarith only [h0, h3192, hlam]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [h2852, hlam, p3167_1]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [hlam, p3167_0]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            rcases p3167_3 (m.d 0 1) (by simp) with h3201 | h3201
                            · linarith only [h2249, h3201, hlam]
                            · rcases p3167_3 (m.d 0 2) (by simp) with h3203 | h3203
                              · rcases p3167_3 (m.d 0 3) (by simp) with h3204 | h3204
                                · rcases p3167_3 (m.d 0 4) (by simp) with h3205 | h3205
                                  · linarith only [h2855, h3205, hlam]
                                  · rcases p3167_3 (m.d 0 5) (by simp) with h3207 | h3207
                                    · linarith only [h2856, h3207, hlam]
                                    · linarith only [h2857, h3207, hlam]
                                · linarith only [h2855, h3204, hlam]
                              · linarith only [h2853, h3203, hlam]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [h2856, h3160, h3161, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p3167_1]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [h2857, h3154, h3157, h3159, hc01, hc12, hlam, hphi, p3167_1]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [h2853, hlam, p3167_0]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [h2855, hlam, p3167_0]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [hlam, p3167_0]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [h2857, hlam, p3167_0]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [h2857, h3154, h3157, h3159, hc01, hc12, hlam, hphi, p3167_1]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [h2854, hlam, p3167_1]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [h2856, hlam, p3167_0]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [h2576, h2857, h3154, h3157, h3159, hc01, hc12, hlam, hphi, p3167_1]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [hlam, p3167_0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3223 | h3223
                    · linarith only [h2855, h3160, h3223, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3225 | h3225
                      · linarith only [h2855, h2857, h3160, h3225, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3227 | h3227
                        · linarith only [h2855, h2857, h3227, hlam]
                        · rcases h0bigk with h3229c | h3229c | h3229c | h3229c | h3229c | h3229c | h3229c | h3229c | h3229c | h3229c | h3229c | h3229c | h3229c | h3229c | h3229c | h3229c | h3229c | h3229c | h3229c | h3229c | h3229c | h3229c | h3229c | h3229c | h3229c
                          · have p3229_0 := h3229c.1
                            have p3229_1 := h3229c.2.1
                            have p3229_2 := h3229c.2.2.1
                            have p3229_3 := h3229c.2.2.2
                            linarith only [hlam, p3229_0]
                          · have p3229_0 := h3229c.1
                            have p3229_1 := h3229c.2.1
                            have p3229_2 := h3229c.2.2.1
                            have p3229_3 := h3229c.2.2.2
                            linarith only [h0, hlam, p3229_1]
                          · have p3229_0 := h3229c.1
                            have p3229_1 := h3229c.2.1
                            have p3229_2 := h3229c.2.2.1
                            have p3229_3 := h3229c.2.2.2
                            linarith only [h2249, hlam, p3229_0]
                          · have p3229_0 := h3229c.1
                            have p3229_1 := h3229c.2.1
                            have p3229_2 := h3229c.2.2.1
                            have p3229_3 := h3229c.2.2.2
                            linarith only [h2576, hlam, p3229_1]
                          · have p3229_0 := h3229c.1
                            have p3229_1 := h3229c.2.1
                            have p3229_2 := h3229c.2.2.1
                            have p3229_3 := h3229c.2.2.2
                            linarith only [h2850, hlam, p3229_1]
                          · have p3229_0 := h3229c.1
                            have p3229_1 := h3229c.2.1
                            have p3229_2 := h3229c.2.2.1
                            have p3229_3 := h3229c.2.2.2
                            rcases p3229_3 (m.d 0 1) (by simp) with h3235 | h3235
                            · linarith only [h0, h3235, hlam]
                            · rcases p3229_3 (m.d 0 2) (by simp) with h3237 | h3237
                              · rcases p3229_3 (m.d 0 3) (by simp) with h3238 | h3238
                                · linarith only [h2852, h3238, hlam]
                                · linarith only [h2249, h3238, hlam]
                              · linarith only [h0, h3237, hlam]
                          · have p3229_0 := h3229c.1
                            have p3229_1 := h3229c.2.1
                            have p3229_2 := h3229c.2.2.1
                            have p3229_3 := h3229c.2.2.2
                            linarith only [hlam, p3229_0]
                          · have p3229_0 := h3229c.1
                            have p3229_1 := h3229c.2.1
                            have p3229_2 := h3229c.2.2.1
                            have p3229_3 := h3229c.2.2.2
                            linarith only [h0, h2855, h3160, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3229_1]
                          · have p3229_0 := h3229c.1
                            have p3229_1 := h3229c.2.1
                            have p3229_2 := h3229c.2.2.1
                            have p3229_3 := h3229c.2.2.2
                            rcases p3229_3 (m.d 0 1) (by simp) with h3244 | h3244
                            · linarith only [h0, h3244, hlam]
                            · rcases p3229_3 (m.d 0 2) (by simp) with h3246 | h3246
                              · rcases p3229_3 (m.d 0 3) (by simp) with h3247 | h3247
                                · linarith only [h2852, h3247, hlam]
                                · linarith only [h2855, h3247, hlam]
                              · linarith only [h2853, h3246, hlam]
                          · have p3229_0 := h3229c.1
                            have p3229_1 := h3229c.2.1
                            have p3229_2 := h3229c.2.2.1
                            have p3229_3 := h3229c.2.2.2
                            linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p3229_1, u5ehi0]
                          · have p3229_0 := h3229c.1
                            have p3229_1 := h3229c.2.1
                            have p3229_2 := h3229c.2.2.1
                            have p3229_3 := h3229c.2.2.2
                            rcases p3229_3 (m.d 0 1) (by simp) with h3252 | h3252
                            · linarith only [h2249, h3252, hlam]
                            · rcases p3229_3 (m.d 0 2) (by simp) with h3254 | h3254
                              · rcases p3229_3 (m.d 0 3) (by simp) with h3255 | h3255
                                · rcases p3229_3 (m.d 0 4) (by simp) with h3256 | h3256
                                  · linarith only [h2855, h3256, hlam]
                                  · linarith only [h2576, h3256, hlam]
                                · linarith only [h2249, h3255, hlam]
                              · linarith only [h0, h3254, hlam]
                          · have p3229_0 := h3229c.1
                            have p3229_1 := h3229c.2.1
                            have p3229_2 := h3229c.2.2.1
                            have p3229_3 := h3229c.2.2.2
                            linarith only [h2852, hlam, p3229_1]
                          · have p3229_0 := h3229c.1
                            have p3229_1 := h3229c.2.1
                            have p3229_2 := h3229c.2.2.1
                            have p3229_3 := h3229c.2.2.2
                            linarith only [hlam, p3229_0]
                          · have p3229_0 := h3229c.1
                            have p3229_1 := h3229c.2.1
                            have p3229_2 := h3229c.2.2.1
                            have p3229_3 := h3229c.2.2.2
                            rcases p3229_3 (m.d 0 1) (by simp) with h3263 | h3263
                            · linarith only [h2249, h3263, hlam]
                            · rcases p3229_3 (m.d 0 2) (by simp) with h3265 | h3265
                              · rcases p3229_3 (m.d 0 3) (by simp) with h3266 | h3266
                                · rcases p3229_3 (m.d 0 4) (by simp) with h3267 | h3267
                                  · linarith only [h2855, h3267, hlam]
                                  · rcases p3229_3 (m.d 0 5) (by simp) with h3269 | h3269
                                    · linarith only [h2856, h3269, hlam]
                                    · linarith only [h2857, h3269, hlam]
                                · linarith only [h2855, h3266, hlam]
                              · linarith only [h2853, h3265, hlam]
                          · have p3229_0 := h3229c.1
                            have p3229_1 := h3229c.2.1
                            have p3229_2 := h3229c.2.2.1
                            have p3229_3 := h3229c.2.2.2
                            linarith only [h2856, h3223, hc03, hlam, hphi, ht0b, ht5b, p3229_1, u5ehi2]
                          · have p3229_0 := h3229c.1
                            have p3229_1 := h3229c.2.1
                            have p3229_2 := h3229c.2.2.1
                            have p3229_3 := h3229c.2.2.2
                            linarith only [h2857, h3154, h3157, h3159, hc01, hc12, hlam, hphi, p3229_1]
                          · have p3229_0 := h3229c.1
                            have p3229_1 := h3229c.2.1
                            have p3229_2 := h3229c.2.2.1
                            have p3229_3 := h3229c.2.2.2
                            linarith only [h2853, hlam, p3229_0]
                          · have p3229_0 := h3229c.1
                            have p3229_1 := h3229c.2.1
                            have p3229_2 := h3229c.2.2.1
                            have p3229_3 := h3229c.2.2.2
                            linarith only [h2855, hlam, p3229_0]
                          · have p3229_0 := h3229c.1
                            have p3229_1 := h3229c.2.1
                            have p3229_2 := h3229c.2.2.1
                            have p3229_3 := h3229c.2.2.2
                            linarith only [hlam, p3229_0]
                          · have p3229_0 := h3229c.1
                            have p3229_1 := h3229c.2.1
                            have p3229_2 := h3229c.2.2.1
                            have p3229_3 := h3229c.2.2.2
                            linarith only [h2857, hlam, p3229_0]
                          · have p3229_0 := h3229c.1
                            have p3229_1 := h3229c.2.1
                            have p3229_2 := h3229c.2.2.1
                            have p3229_3 := h3229c.2.2.2
                            linarith only [h2857, h3154, h3157, h3159, hc01, hc12, hlam, hphi, p3229_1]
                          · have p3229_0 := h3229c.1
                            have p3229_1 := h3229c.2.1
                            have p3229_2 := h3229c.2.2.1
                            have p3229_3 := h3229c.2.2.2
                            linarith only [h2854, hlam, p3229_1]
                          · have p3229_0 := h3229c.1
                            have p3229_1 := h3229c.2.1
                            have p3229_2 := h3229c.2.2.1
                            have p3229_3 := h3229c.2.2.2
                            linarith only [h2856, hlam, p3229_0]
                          · have p3229_0 := h3229c.1
                            have p3229_1 := h3229c.2.1
                            have p3229_2 := h3229c.2.2.1
                            have p3229_3 := h3229c.2.2.2
                            linarith only [h2576, h2857, h3154, h3157, h3159, hc01, hc12, hlam, hphi, p3229_1]
                          · have p3229_0 := h3229c.1
                            have p3229_1 := h3229c.2.1
                            have p3229_2 := h3229c.2.2.1
                            have p3229_3 := h3229c.2.2.2
                            linarith only [hlam, p3229_0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3285 | h3285
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3286 | h3286
                    · linarith only [h0, h2852, h3286, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3288 | h3288
                      · linarith only [h2576, h3159, h3288, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3290 | h3290
                        · linarith only [h2249, h2576, h2856, h3154, h3159, h3285, h3286, h3290, hc01, hc12, hlam, hphi]
                        · rcases h0bigk with h3292c | h3292c | h3292c | h3292c | h3292c | h3292c | h3292c | h3292c | h3292c | h3292c | h3292c | h3292c | h3292c | h3292c | h3292c | h3292c | h3292c | h3292c | h3292c | h3292c | h3292c | h3292c | h3292c | h3292c | h3292c
                          · have p3292_0 := h3292c.1
                            have p3292_1 := h3292c.2.1
                            have p3292_2 := h3292c.2.2.1
                            have p3292_3 := h3292c.2.2.2
                            linarith only [hlam, p3292_0]
                          · have p3292_0 := h3292c.1
                            have p3292_1 := h3292c.2.1
                            have p3292_2 := h3292c.2.2.1
                            have p3292_3 := h3292c.2.2.2
                            linarith only [h0, hlam, p3292_1]
                          · have p3292_0 := h3292c.1
                            have p3292_1 := h3292c.2.1
                            have p3292_2 := h3292c.2.2.1
                            have p3292_3 := h3292c.2.2.2
                            linarith only [h2249, hlam, p3292_0]
                          · have p3292_0 := h3292c.1
                            have p3292_1 := h3292c.2.1
                            have p3292_2 := h3292c.2.2.1
                            have p3292_3 := h3292c.2.2.2
                            linarith only [h2576, hlam, p3292_1]
                          · have p3292_0 := h3292c.1
                            have p3292_1 := h3292c.2.1
                            have p3292_2 := h3292c.2.2.1
                            have p3292_3 := h3292c.2.2.2
                            linarith only [h2850, hlam, p3292_1]
                          · have p3292_0 := h3292c.1
                            have p3292_1 := h3292c.2.1
                            have p3292_2 := h3292c.2.2.1
                            have p3292_3 := h3292c.2.2.2
                            rcases p3292_3 (m.d 0 1) (by simp) with h3298 | h3298
                            · linarith only [h0, h3298, hlam]
                            · rcases p3292_3 (m.d 0 2) (by simp) with h3300 | h3300
                              · rcases p3292_3 (m.d 0 3) (by simp) with h3301 | h3301
                                · linarith only [h2852, h3301, hlam]
                                · linarith only [h2249, h3301, hlam]
                              · linarith only [h0, h3300, hlam]
                          · have p3292_0 := h3292c.1
                            have p3292_1 := h3292c.2.1
                            have p3292_2 := h3292c.2.2.1
                            have p3292_3 := h3292c.2.2.2
                            linarith only [hlam, p3292_0]
                          · have p3292_0 := h3292c.1
                            have p3292_1 := h3292c.2.1
                            have p3292_2 := h3292c.2.2.1
                            have p3292_3 := h3292c.2.2.2
                            linarith only [h0, h2856, h3286, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3292_1]
                          · have p3292_0 := h3292c.1
                            have p3292_1 := h3292c.2.1
                            have p3292_2 := h3292c.2.2.1
                            have p3292_3 := h3292c.2.2.2
                            rcases p3292_3 (m.d 0 1) (by simp) with h3307 | h3307
                            · linarith only [h0, h3307, hlam]
                            · rcases p3292_3 (m.d 0 2) (by simp) with h3309 | h3309
                              · rcases p3292_3 (m.d 0 3) (by simp) with h3310 | h3310
                                · linarith only [h2852, h3310, hlam]
                                · linarith only [h2855, h3310, hlam]
                              · linarith only [h2853, h3309, hlam]
                          · have p3292_0 := h3292c.1
                            have p3292_1 := h3292c.2.1
                            have p3292_2 := h3292c.2.2.1
                            have p3292_3 := h3292c.2.2.2
                            linarith only [h0, h2856, h3285, h3286, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3292_1]
                          · have p3292_0 := h3292c.1
                            have p3292_1 := h3292c.2.1
                            have p3292_2 := h3292c.2.2.1
                            have p3292_3 := h3292c.2.2.2
                            rcases p3292_3 (m.d 0 1) (by simp) with h3315 | h3315
                            · linarith only [h2249, h3315, hlam]
                            · rcases p3292_3 (m.d 0 2) (by simp) with h3317 | h3317
                              · rcases p3292_3 (m.d 0 3) (by simp) with h3318 | h3318
                                · rcases p3292_3 (m.d 0 4) (by simp) with h3319 | h3319
                                  · linarith only [h2855, h3319, hlam]
                                  · linarith only [h2576, h3319, hlam]
                                · linarith only [h2249, h3318, hlam]
                              · linarith only [h0, h3317, hlam]
                          · have p3292_0 := h3292c.1
                            have p3292_1 := h3292c.2.1
                            have p3292_2 := h3292c.2.2.1
                            have p3292_3 := h3292c.2.2.2
                            linarith only [h2852, hlam, p3292_1]
                          · have p3292_0 := h3292c.1
                            have p3292_1 := h3292c.2.1
                            have p3292_2 := h3292c.2.2.1
                            have p3292_3 := h3292c.2.2.2
                            linarith only [hlam, p3292_0]
                          · have p3292_0 := h3292c.1
                            have p3292_1 := h3292c.2.1
                            have p3292_2 := h3292c.2.2.1
                            have p3292_3 := h3292c.2.2.2
                            rcases p3292_3 (m.d 0 1) (by simp) with h3326 | h3326
                            · linarith only [h2249, h3326, hlam]
                            · rcases p3292_3 (m.d 0 2) (by simp) with h3328 | h3328
                              · rcases p3292_3 (m.d 0 3) (by simp) with h3329 | h3329
                                · rcases p3292_3 (m.d 0 4) (by simp) with h3330 | h3330
                                  · linarith only [h2855, h3330, hlam]
                                  · rcases p3292_3 (m.d 0 5) (by simp) with h3332 | h3332
                                    · linarith only [h2856, h3332, hlam]
                                    · linarith only [h2857, h3332, hlam]
                                · linarith only [h2855, h3329, hlam]
                              · linarith only [h2853, h3328, hlam]
                          · have p3292_0 := h3292c.1
                            have p3292_1 := h3292c.2.1
                            have p3292_2 := h3292c.2.2.1
                            have p3292_3 := h3292c.2.2.2
                            linarith only [h2249, h2856, h3154, h3285, h3286, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3292_1]
                          · have p3292_0 := h3292c.1
                            have p3292_1 := h3292c.2.1
                            have p3292_2 := h3292c.2.2.1
                            have p3292_3 := h3292c.2.2.2
                            linarith only [h2576, h3159, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3292_1]
                          · have p3292_0 := h3292c.1
                            have p3292_1 := h3292c.2.1
                            have p3292_2 := h3292c.2.2.1
                            have p3292_3 := h3292c.2.2.2
                            linarith only [h2853, hlam, p3292_0]
                          · have p3292_0 := h3292c.1
                            have p3292_1 := h3292c.2.1
                            have p3292_2 := h3292c.2.2.1
                            have p3292_3 := h3292c.2.2.2
                            linarith only [h2855, hlam, p3292_0]
                          · have p3292_0 := h3292c.1
                            have p3292_1 := h3292c.2.1
                            have p3292_2 := h3292c.2.2.1
                            have p3292_3 := h3292c.2.2.2
                            linarith only [hlam, p3292_0]
                          · have p3292_0 := h3292c.1
                            have p3292_1 := h3292c.2.1
                            have p3292_2 := h3292c.2.2.1
                            have p3292_3 := h3292c.2.2.2
                            linarith only [h2857, hlam, p3292_0]
                          · have p3292_0 := h3292c.1
                            have p3292_1 := h3292c.2.1
                            have p3292_2 := h3292c.2.2.1
                            have p3292_3 := h3292c.2.2.2
                            rcases p3292_3 (m.d 0 1) (by simp) with h3343 | h3343
                            · linarith only [h2850, h3343, hlam]
                            · rcases p3292_3 (m.d 0 2) (by simp) with h3345 | h3345
                              · rcases p3292_3 (m.d 0 3) (by simp) with h3346 | h3346
                                · rcases p3292_3 (m.d 0 4) (by simp) with h3347 | h3347
                                  · linarith only [h2857, h3347, hlam]
                                  · linarith only [h2576, h3347, hlam]
                                · linarith only [h2249, h3346, hlam]
                              · linarith only [h0, h3345, hlam]
                          · have p3292_0 := h3292c.1
                            have p3292_1 := h3292c.2.1
                            have p3292_2 := h3292c.2.2.1
                            have p3292_3 := h3292c.2.2.2
                            linarith only [h2854, hlam, p3292_1]
                          · have p3292_0 := h3292c.1
                            have p3292_1 := h3292c.2.1
                            have p3292_2 := h3292c.2.2.1
                            have p3292_3 := h3292c.2.2.2
                            linarith only [h2856, hlam, p3292_0]
                          · have p3292_0 := h3292c.1
                            have p3292_1 := h3292c.2.1
                            have p3292_2 := h3292c.2.2.1
                            have p3292_3 := h3292c.2.2.2
                            rcases p3292_3 (m.d 0 1) (by simp) with h3354 | h3354
                            · linarith only [h2850, h3354, hlam]
                            · rcases p3292_3 (m.d 0 2) (by simp) with h3356 | h3356
                              · rcases p3292_3 (m.d 0 3) (by simp) with h3357 | h3357
                                · rcases p3292_3 (m.d 0 4) (by simp) with h3358 | h3358
                                  · linarith only [h2857, h3358, hlam]
                                  · rcases p3292_3 (m.d 0 5) (by simp) with h3360 | h3360
                                    · rcases h2bigk with h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c
                                      · have p3361_0 := h3361c.1
                                        have p3361_1 := h3361c.2.1
                                        have p3361_2 := h3361c.2.2.1
                                        have p3361_3 := h3361c.2.2.2
                                        linarith only [hlam, p3361_0]
                                      · have p3361_0 := h3361c.1
                                        have p3361_1 := h3361c.2.1
                                        have p3361_2 := h3361c.2.2.1
                                        have p3361_3 := h3361c.2.2.2
                                        linarith only [h0, hlam, p3361_1]
                                      · have p3361_0 := h3361c.1
                                        have p3361_1 := h3361c.2.1
                                        have p3361_2 := h3361c.2.2.1
                                        have p3361_3 := h3361c.2.2.2
                                        rcases p3361_3 (m.d 0 2) (by simp) with h3364 | h3364
                                        · rcases p3361_3 (m.d 1 2) (by simp) with h3365 | h3365
                                          · rcases p3361_3 (m.d 2 3) (by simp) with h3366 | h3366
                                            · linarith only [h3366, hlam, p3361_0]
                                            · rcases p3361_3 (m.d 2 4) (by simp) with h3368 | h3368
                                              · linarith only [h2853, h3368, hlam]
                                              · rcases p3361_3 (m.d 2 5) (by simp) with h3370 | h3370
                                                · linarith only [h2854, h3370, hlam]
                                                · linarith only [h3286, h3370, hlam]
                                          · linarith only [h3154, h3365, hlam]
                                        · linarith only [h3364, hlam, p3361_0]
                                      · have p3361_0 := h3361c.1
                                        have p3361_1 := h3361c.2.1
                                        have p3361_2 := h3361c.2.2.1
                                        have p3361_3 := h3361c.2.2.2
                                        rcases p3361_3 (m.d 0 2) (by simp) with h3375 | h3375
                                        · rcases p3361_3 (m.d 1 2) (by simp) with h3376 | h3376
                                          · rcases p3361_3 (m.d 2 3) (by simp) with h3377 | h3377
                                            · linarith only [h2852, h3377, hlam]
                                            · linarith only [h3285, h3377, hlam]
                                          · linarith only [h3155, h3376, hlam]
                                        · linarith only [h3375, hlam, p3361_0]
                                      · have p3361_0 := h3361c.1
                                        have p3361_1 := h3361c.2.1
                                        have p3361_2 := h3361c.2.2.1
                                        have p3361_3 := h3361c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p3361_1, u5ehi2]
                                      · have p3361_0 := h3361c.1
                                        have p3361_1 := h3361c.2.1
                                        have p3361_2 := h3361c.2.2.1
                                        have p3361_3 := h3361c.2.2.2
                                        linarith only [h2852, h3285, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3361_1]
                                      · have p3361_0 := h3361c.1
                                        have p3361_1 := h3361c.2.1
                                        have p3361_2 := h3361c.2.2.1
                                        have p3361_3 := h3361c.2.2.2
                                        linarith only [hlam, p3361_0]
                                      · have p3361_0 := h3361c.1
                                        have p3361_1 := h3361c.2.1
                                        have p3361_2 := h3361c.2.2.1
                                        have p3361_3 := h3361c.2.2.2
                                        rcases p3361_3 (m.d 0 2) (by simp) with h3385 | h3385
                                        · linarith only [h0, h3385, hlam]
                                        · linarith only [h2852, h3385, hlam]
                                      · have p3361_0 := h3361c.1
                                        have p3361_1 := h3361c.2.1
                                        have p3361_2 := h3361c.2.2.1
                                        have p3361_3 := h3361c.2.2.2
                                        rcases p3361_3 (m.d 0 2) (by simp) with h3388 | h3388
                                        · linarith only [h0, h3388, hlam]
                                        · linarith only [h2853, h3388, hlam]
                                      · have p3361_0 := h3361c.1
                                        have p3361_1 := h3361c.2.1
                                        have p3361_2 := h3361c.2.2.1
                                        have p3361_3 := h3361c.2.2.2
                                        linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p3361_1, u5ehi2]
                                      · have p3361_0 := h3361c.1
                                        have p3361_1 := h3361c.2.1
                                        have p3361_2 := h3361c.2.2.1
                                        have p3361_3 := h3361c.2.2.2
                                        linarith only [h2852, hlam, p3361_0]
                                      · have p3361_0 := h3361c.1
                                        have p3361_1 := h3361c.2.1
                                        have p3361_2 := h3361c.2.2.1
                                        have p3361_3 := h3361c.2.2.2
                                        linarith only [h3154, hlam, p3361_0]
                                      · have p3361_0 := h3361c.1
                                        have p3361_1 := h3361c.2.1
                                        have p3361_2 := h3361c.2.2.1
                                        have p3361_3 := h3361c.2.2.2
                                        linarith only [hlam, p3361_0]
                                      · have p3361_0 := h3361c.1
                                        have p3361_1 := h3361c.2.1
                                        have p3361_2 := h3361c.2.2.1
                                        have p3361_3 := h3361c.2.2.2
                                        linarith only [h2852, h2856, h3286, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p3361_1]
                                      · have p3361_0 := h3361c.1
                                        have p3361_1 := h3361c.2.1
                                        have p3361_2 := h3361c.2.2.1
                                        have p3361_3 := h3361c.2.2.2
                                        linarith only [h3286, hlam, p3361_0]
                                      · have p3361_0 := h3361c.1
                                        have p3361_1 := h3361c.2.1
                                        have p3361_2 := h3361c.2.2.1
                                        have p3361_3 := h3361c.2.2.2
                                        linarith only [h2853, hlam, p3361_0]
                                      · have p3361_0 := h3361c.1
                                        have p3361_1 := h3361c.2.1
                                        have p3361_2 := h3361c.2.2.1
                                        have p3361_3 := h3361c.2.2.2
                                        linarith only [h3155, hlam, p3361_0]
                                      · have p3361_0 := h3361c.1
                                        have p3361_1 := h3361c.2.1
                                        have p3361_2 := h3361c.2.2.1
                                        have p3361_3 := h3361c.2.2.2
                                        linarith only [h3285, hlam, p3361_1]
                                      · have p3361_0 := h3361c.1
                                        have p3361_1 := h3361c.2.1
                                        have p3361_2 := h3361c.2.2.1
                                        have p3361_3 := h3361c.2.2.2
                                        linarith only [hlam, p3361_0]
                                      · have p3361_0 := h3361c.1
                                        have p3361_1 := h3361c.2.1
                                        have p3361_2 := h3361c.2.2.1
                                        have p3361_3 := h3361c.2.2.2
                                        linarith only [h3288, hlam, p3361_1]
                                      · have p3361_0 := h3361c.1
                                        have p3361_1 := h3361c.2.1
                                        have p3361_2 := h3361c.2.2.1
                                        have p3361_3 := h3361c.2.2.2
                                        linarith only [h2854, hlam, p3361_0]
                                      · have p3361_0 := h3361c.1
                                        have p3361_1 := h3361c.2.1
                                        have p3361_2 := h3361c.2.2.1
                                        have p3361_3 := h3361c.2.2.2
                                        linarith only [h3156, hlam, p3361_0]
                                      · have p3361_0 := h3361c.1
                                        have p3361_1 := h3361c.2.1
                                        have p3361_2 := h3361c.2.2.1
                                        have p3361_3 := h3361c.2.2.2
                                        linarith only [h0, h2576, h2850, h2854, h3159, h3285, hc01, hc12, hc34, hc45, hlam, hphi, p3292_1, p3361_1]
                                      · have p3361_0 := h3361c.1
                                        have p3361_1 := h3361c.2.1
                                        have p3361_2 := h3361c.2.2.1
                                        have p3361_3 := h3361c.2.2.2
                                        rcases p3361_3 (m.d 0 2) (by simp) with h3405 | h3405
                                        · rcases p3361_3 (m.d 1 2) (by simp) with h3406 | h3406
                                          · rcases p3361_3 (m.d 2 3) (by simp) with h3407 | h3407
                                            · linarith only [h3286, h3407, hlam]
                                            · linarith only [h3285, h3407, hlam]
                                          · linarith only [h3155, h3406, hlam]
                                        · linarith only [h2853, h3405, hlam]
                                      · have p3361_0 := h3361c.1
                                        have p3361_1 := h3361c.2.1
                                        have p3361_2 := h3361c.2.2.1
                                        have p3361_3 := h3361c.2.2.2
                                        linarith only [hlam, p3361_0]
                                    · linarith only [h2857, h3360, hlam]
                                · linarith only [h2855, h3357, hlam]
                              · linarith only [h2853, h3356, hlam]
                          · have p3292_0 := h3292c.1
                            have p3292_1 := h3292c.2.1
                            have p3292_2 := h3292c.2.2.1
                            have p3292_3 := h3292c.2.2.2
                            linarith only [hlam, p3292_0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3417 | h3417
                    · linarith only [h2855, h3285, h3417, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3419 | h3419
                      · linarith only [h2576, h3159, h3419, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3421 | h3421
                        · linarith only [h2576, h2855, h3159, h3421, hlam]
                        · rcases h0bigk with h3423c | h3423c | h3423c | h3423c | h3423c | h3423c | h3423c | h3423c | h3423c | h3423c | h3423c | h3423c | h3423c | h3423c | h3423c | h3423c | h3423c | h3423c | h3423c | h3423c | h3423c | h3423c | h3423c | h3423c | h3423c
                          · have p3423_0 := h3423c.1
                            have p3423_1 := h3423c.2.1
                            have p3423_2 := h3423c.2.2.1
                            have p3423_3 := h3423c.2.2.2
                            linarith only [hlam, p3423_0]
                          · have p3423_0 := h3423c.1
                            have p3423_1 := h3423c.2.1
                            have p3423_2 := h3423c.2.2.1
                            have p3423_3 := h3423c.2.2.2
                            linarith only [h0, hlam, p3423_1]
                          · have p3423_0 := h3423c.1
                            have p3423_1 := h3423c.2.1
                            have p3423_2 := h3423c.2.2.1
                            have p3423_3 := h3423c.2.2.2
                            linarith only [h2249, hlam, p3423_0]
                          · have p3423_0 := h3423c.1
                            have p3423_1 := h3423c.2.1
                            have p3423_2 := h3423c.2.2.1
                            have p3423_3 := h3423c.2.2.2
                            linarith only [h2576, hlam, p3423_1]
                          · have p3423_0 := h3423c.1
                            have p3423_1 := h3423c.2.1
                            have p3423_2 := h3423c.2.2.1
                            have p3423_3 := h3423c.2.2.2
                            linarith only [h2850, hlam, p3423_1]
                          · have p3423_0 := h3423c.1
                            have p3423_1 := h3423c.2.1
                            have p3423_2 := h3423c.2.2.1
                            have p3423_3 := h3423c.2.2.2
                            rcases p3423_3 (m.d 0 1) (by simp) with h3429 | h3429
                            · linarith only [h0, h3429, hlam]
                            · rcases p3423_3 (m.d 0 2) (by simp) with h3431 | h3431
                              · rcases p3423_3 (m.d 0 3) (by simp) with h3432 | h3432
                                · linarith only [h2852, h3432, hlam]
                                · linarith only [h2249, h3432, hlam]
                              · linarith only [h0, h3431, hlam]
                          · have p3423_0 := h3423c.1
                            have p3423_1 := h3423c.2.1
                            have p3423_2 := h3423c.2.2.1
                            have p3423_3 := h3423c.2.2.2
                            linarith only [hlam, p3423_0]
                          · have p3423_0 := h3423c.1
                            have p3423_1 := h3423c.2.1
                            have p3423_2 := h3423c.2.2.1
                            have p3423_3 := h3423c.2.2.2
                            linarith only [h0, h2856, h3417, hc12, hlam, hphi, ht01, ht0b, ht5b, p3423_1, u5ehi2]
                          · have p3423_0 := h3423c.1
                            have p3423_1 := h3423c.2.1
                            have p3423_2 := h3423c.2.2.1
                            have p3423_3 := h3423c.2.2.2
                            rcases p3423_3 (m.d 0 1) (by simp) with h3438 | h3438
                            · linarith only [h0, h3438, hlam]
                            · rcases p3423_3 (m.d 0 2) (by simp) with h3440 | h3440
                              · rcases p3423_3 (m.d 0 3) (by simp) with h3441 | h3441
                                · linarith only [h2852, h3441, hlam]
                                · linarith only [h2855, h3441, hlam]
                              · linarith only [h2853, h3440, hlam]
                          · have p3423_0 := h3423c.1
                            have p3423_1 := h3423c.2.1
                            have p3423_2 := h3423c.2.2.1
                            have p3423_3 := h3423c.2.2.2
                            linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p3423_1, u5ehi0]
                          · have p3423_0 := h3423c.1
                            have p3423_1 := h3423c.2.1
                            have p3423_2 := h3423c.2.2.1
                            have p3423_3 := h3423c.2.2.2
                            rcases p3423_3 (m.d 0 1) (by simp) with h3446 | h3446
                            · linarith only [h2249, h3446, hlam]
                            · rcases p3423_3 (m.d 0 2) (by simp) with h3448 | h3448
                              · rcases p3423_3 (m.d 0 3) (by simp) with h3449 | h3449
                                · rcases p3423_3 (m.d 0 4) (by simp) with h3450 | h3450
                                  · linarith only [h2855, h3450, hlam]
                                  · linarith only [h2576, h3450, hlam]
                                · linarith only [h2249, h3449, hlam]
                              · linarith only [h0, h3448, hlam]
                          · have p3423_0 := h3423c.1
                            have p3423_1 := h3423c.2.1
                            have p3423_2 := h3423c.2.2.1
                            have p3423_3 := h3423c.2.2.2
                            linarith only [h2852, hlam, p3423_1]
                          · have p3423_0 := h3423c.1
                            have p3423_1 := h3423c.2.1
                            have p3423_2 := h3423c.2.2.1
                            have p3423_3 := h3423c.2.2.2
                            linarith only [hlam, p3423_0]
                          · have p3423_0 := h3423c.1
                            have p3423_1 := h3423c.2.1
                            have p3423_2 := h3423c.2.2.1
                            have p3423_3 := h3423c.2.2.2
                            rcases p3423_3 (m.d 0 1) (by simp) with h3457 | h3457
                            · linarith only [h2249, h3457, hlam]
                            · rcases p3423_3 (m.d 0 2) (by simp) with h3459 | h3459
                              · rcases p3423_3 (m.d 0 3) (by simp) with h3460 | h3460
                                · rcases p3423_3 (m.d 0 4) (by simp) with h3461 | h3461
                                  · linarith only [h2855, h3461, hlam]
                                  · rcases p3423_3 (m.d 0 5) (by simp) with h3463 | h3463
                                    · linarith only [h2856, h3463, hlam]
                                    · linarith only [h2857, h3463, hlam]
                                · linarith only [h2855, h3460, hlam]
                              · linarith only [h2853, h3459, hlam]
                          · have p3423_0 := h3423c.1
                            have p3423_1 := h3423c.2.1
                            have p3423_2 := h3423c.2.2.1
                            have p3423_3 := h3423c.2.2.2
                            linarith only [h2249, h2856, h3154, h3417, hc12, hlam, hphi, ht01, ht0b, ht5b, p3423_1, u5ehi2]
                          · have p3423_0 := h3423c.1
                            have p3423_1 := h3423c.2.1
                            have p3423_2 := h3423c.2.2.1
                            have p3423_3 := h3423c.2.2.2
                            linarith only [h2576, h3159, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3423_1]
                          · have p3423_0 := h3423c.1
                            have p3423_1 := h3423c.2.1
                            have p3423_2 := h3423c.2.2.1
                            have p3423_3 := h3423c.2.2.2
                            linarith only [h2853, hlam, p3423_0]
                          · have p3423_0 := h3423c.1
                            have p3423_1 := h3423c.2.1
                            have p3423_2 := h3423c.2.2.1
                            have p3423_3 := h3423c.2.2.2
                            linarith only [h2855, hlam, p3423_0]
                          · have p3423_0 := h3423c.1
                            have p3423_1 := h3423c.2.1
                            have p3423_2 := h3423c.2.2.1
                            have p3423_3 := h3423c.2.2.2
                            linarith only [hlam, p3423_0]
                          · have p3423_0 := h3423c.1
                            have p3423_1 := h3423c.2.1
                            have p3423_2 := h3423c.2.2.1
                            have p3423_3 := h3423c.2.2.2
                            linarith only [h2857, hlam, p3423_0]
                          · have p3423_0 := h3423c.1
                            have p3423_1 := h3423c.2.1
                            have p3423_2 := h3423c.2.2.1
                            have p3423_3 := h3423c.2.2.2
                            rcases p3423_3 (m.d 0 1) (by simp) with h3474 | h3474
                            · linarith only [h2850, h3474, hlam]
                            · rcases p3423_3 (m.d 0 2) (by simp) with h3476 | h3476
                              · rcases p3423_3 (m.d 0 3) (by simp) with h3477 | h3477
                                · rcases p3423_3 (m.d 0 4) (by simp) with h3478 | h3478
                                  · linarith only [h2857, h3478, hlam]
                                  · linarith only [h2576, h3478, hlam]
                                · linarith only [h2249, h3477, hlam]
                              · linarith only [h0, h3476, hlam]
                          · have p3423_0 := h3423c.1
                            have p3423_1 := h3423c.2.1
                            have p3423_2 := h3423c.2.2.1
                            have p3423_3 := h3423c.2.2.2
                            linarith only [h2854, hlam, p3423_1]
                          · have p3423_0 := h3423c.1
                            have p3423_1 := h3423c.2.1
                            have p3423_2 := h3423c.2.2.1
                            have p3423_3 := h3423c.2.2.2
                            linarith only [h2856, hlam, p3423_0]
                          · have p3423_0 := h3423c.1
                            have p3423_1 := h3423c.2.1
                            have p3423_2 := h3423c.2.2.1
                            have p3423_3 := h3423c.2.2.2
                            linarith only [h2850, h2855, h3159, h3285, hc23, hc45, hlam, hphi, ht34, p3423_1]
                          · have p3423_0 := h3423c.1
                            have p3423_1 := h3423c.2.1
                            have p3423_2 := h3423c.2.2.1
                            have p3423_3 := h3423c.2.2.2
                            linarith only [hlam, p3423_0]
              · linarith only [h2249, h2856, h3158, hlam]
            · linarith only [h2249, h2855, h2856, h3157, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
          · linarith only [h0, h2852, h2856, h3156, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
        · linarith only [h0, h2853, h3155, hlam]
      · linarith only [h0, h2852, h2856, h3154, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h3492 | h3492
    · linarith only [h2855, h2856, h3492, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3494 | h3494
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3495 | h3495
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3496 | h3496
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3497 | h3497
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3498 | h3498
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3499 | h3499
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3500 | h3500
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3501 | h3501
                    · linarith only [h2852, h2856, h3501, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3503 | h3503
                      · linarith only [h2853, h2855, h2856, h3492, h3494, h3498, h3503, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3505 | h3505
                        · linarith only [h2852, h2856, h3492, h3494, h3498, h3500, h3505, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases h0bigk with h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c
                          · have p3507_0 := h3507c.1
                            have p3507_1 := h3507c.2.1
                            have p3507_2 := h3507c.2.2.1
                            have p3507_3 := h3507c.2.2.2
                            linarith only [hlam, p3507_0]
                          · have p3507_0 := h3507c.1
                            have p3507_1 := h3507c.2.1
                            have p3507_2 := h3507c.2.2.1
                            have p3507_3 := h3507c.2.2.2
                            linarith only [h0, hlam, p3507_1]
                          · have p3507_0 := h3507c.1
                            have p3507_1 := h3507c.2.1
                            have p3507_2 := h3507c.2.2.1
                            have p3507_3 := h3507c.2.2.2
                            linarith only [h2249, hlam, p3507_0]
                          · have p3507_0 := h3507c.1
                            have p3507_1 := h3507c.2.1
                            have p3507_2 := h3507c.2.2.1
                            have p3507_3 := h3507c.2.2.2
                            linarith only [h2576, hlam, p3507_1]
                          · have p3507_0 := h3507c.1
                            have p3507_1 := h3507c.2.1
                            have p3507_2 := h3507c.2.2.1
                            have p3507_3 := h3507c.2.2.2
                            linarith only [h2850, hlam, p3507_1]
                          · have p3507_0 := h3507c.1
                            have p3507_1 := h3507c.2.1
                            have p3507_2 := h3507c.2.2.1
                            have p3507_3 := h3507c.2.2.2
                            rcases p3507_3 (m.d 0 1) (by simp) with h3513 | h3513
                            · linarith only [h0, h3513, hlam]
                            · rcases p3507_3 (m.d 0 2) (by simp) with h3515 | h3515
                              · rcases p3507_3 (m.d 0 3) (by simp) with h3516 | h3516
                                · linarith only [h2852, h3516, hlam]
                                · linarith only [h2249, h3516, hlam]
                              · linarith only [h0, h3515, hlam]
                          · have p3507_0 := h3507c.1
                            have p3507_1 := h3507c.2.1
                            have p3507_2 := h3507c.2.2.1
                            have p3507_3 := h3507c.2.2.2
                            linarith only [hlam, p3507_0]
                          · have p3507_0 := h3507c.1
                            have p3507_1 := h3507c.2.1
                            have p3507_2 := h3507c.2.2.1
                            have p3507_3 := h3507c.2.2.2
                            rcases p3507_3 (m.d 0 1) (by simp) with h3521 | h3521
                            · linarith only [h0, h3521, hlam]
                            · rcases p3507_3 (m.d 0 2) (by simp) with h3523 | h3523
                              · rcases p3507_3 (m.d 0 3) (by simp) with h3524 | h3524
                                · linarith only [h2852, h3524, hlam]
                                · rcases p3507_3 (m.d 0 4) (by simp) with h3526 | h3526
                                  · linarith only [h2853, h3526, hlam]
                                  · rcases p3507_3 (m.d 0 5) (by simp) with h3528 | h3528
                                    · linarith only [h2854, h3528, hlam]
                                    · linarith only [h2856, h3528, hlam]
                              · linarith only [h2852, h3523, hlam]
                          · have p3507_0 := h3507c.1
                            have p3507_1 := h3507c.2.1
                            have p3507_2 := h3507c.2.2.1
                            have p3507_3 := h3507c.2.2.2
                            rcases p3507_3 (m.d 0 1) (by simp) with h3532 | h3532
                            · linarith only [h0, h3532, hlam]
                            · rcases p3507_3 (m.d 0 2) (by simp) with h3534 | h3534
                              · rcases p3507_3 (m.d 0 3) (by simp) with h3535 | h3535
                                · linarith only [h2852, h3535, hlam]
                                · linarith only [h2855, h3535, hlam]
                              · linarith only [h2853, h3534, hlam]
                          · have p3507_0 := h3507c.1
                            have p3507_1 := h3507c.2.1
                            have p3507_2 := h3507c.2.2.1
                            have p3507_3 := h3507c.2.2.2
                            linarith only [h2854, hc02, hlam, hphi, ht0b, ht5b, p3507_1, u5ehi2]
                          · have p3507_0 := h3507c.1
                            have p3507_1 := h3507c.2.1
                            have p3507_2 := h3507c.2.2.1
                            have p3507_3 := h3507c.2.2.2
                            linarith only [h2856, h3494, h3497, h3499, h3505, hc01, hc12, hlam, hphi, p3507_1]
                          · have p3507_0 := h3507c.1
                            have p3507_1 := h3507c.2.1
                            have p3507_2 := h3507c.2.2.1
                            have p3507_3 := h3507c.2.2.2
                            linarith only [h2852, hlam, p3507_1]
                          · have p3507_0 := h3507c.1
                            have p3507_1 := h3507c.2.1
                            have p3507_2 := h3507c.2.2.1
                            have p3507_3 := h3507c.2.2.2
                            linarith only [hlam, p3507_0]
                          · have p3507_0 := h3507c.1
                            have p3507_1 := h3507c.2.1
                            have p3507_2 := h3507c.2.2.1
                            have p3507_3 := h3507c.2.2.2
                            linarith only [h2576, h2856, h3494, h3497, h3499, h3505, hc01, hc12, hlam, hphi, p3507_1]
                          · have p3507_0 := h3507c.1
                            have p3507_1 := h3507c.2.1
                            have p3507_2 := h3507c.2.2.1
                            have p3507_3 := h3507c.2.2.2
                            linarith only [h2856, hlam, p3507_1]
                          · have p3507_0 := h3507c.1
                            have p3507_1 := h3507c.2.1
                            have p3507_2 := h3507c.2.2.1
                            have p3507_3 := h3507c.2.2.2
                            linarith only [h2855, h2856, h3494, h3497, h3499, h3505, hc01, hc12, hlam, hphi, p3507_1]
                          · have p3507_0 := h3507c.1
                            have p3507_1 := h3507c.2.1
                            have p3507_2 := h3507c.2.2.1
                            have p3507_3 := h3507c.2.2.2
                            linarith only [h2853, hlam, p3507_0]
                          · have p3507_0 := h3507c.1
                            have p3507_1 := h3507c.2.1
                            have p3507_2 := h3507c.2.2.1
                            have p3507_3 := h3507c.2.2.2
                            linarith only [h2855, hlam, p3507_0]
                          · have p3507_0 := h3507c.1
                            have p3507_1 := h3507c.2.1
                            have p3507_2 := h3507c.2.2.1
                            have p3507_3 := h3507c.2.2.2
                            linarith only [hlam, p3507_0]
                          · have p3507_0 := h3507c.1
                            have p3507_1 := h3507c.2.1
                            have p3507_2 := h3507c.2.2.1
                            have p3507_3 := h3507c.2.2.2
                            linarith only [h3492, hlam, p3507_0]
                          · have p3507_0 := h3507c.1
                            have p3507_1 := h3507c.2.1
                            have p3507_2 := h3507c.2.2.1
                            have p3507_3 := h3507c.2.2.2
                            linarith only [h2856, h3494, h3497, h3499, h3505, hc01, hc12, hlam, hphi, p3507_1]
                          · have p3507_0 := h3507c.1
                            have p3507_1 := h3507c.2.1
                            have p3507_2 := h3507c.2.2.1
                            have p3507_3 := h3507c.2.2.2
                            linarith only [h2854, hlam, p3507_1]
                          · have p3507_0 := h3507c.1
                            have p3507_1 := h3507c.2.1
                            have p3507_2 := h3507c.2.2.1
                            have p3507_3 := h3507c.2.2.2
                            linarith only [h2852, h2856, h3494, h3497, h3499, h3500, h3505, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3507_1]
                          · have p3507_0 := h3507c.1
                            have p3507_1 := h3507c.2.1
                            have p3507_2 := h3507c.2.2.1
                            have p3507_3 := h3507c.2.2.2
                            linarith only [h2576, h2856, h3494, h3497, h3499, h3505, hc01, hc12, hlam, hphi, p3507_1]
                          · have p3507_0 := h3507c.1
                            have p3507_1 := h3507c.2.1
                            have p3507_2 := h3507c.2.2.1
                            have p3507_3 := h3507c.2.2.2
                            linarith only [hlam, p3507_0]
                  · linarith only [h2855, h2856, h3500, hc23, hc35, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3556 | h3556
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3557 | h3557
                    · linarith only [h2852, h2856, h3557, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3559 | h3559
                      · linarith only [h2576, h3499, h3559, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3561 | h3561
                        · linarith only [h2576, h3499, h3561, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases h0bigk with h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [hlam, p3563_0]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [h0, hlam, p3563_1]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [h2249, hlam, p3563_0]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [h2576, hlam, p3563_1]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [h2850, hlam, p3563_1]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            rcases p3563_3 (m.d 0 1) (by simp) with h3569 | h3569
                            · linarith only [h0, h3569, hlam]
                            · rcases p3563_3 (m.d 0 2) (by simp) with h3571 | h3571
                              · rcases p3563_3 (m.d 0 3) (by simp) with h3572 | h3572
                                · linarith only [h2852, h3572, hlam]
                                · linarith only [h2249, h3572, hlam]
                              · linarith only [h0, h3571, hlam]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [hlam, p3563_0]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            rcases p3563_3 (m.d 0 1) (by simp) with h3577 | h3577
                            · linarith only [h0, h3577, hlam]
                            · rcases p3563_3 (m.d 0 2) (by simp) with h3579 | h3579
                              · rcases p3563_3 (m.d 0 3) (by simp) with h3580 | h3580
                                · linarith only [h2852, h3580, hlam]
                                · rcases p3563_3 (m.d 0 4) (by simp) with h3582 | h3582
                                  · linarith only [h2853, h3582, hlam]
                                  · rcases p3563_3 (m.d 0 5) (by simp) with h3584 | h3584
                                    · linarith only [h2854, h3584, hlam]
                                    · linarith only [h2856, h3584, hlam]
                              · linarith only [h2852, h3579, hlam]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            rcases p3563_3 (m.d 0 1) (by simp) with h3588 | h3588
                            · linarith only [h0, h3588, hlam]
                            · rcases p3563_3 (m.d 0 2) (by simp) with h3590 | h3590
                              · rcases p3563_3 (m.d 0 3) (by simp) with h3591 | h3591
                                · linarith only [h2852, h3591, hlam]
                                · linarith only [h2855, h3591, hlam]
                              · linarith only [h2853, h3590, hlam]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p3563_1, u5ehi0]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [h2856, h3494, h3498, hc01, hc12, hlam, hphi, p3563_1]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [h2852, hlam, p3563_1]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [hlam, p3563_0]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [h2856, h3494, h3498, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3563_1]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [h2856, hlam, p3563_1]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [h2576, h3499, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3563_1]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [h2853, hlam, p3563_0]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [h2855, hlam, p3563_0]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [hlam, p3563_0]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [h3492, hlam, p3563_0]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [h2856, h3494, h3498, hc01, hc12, hlam, hphi, p3563_1]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [h2854, hlam, p3563_1]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [h2852, h2856, h3494, h3498, h3556, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3563_1]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [h2576, h2856, h3494, h3498, hc01, hc12, hlam, hphi, p3563_1]
                          · have p3563_0 := h3563c.1
                            have p3563_1 := h3563c.2.1
                            have p3563_2 := h3563c.2.2.1
                            have p3563_3 := h3563c.2.2.2
                            linarith only [hlam, p3563_0]
                  · linarith only [h2855, h2856, h3494, h3498, h3556, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3612 | h3612
                · linarith only [h2854, h3492, h3497, h3498, h3612, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3614 | h3614
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3615 | h3615
                    · linarith only [h2249, h3498, h3615, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3617 | h3617
                      · linarith only [h0, h2853, h3612, h3617, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3619 | h3619
                        · linarith only [h2576, h3612, h3619, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases h0bigk with h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c
                          · have p3621_0 := h3621c.1
                            have p3621_1 := h3621c.2.1
                            have p3621_2 := h3621c.2.2.1
                            have p3621_3 := h3621c.2.2.2
                            linarith only [hlam, p3621_0]
                          · have p3621_0 := h3621c.1
                            have p3621_1 := h3621c.2.1
                            have p3621_2 := h3621c.2.2.1
                            have p3621_3 := h3621c.2.2.2
                            linarith only [h0, hlam, p3621_1]
                          · have p3621_0 := h3621c.1
                            have p3621_1 := h3621c.2.1
                            have p3621_2 := h3621c.2.2.1
                            have p3621_3 := h3621c.2.2.2
                            linarith only [h2249, hlam, p3621_0]
                          · have p3621_0 := h3621c.1
                            have p3621_1 := h3621c.2.1
                            have p3621_2 := h3621c.2.2.1
                            have p3621_3 := h3621c.2.2.2
                            linarith only [h2576, hlam, p3621_1]
                          · have p3621_0 := h3621c.1
                            have p3621_1 := h3621c.2.1
                            have p3621_2 := h3621c.2.2.1
                            have p3621_3 := h3621c.2.2.2
                            linarith only [h2850, hlam, p3621_1]
                          · have p3621_0 := h3621c.1
                            have p3621_1 := h3621c.2.1
                            have p3621_2 := h3621c.2.2.1
                            have p3621_3 := h3621c.2.2.2
                            rcases p3621_3 (m.d 0 1) (by simp) with h3627 | h3627
                            · linarith only [h0, h3627, hlam]
                            · rcases p3621_3 (m.d 0 2) (by simp) with h3629 | h3629
                              · rcases p3621_3 (m.d 0 3) (by simp) with h3630 | h3630
                                · linarith only [h2852, h3630, hlam]
                                · linarith only [h2249, h3630, hlam]
                              · linarith only [h0, h3629, hlam]
                          · have p3621_0 := h3621c.1
                            have p3621_1 := h3621c.2.1
                            have p3621_2 := h3621c.2.2.1
                            have p3621_3 := h3621c.2.2.2
                            linarith only [hlam, p3621_0]
                          · have p3621_0 := h3621c.1
                            have p3621_1 := h3621c.2.1
                            have p3621_2 := h3621c.2.2.1
                            have p3621_3 := h3621c.2.2.2
                            rcases p3621_3 (m.d 0 1) (by simp) with h3635 | h3635
                            · linarith only [h0, h3635, hlam]
                            · rcases p3621_3 (m.d 0 2) (by simp) with h3637 | h3637
                              · rcases p3621_3 (m.d 0 3) (by simp) with h3638 | h3638
                                · linarith only [h2852, h3638, hlam]
                                · rcases p3621_3 (m.d 0 4) (by simp) with h3640 | h3640
                                  · linarith only [h2853, h3640, hlam]
                                  · rcases p3621_3 (m.d 0 5) (by simp) with h3642 | h3642
                                    · linarith only [h2854, h3642, hlam]
                                    · linarith only [h2856, h3642, hlam]
                              · linarith only [h2852, h3637, hlam]
                          · have p3621_0 := h3621c.1
                            have p3621_1 := h3621c.2.1
                            have p3621_2 := h3621c.2.2.1
                            have p3621_3 := h3621c.2.2.2
                            rcases p3621_3 (m.d 0 1) (by simp) with h3646 | h3646
                            · linarith only [h0, h3646, hlam]
                            · rcases p3621_3 (m.d 0 2) (by simp) with h3648 | h3648
                              · rcases p3621_3 (m.d 0 3) (by simp) with h3649 | h3649
                                · linarith only [h2852, h3649, hlam]
                                · linarith only [h2855, h3649, hlam]
                              · linarith only [h2853, h3648, hlam]
                          · have p3621_0 := h3621c.1
                            have p3621_1 := h3621c.2.1
                            have p3621_2 := h3621c.2.2.1
                            have p3621_3 := h3621c.2.2.2
                            linarith only [h0, h2854, hc12, hlam, hphi, ht01, ht0b, ht5b, p3621_1, u5ehi2]
                          · have p3621_0 := h3621c.1
                            have p3621_1 := h3621c.2.1
                            have p3621_2 := h3621c.2.2.1
                            have p3621_3 := h3621c.2.2.2
                            linarith only [h2249, h3498, hc01, hc35, hlam, hphi, ht12, ht23, p3621_1]
                          · have p3621_0 := h3621c.1
                            have p3621_1 := h3621c.2.1
                            have p3621_2 := h3621c.2.2.1
                            have p3621_3 := h3621c.2.2.2
                            linarith only [h2852, hlam, p3621_1]
                          · have p3621_0 := h3621c.1
                            have p3621_1 := h3621c.2.1
                            have p3621_2 := h3621c.2.2.1
                            have p3621_3 := h3621c.2.2.2
                            linarith only [hlam, p3621_0]
                          · have p3621_0 := h3621c.1
                            have p3621_1 := h3621c.2.1
                            have p3621_2 := h3621c.2.2.1
                            have p3621_3 := h3621c.2.2.2
                            linarith only [h2249, h3498, h3619, hc04, hc45, hlam, hphi, p3621_1]
                          · have p3621_0 := h3621c.1
                            have p3621_1 := h3621c.2.1
                            have p3621_2 := h3621c.2.2.1
                            have p3621_3 := h3621c.2.2.2
                            linarith only [h2856, hlam, p3621_1]
                          · have p3621_0 := h3621c.1
                            have p3621_1 := h3621c.2.1
                            have p3621_2 := h3621c.2.2.1
                            have p3621_3 := h3621c.2.2.2
                            linarith only [h2249, h2855, h3498, h3619, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3621_1]
                          · have p3621_0 := h3621c.1
                            have p3621_1 := h3621c.2.1
                            have p3621_2 := h3621c.2.2.1
                            have p3621_3 := h3621c.2.2.2
                            linarith only [h2853, hlam, p3621_0]
                          · have p3621_0 := h3621c.1
                            have p3621_1 := h3621c.2.1
                            have p3621_2 := h3621c.2.2.1
                            have p3621_3 := h3621c.2.2.2
                            linarith only [h2855, hlam, p3621_0]
                          · have p3621_0 := h3621c.1
                            have p3621_1 := h3621c.2.1
                            have p3621_2 := h3621c.2.2.1
                            have p3621_3 := h3621c.2.2.2
                            linarith only [hlam, p3621_0]
                          · have p3621_0 := h3621c.1
                            have p3621_1 := h3621c.2.1
                            have p3621_2 := h3621c.2.2.1
                            have p3621_3 := h3621c.2.2.2
                            linarith only [h3492, hlam, p3621_0]
                          · have p3621_0 := h3621c.1
                            have p3621_1 := h3621c.2.1
                            have p3621_2 := h3621c.2.2.1
                            have p3621_3 := h3621c.2.2.2
                            rcases p3621_3 (m.d 0 1) (by simp) with h3664 | h3664
                            · linarith only [h2850, h3664, hlam]
                            · rcases p3621_3 (m.d 0 2) (by simp) with h3666 | h3666
                              · rcases p3621_3 (m.d 0 3) (by simp) with h3667 | h3667
                                · linarith only [h2856, h3667, hlam]
                                · linarith only [h2249, h3667, hlam]
                              · linarith only [h0, h3666, hlam]
                          · have p3621_0 := h3621c.1
                            have p3621_1 := h3621c.2.1
                            have p3621_2 := h3621c.2.2.1
                            have p3621_3 := h3621c.2.2.2
                            linarith only [h2854, hlam, p3621_1]
                          · have p3621_0 := h3621c.1
                            have p3621_1 := h3621c.2.1
                            have p3621_2 := h3621c.2.2.1
                            have p3621_3 := h3621c.2.2.2
                            linarith only [h2855, h2856, h3619, hc34, hc45, hlam, hphi, p3621_1]
                          · have p3621_0 := h3621c.1
                            have p3621_1 := h3621c.2.1
                            have p3621_2 := h3621c.2.2.1
                            have p3621_3 := h3621c.2.2.2
                            rcases p3621_3 (m.d 0 1) (by simp) with h3673 | h3673
                            · linarith only [h2850, h3673, hlam]
                            · rcases p3621_3 (m.d 0 2) (by simp) with h3675 | h3675
                              · rcases p3621_3 (m.d 0 3) (by simp) with h3676 | h3676
                                · linarith only [h2856, h3676, hlam]
                                · linarith only [h2855, h3676, hlam]
                              · linarith only [h2853, h3675, hlam]
                          · have p3621_0 := h3621c.1
                            have p3621_1 := h3621c.2.1
                            have p3621_2 := h3621c.2.2.1
                            have p3621_3 := h3621c.2.2.2
                            linarith only [hlam, p3621_0]
                  · linarith only [h2855, h2856, h3614, hc23, hc35, hlam, hphi]
            · linarith only [h2249, h2855, h3497, hlam]
          · linarith only [h0, h2854, h3496, hlam]
        · linarith only [h0, h2854, h3495, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
      · linarith only [h0, h2854, h3494, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]

end R2N4
