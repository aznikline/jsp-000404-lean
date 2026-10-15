import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8870000 in
theorem r1l7_11_13_25_L_I_L_R_H_I_x1_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2319 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2512 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2736 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2841 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h2842 | h2842
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2843 | h2843
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2844 | h2844
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2845 | h2845
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2846 | h2846
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2847 | h2847
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2848 | h2848
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2849 | h2849
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2850 | h2850
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2851 | h2851
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2852 | h2852
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2853 | h2853
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2854 | h2854
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2855 | h2855
                            · rcases h1bigk with h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c | h2856c
                              · have p2856_0 := h2856c.1
                                have p2856_1 := h2856c.2.1
                                have p2856_2 := h2856c.2.2.1
                                have p2856_3 := h2856c.2.2.2
                                linarith only [hlam, p2856_0]
                              · have p2856_0 := h2856c.1
                                have p2856_1 := h2856c.2.1
                                have p2856_2 := h2856c.2.2.1
                                have p2856_3 := h2856c.2.2.2
                                linarith only [h0, hlam, p2856_0]
                              · have p2856_0 := h2856c.1
                                have p2856_1 := h2856c.2.1
                                have p2856_2 := h2856c.2.2.1
                                have p2856_3 := h2856c.2.2.2
                                linarith only [h2319, hlam, p2856_0]
                              · have p2856_0 := h2856c.1
                                have p2856_1 := h2856c.2.1
                                have p2856_2 := h2856c.2.2.1
                                have p2856_3 := h2856c.2.2.2
                                linarith only [h2512, hlam, p2856_0]
                              · have p2856_0 := h2856c.1
                                have p2856_1 := h2856c.2.1
                                have p2856_2 := h2856c.2.2.1
                                have p2856_3 := h2856c.2.2.2
                                linarith only [h2736, hlam, p2856_0]
                              · have p2856_0 := h2856c.1
                                have p2856_1 := h2856c.2.1
                                have p2856_2 := h2856c.2.2.1
                                have p2856_3 := h2856c.2.2.2
                                rcases p2856_3 (m.d 0 1) (by simp) with h2862 | h2862
                                · linarith only [h2862, hlam, p2856_0]
                                · rcases p2856_3 (m.d 1 2) (by simp) with h2864 | h2864
                                  · rcases p2856_3 (m.d 1 3) (by simp) with h2865 | h2865
                                    · linarith only [h2846, h2865, hlam]
                                    · linarith only [h2319, h2865, hlam]
                                  · linarith only [h2864, hlam, p2856_0]
                              · have p2856_0 := h2856c.1
                                have p2856_1 := h2856c.2.1
                                have p2856_2 := h2856c.2.2.1
                                have p2856_3 := h2856c.2.2.2
                                linarith only [hlam, p2856_0]
                              · have p2856_0 := h2856c.1
                                have p2856_1 := h2856c.2.1
                                have p2856_2 := h2856c.2.2.1
                                have p2856_3 := h2856c.2.2.2
                                linarith only [h2319, hc01, hc12, hlam, hphi, p2856_1]
                              · have p2856_0 := h2856c.1
                                have p2856_1 := h2856c.2.1
                                have p2856_2 := h2856c.2.2.1
                                have p2856_3 := h2856c.2.2.2
                                linarith only [h2512, hc01, hc12, hlam, hphi, p2856_1]
                              · have p2856_0 := h2856c.1
                                have p2856_1 := h2856c.2.1
                                have p2856_2 := h2856c.2.2.1
                                have p2856_3 := h2856c.2.2.2
                                linarith only [h2736, hc01, hc12, hlam, hphi, p2856_1]
                              · have p2856_0 := h2856c.1
                                have p2856_1 := h2856c.2.1
                                have p2856_2 := h2856c.2.2.1
                                have p2856_3 := h2856c.2.2.2
                                rcases p2856_3 (m.d 0 1) (by simp) with h2873 | h2873
                                · linarith only [h2873, hlam, p2856_0]
                                · rcases p2856_3 (m.d 1 2) (by simp) with h2875 | h2875
                                  · rcases p2856_3 (m.d 1 3) (by simp) with h2876 | h2876
                                    · rcases p2856_3 (m.d 1 4) (by simp) with h2877 | h2877
                                      · linarith only [h2849, h2877, hlam]
                                      · linarith only [h2512, h2877, hlam]
                                    · linarith only [h2876, hlam, p2856_0]
                                  · linarith only [h0, h2875, hlam]
                              · have p2856_0 := h2856c.1
                                have p2856_1 := h2856c.2.1
                                have p2856_2 := h2856c.2.2.1
                                have p2856_3 := h2856c.2.2.2
                                linarith only [h2846, hlam, p2856_1]
                              · have p2856_0 := h2856c.1
                                have p2856_1 := h2856c.2.1
                                have p2856_2 := h2856c.2.2.1
                                have p2856_3 := h2856c.2.2.2
                                linarith only [hlam, p2856_0]
                              · have p2856_0 := h2856c.1
                                have p2856_1 := h2856c.2.1
                                have p2856_2 := h2856c.2.2.1
                                have p2856_3 := h2856c.2.2.2
                                linarith only [h2736, h2851, hc01, hc13, hlam, hphi, p2856_1]
                              · have p2856_0 := h2856c.1
                                have p2856_1 := h2856c.2.1
                                have p2856_2 := h2856c.2.2.1
                                have p2856_3 := h2856c.2.2.2
                                linarith only [h2736, h2846, hc01, hc12, hlam, hphi, p2856_1]
                              · have p2856_0 := h2856c.1
                                have p2856_1 := h2856c.2.1
                                have p2856_2 := h2856c.2.2.1
                                have p2856_3 := h2856c.2.2.2
                                rcases p2856_3 (m.d 0 1) (by simp) with h2886 | h2886
                                · linarith only [h2886, hlam, p2856_0]
                                · rcases p2856_3 (m.d 1 2) (by simp) with h2888 | h2888
                                  · rcases p2856_3 (m.d 1 3) (by simp) with h2889 | h2889
                                    · rcases p2856_3 (m.d 1 4) (by simp) with h2890 | h2890
                                      · rcases p2856_3 (m.d 1 5) (by simp) with h2891 | h2891
                                        · linarith only [h2851, h2891, hlam]
                                        · linarith only [h2736, h2891, hlam]
                                      · linarith only [h2890, hlam, p2856_0]
                                    · linarith only [h2319, h2889, hlam]
                                  · linarith only [h0, h2888, hlam]
                              · have p2856_0 := h2856c.1
                                have p2856_1 := h2856c.2.1
                                have p2856_2 := h2856c.2.2.1
                                have p2856_3 := h2856c.2.2.2
                                linarith only [h2847, hlam, p2856_1]
                              · have p2856_0 := h2856c.1
                                have p2856_1 := h2856c.2.1
                                have p2856_2 := h2856c.2.2.1
                                have p2856_3 := h2856c.2.2.2
                                linarith only [h2849, hlam, p2856_0]
                              · have p2856_0 := h2856c.1
                                have p2856_1 := h2856c.2.1
                                have p2856_2 := h2856c.2.2.1
                                have p2856_3 := h2856c.2.2.2
                                linarith only [hlam, p2856_0]
                              · have p2856_0 := h2856c.1
                                have p2856_1 := h2856c.2.1
                                have p2856_2 := h2856c.2.2.1
                                have p2856_3 := h2856c.2.2.2
                                linarith only [h2736, hc01, hc14, hlam, hphi, p2856_1]
                              · have p2856_0 := h2856c.1
                                have p2856_1 := h2856c.2.1
                                have p2856_2 := h2856c.2.2.1
                                have p2856_3 := h2856c.2.2.2
                                rcases p2856_3 (m.d 0 1) (by simp) with h2901 | h2901
                                · linarith only [h2901, hlam, p2856_0]
                                · rcases p2856_3 (m.d 1 2) (by simp) with h2903 | h2903
                                  · rcases p2856_3 (m.d 1 3) (by simp) with h2904 | h2904
                                    · rcases p2856_3 (m.d 1 4) (by simp) with h2905 | h2905
                                      · rcases p2856_3 (m.d 1 5) (by simp) with h2906 | h2906
                                        · rcases h5bigk with h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c | h2907c
                                          · have p2907_0 := h2907c.1
                                            have p2907_1 := h2907c.2.1
                                            have p2907_2 := h2907c.2.2.1
                                            have p2907_3 := h2907c.2.2.2
                                            linarith only [hlam, p2907_0]
                                          · have p2907_0 := h2907c.1
                                            have p2907_1 := h2907c.2.1
                                            have p2907_2 := h2907c.2.2.1
                                            have p2907_3 := h2907c.2.2.2
                                            linarith only [h2736, hlam, p2907_1]
                                          · have p2907_0 := h2907c.1
                                            have p2907_1 := h2907c.2.1
                                            have p2907_2 := h2907c.2.2.1
                                            have p2907_3 := h2907c.2.2.2
                                            linarith only [h2853, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p2907_1, u3ehi4]
                                          · have p2907_0 := h2907c.1
                                            have p2907_1 := h2907c.2.1
                                            have p2907_2 := h2907c.2.2.1
                                            have p2907_3 := h2907c.2.2.2
                                            linarith only [h2844, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p2907_1, u3ehi4]
                                          · have p2907_0 := h2907c.1
                                            have p2907_1 := h2907c.2.1
                                            have p2907_2 := h2907c.2.2.1
                                            have p2907_3 := h2907c.2.2.2
                                            rcases p2907_3 (m.d 0 5) (by simp) with h2912 | h2912
                                            · rcases p2907_3 (m.d 1 5) (by simp) with h2913 | h2913
                                              · rcases p2907_3 (m.d 2 5) (by simp) with h2914 | h2914
                                                · linarith only [h2842, h2914, hlam]
                                                · linarith only [h2854, h2914, hlam]
                                              · linarith only [h2851, h2913, hlam]
                                            · linarith only [h2845, h2912, hlam]
                                          · have p2907_0 := h2907c.1
                                            have p2907_1 := h2907c.2.1
                                            have p2907_2 := h2907c.2.2.1
                                            have p2907_3 := h2907c.2.2.2
                                            linarith only [h2736, h2846, h2849, h2851, hc01, hc12, hlam, hphi, p2907_1]
                                          · have p2907_0 := h2907c.1
                                            have p2907_1 := h2907c.2.1
                                            have p2907_2 := h2907c.2.2.1
                                            have p2907_3 := h2907c.2.2.2
                                            linarith only [hlam, p2907_0]
                                          · have p2907_0 := h2907c.1
                                            have p2907_1 := h2907c.2.1
                                            have p2907_2 := h2907c.2.2.1
                                            have p2907_3 := h2907c.2.2.2
                                            linarith only [h2846, h2849, h2851, h2853, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2907_1, u3ehi4]
                                          · have p2907_0 := h2907c.1
                                            have p2907_1 := h2907c.2.1
                                            have p2907_2 := h2907c.2.2.1
                                            have p2907_3 := h2907c.2.2.2
                                            linarith only [h2846, h2849, h2851, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2907_1, u3ehi4]
                                          · have p2907_0 := h2907c.1
                                            have p2907_1 := h2907c.2.1
                                            have p2907_2 := h2907c.2.2.1
                                            have p2907_3 := h2907c.2.2.2
                                            rcases p2907_3 (m.d 0 5) (by simp) with h2923 | h2923
                                            · linarith only [h2736, h2923, hlam]
                                            · linarith only [h2845, h2923, hlam]
                                          · have p2907_0 := h2907c.1
                                            have p2907_1 := h2907c.2.1
                                            have p2907_2 := h2907c.2.2.1
                                            have p2907_3 := h2907c.2.2.2
                                            linarith only [h2842, hlam, p2907_1]
                                          · have p2907_0 := h2907c.1
                                            have p2907_1 := h2907c.2.1
                                            have p2907_2 := h2907c.2.2.1
                                            have p2907_3 := h2907c.2.2.2
                                            linarith only [h2848, hlam, p2907_1]
                                          · have p2907_0 := h2907c.1
                                            have p2907_1 := h2907c.2.1
                                            have p2907_2 := h2907c.2.2.1
                                            have p2907_3 := h2907c.2.2.2
                                            linarith only [hlam, p2907_0]
                                          · have p2907_0 := h2907c.1
                                            have p2907_1 := h2907c.2.1
                                            have p2907_2 := h2907c.2.2.1
                                            have p2907_3 := h2907c.2.2.2
                                            linarith only [h2842, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p2907_1, u3ehi4]
                                          · have p2907_0 := h2907c.1
                                            have p2907_1 := h2907c.2.1
                                            have p2907_2 := h2907c.2.2.1
                                            have p2907_3 := h2907c.2.2.2
                                            linarith only [h0, h2841, h2852, h2854, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2907_1]
                                          · have p2907_0 := h2907c.1
                                            have p2907_1 := h2907c.2.1
                                            have p2907_2 := h2907c.2.2.1
                                            have p2907_3 := h2907c.2.2.2
                                            linarith only [h2844, hlam, p2907_0]
                                          · have p2907_0 := h2907c.1
                                            have p2907_1 := h2907c.2.1
                                            have p2907_2 := h2907c.2.2.1
                                            have p2907_3 := h2907c.2.2.2
                                            linarith only [h2850, hlam, p2907_0]
                                          · have p2907_0 := h2907c.1
                                            have p2907_1 := h2907c.2.1
                                            have p2907_2 := h2907c.2.2.1
                                            have p2907_3 := h2907c.2.2.2
                                            linarith only [h2853, hlam, p2907_0]
                                          · have p2907_0 := h2907c.1
                                            have p2907_1 := h2907c.2.1
                                            have p2907_2 := h2907c.2.2.1
                                            have p2907_3 := h2907c.2.2.2
                                            linarith only [hlam, p2907_0]
                                          · have p2907_0 := h2907c.1
                                            have p2907_1 := h2907c.2.1
                                            have p2907_2 := h2907c.2.2.1
                                            have p2907_3 := h2907c.2.2.2
                                            linarith only [h2319, h2843, h2846, h2855, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2907_1]
                                          · have p2907_0 := h2907c.1
                                            have p2907_1 := h2907c.2.1
                                            have p2907_2 := h2907c.2.2.1
                                            have p2907_3 := h2907c.2.2.2
                                            linarith only [h2845, hlam, p2907_0]
                                          · have p2907_0 := h2907c.1
                                            have p2907_1 := h2907c.2.1
                                            have p2907_2 := h2907c.2.2.1
                                            have p2907_3 := h2907c.2.2.2
                                            linarith only [h2851, hlam, p2907_0]
                                          · have p2907_0 := h2907c.1
                                            have p2907_1 := h2907c.2.1
                                            have p2907_2 := h2907c.2.2.1
                                            have p2907_3 := h2907c.2.2.2
                                            linarith only [h2854, hlam, p2907_0]
                                          · have p2907_0 := h2907c.1
                                            have p2907_1 := h2907c.2.1
                                            have p2907_2 := h2907c.2.2.1
                                            have p2907_3 := h2907c.2.2.2
                                            linarith only [h2855, hlam, p2907_0]
                                          · have p2907_0 := h2907c.1
                                            have p2907_1 := h2907c.2.1
                                            have p2907_2 := h2907c.2.2.1
                                            have p2907_3 := h2907c.2.2.2
                                            linarith only [hlam, p2907_0]
                                        · linarith only [h2906, hlam, p2856_0]
                                      · linarith only [h2512, h2905, hlam]
                                    · linarith only [h2319, h2904, hlam]
                                  · linarith only [h0, h2903, hlam]
                              · have p2856_0 := h2856c.1
                                have p2856_1 := h2856c.2.1
                                have p2856_2 := h2856c.2.2.1
                                have p2856_3 := h2856c.2.2.2
                                linarith only [h2848, hlam, p2856_1]
                              · have p2856_0 := h2856c.1
                                have p2856_1 := h2856c.2.1
                                have p2856_2 := h2856c.2.2.1
                                have p2856_3 := h2856c.2.2.2
                                linarith only [h2850, hlam, p2856_0]
                              · have p2856_0 := h2856c.1
                                have p2856_1 := h2856c.2.1
                                have p2856_2 := h2856c.2.2.1
                                have p2856_3 := h2856c.2.2.2
                                linarith only [h2851, hlam, p2856_0]
                              · have p2856_0 := h2856c.1
                                have p2856_1 := h2856c.2.1
                                have p2856_2 := h2856c.2.2.1
                                have p2856_3 := h2856c.2.2.2
                                linarith only [hlam, p2856_0]
                            · linarith only [h0, h2841, h2852, h2854, h2855, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2950 | h2950
                            · linarith only [h0, h2841, h2852, h2854, h2950, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases h1bigk with h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c
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
                                linarith only [h2319, hlam, p2952_0]
                              · have p2952_0 := h2952c.1
                                have p2952_1 := h2952c.2.1
                                have p2952_2 := h2952c.2.2.1
                                have p2952_3 := h2952c.2.2.2
                                linarith only [h2512, hlam, p2952_0]
                              · have p2952_0 := h2952c.1
                                have p2952_1 := h2952c.2.1
                                have p2952_2 := h2952c.2.2.1
                                have p2952_3 := h2952c.2.2.2
                                linarith only [h2736, hlam, p2952_0]
                              · have p2952_0 := h2952c.1
                                have p2952_1 := h2952c.2.1
                                have p2952_2 := h2952c.2.2.1
                                have p2952_3 := h2952c.2.2.2
                                rcases p2952_3 (m.d 0 1) (by simp) with h2958 | h2958
                                · linarith only [h2958, hlam, p2952_0]
                                · rcases p2952_3 (m.d 1 2) (by simp) with h2960 | h2960
                                  · rcases p2952_3 (m.d 1 3) (by simp) with h2961 | h2961
                                    · linarith only [h2846, h2961, hlam]
                                    · linarith only [h2319, h2961, hlam]
                                  · linarith only [h2960, hlam, p2952_0]
                              · have p2952_0 := h2952c.1
                                have p2952_1 := h2952c.2.1
                                have p2952_2 := h2952c.2.2.1
                                have p2952_3 := h2952c.2.2.2
                                linarith only [hlam, p2952_0]
                              · have p2952_0 := h2952c.1
                                have p2952_1 := h2952c.2.1
                                have p2952_2 := h2952c.2.2.1
                                have p2952_3 := h2952c.2.2.2
                                linarith only [h2319, hc01, hc12, hlam, hphi, p2952_1]
                              · have p2952_0 := h2952c.1
                                have p2952_1 := h2952c.2.1
                                have p2952_2 := h2952c.2.2.1
                                have p2952_3 := h2952c.2.2.2
                                linarith only [h2512, h2845, h2852, h2854, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2952_1, u3ehi3]
                              · have p2952_0 := h2952c.1
                                have p2952_1 := h2952c.2.1
                                have p2952_2 := h2952c.2.2.1
                                have p2952_3 := h2952c.2.2.2
                                linarith only [h2736, h2845, h2852, h2854, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2952_1, u3ehi3]
                              · have p2952_0 := h2952c.1
                                have p2952_1 := h2952c.2.1
                                have p2952_2 := h2952c.2.2.1
                                have p2952_3 := h2952c.2.2.2
                                rcases p2952_3 (m.d 0 1) (by simp) with h2969 | h2969
                                · linarith only [h2969, hlam, p2952_0]
                                · rcases p2952_3 (m.d 1 2) (by simp) with h2971 | h2971
                                  · rcases p2952_3 (m.d 1 3) (by simp) with h2972 | h2972
                                    · rcases p2952_3 (m.d 1 4) (by simp) with h2973 | h2973
                                      · linarith only [h2849, h2973, hlam]
                                      · linarith only [h2512, h2973, hlam]
                                    · linarith only [h2972, hlam, p2952_0]
                                  · linarith only [h0, h2971, hlam]
                              · have p2952_0 := h2952c.1
                                have p2952_1 := h2952c.2.1
                                have p2952_2 := h2952c.2.2.1
                                have p2952_3 := h2952c.2.2.2
                                linarith only [h2846, hlam, p2952_1]
                              · have p2952_0 := h2952c.1
                                have p2952_1 := h2952c.2.1
                                have p2952_2 := h2952c.2.2.1
                                have p2952_3 := h2952c.2.2.2
                                linarith only [hlam, p2952_0]
                              · have p2952_0 := h2952c.1
                                have p2952_1 := h2952c.2.1
                                have p2952_2 := h2952c.2.2.1
                                have p2952_3 := h2952c.2.2.2
                                linarith only [h2512, h2845, h2852, h2854, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2952_1, u3ehi3]
                              · have p2952_0 := h2952c.1
                                have p2952_1 := h2952c.2.1
                                have p2952_2 := h2952c.2.2.1
                                have p2952_3 := h2952c.2.2.2
                                linarith only [h2736, h2845, h2846, h2852, h2854, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2952_1, u3ehi3]
                              · have p2952_0 := h2952c.1
                                have p2952_1 := h2952c.2.1
                                have p2952_2 := h2952c.2.2.1
                                have p2952_3 := h2952c.2.2.2
                                rcases p2952_3 (m.d 0 1) (by simp) with h2982 | h2982
                                · linarith only [h2982, hlam, p2952_0]
                                · rcases p2952_3 (m.d 1 2) (by simp) with h2984 | h2984
                                  · rcases p2952_3 (m.d 1 3) (by simp) with h2985 | h2985
                                    · rcases p2952_3 (m.d 1 4) (by simp) with h2986 | h2986
                                      · rcases p2952_3 (m.d 1 5) (by simp) with h2987 | h2987
                                        · linarith only [h2851, h2987, hlam]
                                        · linarith only [h2736, h2987, hlam]
                                      · linarith only [h2986, hlam, p2952_0]
                                    · linarith only [h2319, h2985, hlam]
                                  · linarith only [h0, h2984, hlam]
                              · have p2952_0 := h2952c.1
                                have p2952_1 := h2952c.2.1
                                have p2952_2 := h2952c.2.2.1
                                have p2952_3 := h2952c.2.2.2
                                linarith only [h2847, hlam, p2952_1]
                              · have p2952_0 := h2952c.1
                                have p2952_1 := h2952c.2.1
                                have p2952_2 := h2952c.2.2.1
                                have p2952_3 := h2952c.2.2.2
                                linarith only [h2849, hlam, p2952_0]
                              · have p2952_0 := h2952c.1
                                have p2952_1 := h2952c.2.1
                                have p2952_2 := h2952c.2.2.1
                                have p2952_3 := h2952c.2.2.2
                                linarith only [hlam, p2952_0]
                              · have p2952_0 := h2952c.1
                                have p2952_1 := h2952c.2.1
                                have p2952_2 := h2952c.2.2.1
                                have p2952_3 := h2952c.2.2.2
                                linarith only [h2736, h2845, h2852, h2854, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2952_1, u3ehi3]
                              · have p2952_0 := h2952c.1
                                have p2952_1 := h2952c.2.1
                                have p2952_2 := h2952c.2.2.1
                                have p2952_3 := h2952c.2.2.2
                                rcases p2952_3 (m.d 0 1) (by simp) with h2997 | h2997
                                · linarith only [h2997, hlam, p2952_0]
                                · rcases p2952_3 (m.d 1 2) (by simp) with h2999 | h2999
                                  · rcases p2952_3 (m.d 1 3) (by simp) with h3000 | h3000
                                    · rcases p2952_3 (m.d 1 4) (by simp) with h3001 | h3001
                                      · rcases p2952_3 (m.d 1 5) (by simp) with h3002 | h3002
                                        · rcases h5bigk with h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c | h3003c
                                          · have p3003_0 := h3003c.1
                                            have p3003_1 := h3003c.2.1
                                            have p3003_2 := h3003c.2.2.1
                                            have p3003_3 := h3003c.2.2.2
                                            linarith only [hlam, p3003_0]
                                          · have p3003_0 := h3003c.1
                                            have p3003_1 := h3003c.2.1
                                            have p3003_2 := h3003c.2.2.1
                                            have p3003_3 := h3003c.2.2.2
                                            linarith only [h2736, hlam, p3003_1]
                                          · have p3003_0 := h3003c.1
                                            have p3003_1 := h3003c.2.1
                                            have p3003_2 := h3003c.2.2.1
                                            have p3003_3 := h3003c.2.2.2
                                            linarith only [h2512, h2845, h2846, h2849, h2853, h2950, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3003_1, u3ehi3]
                                          · have p3003_0 := h3003c.1
                                            have p3003_1 := h3003c.2.1
                                            have p3003_2 := h3003c.2.2.1
                                            have p3003_3 := h3003c.2.2.2
                                            linarith only [h2512, h2845, h2846, h2849, h2950, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3003_1, u3ehi3]
                                          · have p3003_0 := h3003c.1
                                            have p3003_1 := h3003c.2.1
                                            have p3003_2 := h3003c.2.2.1
                                            have p3003_3 := h3003c.2.2.2
                                            linarith only [h2512, h2845, h2846, h2849, h2852, h2854, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3003_1, u3ehi3]
                                          · have p3003_0 := h3003c.1
                                            have p3003_1 := h3003c.2.1
                                            have p3003_2 := h3003c.2.2.1
                                            have p3003_3 := h3003c.2.2.2
                                            linarith only [h2736, h2846, h2849, h2851, hc01, hc12, hlam, hphi, p3003_1]
                                          · have p3003_0 := h3003c.1
                                            have p3003_1 := h3003c.2.1
                                            have p3003_2 := h3003c.2.2.1
                                            have p3003_3 := h3003c.2.2.2
                                            linarith only [hlam, p3003_0]
                                          · have p3003_0 := h3003c.1
                                            have p3003_1 := h3003c.2.1
                                            have p3003_2 := h3003c.2.2.1
                                            have p3003_3 := h3003c.2.2.2
                                            linarith only [h2846, h2849, h2851, h2853, h2950, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3003_1, u3ehi3]
                                          · have p3003_0 := h3003c.1
                                            have p3003_1 := h3003c.2.1
                                            have p3003_2 := h3003c.2.2.1
                                            have p3003_3 := h3003c.2.2.2
                                            linarith only [h2846, h2849, h2851, h2950, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3003_1, u3ehi3]
                                          · have p3003_0 := h3003c.1
                                            have p3003_1 := h3003c.2.1
                                            have p3003_2 := h3003c.2.2.1
                                            have p3003_3 := h3003c.2.2.2
                                            linarith only [h2846, h2849, h2851, h2852, h2854, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3003_1, u3ehi3]
                                          · have p3003_0 := h3003c.1
                                            have p3003_1 := h3003c.2.1
                                            have p3003_2 := h3003c.2.2.1
                                            have p3003_3 := h3003c.2.2.2
                                            linarith only [h2842, hlam, p3003_1]
                                          · have p3003_0 := h3003c.1
                                            have p3003_1 := h3003c.2.1
                                            have p3003_2 := h3003c.2.2.1
                                            have p3003_3 := h3003c.2.2.2
                                            linarith only [h2848, hlam, p3003_1]
                                          · have p3003_0 := h3003c.1
                                            have p3003_1 := h3003c.2.1
                                            have p3003_2 := h3003c.2.2.1
                                            have p3003_3 := h3003c.2.2.2
                                            linarith only [hlam, p3003_0]
                                          · have p3003_0 := h3003c.1
                                            have p3003_1 := h3003c.2.1
                                            have p3003_2 := h3003c.2.2.1
                                            have p3003_3 := h3003c.2.2.2
                                            linarith only [h2950, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3003_1, u3ehi3]
                                          · have p3003_0 := h3003c.1
                                            have p3003_1 := h3003c.2.1
                                            have p3003_2 := h3003c.2.2.1
                                            have p3003_3 := h3003c.2.2.2
                                            linarith only [h2854, hlam, p3003_1]
                                          · have p3003_0 := h3003c.1
                                            have p3003_1 := h3003c.2.1
                                            have p3003_2 := h3003c.2.2.1
                                            have p3003_3 := h3003c.2.2.2
                                            linarith only [h2844, hlam, p3003_0]
                                          · have p3003_0 := h3003c.1
                                            have p3003_1 := h3003c.2.1
                                            have p3003_2 := h3003c.2.2.1
                                            have p3003_3 := h3003c.2.2.2
                                            linarith only [h2850, hlam, p3003_0]
                                          · have p3003_0 := h3003c.1
                                            have p3003_1 := h3003c.2.1
                                            have p3003_2 := h3003c.2.2.1
                                            have p3003_3 := h3003c.2.2.2
                                            linarith only [h2853, hlam, p3003_0]
                                          · have p3003_0 := h3003c.1
                                            have p3003_1 := h3003c.2.1
                                            have p3003_2 := h3003c.2.2.1
                                            have p3003_3 := h3003c.2.2.2
                                            linarith only [hlam, p3003_0]
                                          · have p3003_0 := h3003c.1
                                            have p3003_1 := h3003c.2.1
                                            have p3003_2 := h3003c.2.2.1
                                            have p3003_3 := h3003c.2.2.2
                                            linarith only [h2950, hlam, p3003_1]
                                          · have p3003_0 := h3003c.1
                                            have p3003_1 := h3003c.2.1
                                            have p3003_2 := h3003c.2.2.1
                                            have p3003_3 := h3003c.2.2.2
                                            linarith only [h2845, hlam, p3003_0]
                                          · have p3003_0 := h3003c.1
                                            have p3003_1 := h3003c.2.1
                                            have p3003_2 := h3003c.2.2.1
                                            have p3003_3 := h3003c.2.2.2
                                            linarith only [h2851, hlam, p3003_0]
                                          · have p3003_0 := h3003c.1
                                            have p3003_1 := h3003c.2.1
                                            have p3003_2 := h3003c.2.2.1
                                            have p3003_3 := h3003c.2.2.2
                                            linarith only [h2512, h2845, h2846, h2849, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p3003_1]
                                          · have p3003_0 := h3003c.1
                                            have p3003_1 := h3003c.2.1
                                            have p3003_2 := h3003c.2.2.1
                                            have p3003_3 := h3003c.2.2.2
                                            linarith only [h2512, h2845, h2846, h2849, h2950, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3003_1, u3ehi3]
                                          · have p3003_0 := h3003c.1
                                            have p3003_1 := h3003c.2.1
                                            have p3003_2 := h3003c.2.2.1
                                            have p3003_3 := h3003c.2.2.2
                                            linarith only [hlam, p3003_0]
                                        · linarith only [h3002, hlam, p2952_0]
                                      · linarith only [h2512, h3001, hlam]
                                    · linarith only [h2319, h3000, hlam]
                                  · linarith only [h0, h2999, hlam]
                              · have p2952_0 := h2952c.1
                                have p2952_1 := h2952c.2.1
                                have p2952_2 := h2952c.2.2.1
                                have p2952_3 := h2952c.2.2.2
                                linarith only [h2848, hlam, p2952_1]
                              · have p2952_0 := h2952c.1
                                have p2952_1 := h2952c.2.1
                                have p2952_2 := h2952c.2.2.1
                                have p2952_3 := h2952c.2.2.2
                                linarith only [h2850, hlam, p2952_0]
                              · have p2952_0 := h2952c.1
                                have p2952_1 := h2952c.2.1
                                have p2952_2 := h2952c.2.2.1
                                have p2952_3 := h2952c.2.2.2
                                linarith only [h2851, hlam, p2952_0]
                              · have p2952_0 := h2952c.1
                                have p2952_1 := h2952c.2.1
                                have p2952_2 := h2952c.2.2.1
                                have p2952_3 := h2952c.2.2.2
                                linarith only [hlam, p2952_0]
                        · linarith only [h2319, h2844, h2846, h2852, h2853, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3038 | h3038
                        · linarith only [h2852, h3038, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3040 | h3040
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3041 | h3041
                            · rcases h1bigk with h3042c | h3042c | h3042c | h3042c | h3042c | h3042c | h3042c | h3042c | h3042c | h3042c | h3042c | h3042c | h3042c | h3042c | h3042c | h3042c | h3042c | h3042c | h3042c | h3042c | h3042c | h3042c | h3042c | h3042c | h3042c
                              · have p3042_0 := h3042c.1
                                have p3042_1 := h3042c.2.1
                                have p3042_2 := h3042c.2.2.1
                                have p3042_3 := h3042c.2.2.2
                                linarith only [hlam, p3042_0]
                              · have p3042_0 := h3042c.1
                                have p3042_1 := h3042c.2.1
                                have p3042_2 := h3042c.2.2.1
                                have p3042_3 := h3042c.2.2.2
                                linarith only [h0, hlam, p3042_0]
                              · have p3042_0 := h3042c.1
                                have p3042_1 := h3042c.2.1
                                have p3042_2 := h3042c.2.2.1
                                have p3042_3 := h3042c.2.2.2
                                linarith only [h2319, hlam, p3042_0]
                              · have p3042_0 := h3042c.1
                                have p3042_1 := h3042c.2.1
                                have p3042_2 := h3042c.2.2.1
                                have p3042_3 := h3042c.2.2.2
                                linarith only [h2512, hlam, p3042_0]
                              · have p3042_0 := h3042c.1
                                have p3042_1 := h3042c.2.1
                                have p3042_2 := h3042c.2.2.1
                                have p3042_3 := h3042c.2.2.2
                                linarith only [h2736, hlam, p3042_0]
                              · have p3042_0 := h3042c.1
                                have p3042_1 := h3042c.2.1
                                have p3042_2 := h3042c.2.2.1
                                have p3042_3 := h3042c.2.2.2
                                rcases p3042_3 (m.d 0 1) (by simp) with h3048 | h3048
                                · linarith only [h3048, hlam, p3042_0]
                                · rcases p3042_3 (m.d 1 2) (by simp) with h3050 | h3050
                                  · rcases p3042_3 (m.d 1 3) (by simp) with h3051 | h3051
                                    · linarith only [h2846, h3051, hlam]
                                    · linarith only [h2319, h3051, hlam]
                                  · linarith only [h3050, hlam, p3042_0]
                              · have p3042_0 := h3042c.1
                                have p3042_1 := h3042c.2.1
                                have p3042_2 := h3042c.2.2.1
                                have p3042_3 := h3042c.2.2.2
                                linarith only [hlam, p3042_0]
                              · have p3042_0 := h3042c.1
                                have p3042_1 := h3042c.2.1
                                have p3042_2 := h3042c.2.2.1
                                have p3042_3 := h3042c.2.2.2
                                linarith only [h2319, h2843, h2852, h3040, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3042_1]
                              · have p3042_0 := h3042c.1
                                have p3042_1 := h3042c.2.1
                                have p3042_2 := h3042c.2.2.1
                                have p3042_3 := h3042c.2.2.2
                                linarith only [h2736, h2844, h2851, h3038, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3042_1, u3ehi2]
                              · have p3042_0 := h3042c.1
                                have p3042_1 := h3042c.2.1
                                have p3042_2 := h3042c.2.2.1
                                have p3042_3 := h3042c.2.2.2
                                linarith only [h2736, h2844, h3038, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3042_1, u3ehi2]
                              · have p3042_0 := h3042c.1
                                have p3042_1 := h3042c.2.1
                                have p3042_2 := h3042c.2.2.1
                                have p3042_3 := h3042c.2.2.2
                                rcases p3042_3 (m.d 0 1) (by simp) with h3059 | h3059
                                · linarith only [h3059, hlam, p3042_0]
                                · rcases p3042_3 (m.d 1 2) (by simp) with h3061 | h3061
                                  · rcases p3042_3 (m.d 1 3) (by simp) with h3062 | h3062
                                    · rcases p3042_3 (m.d 1 4) (by simp) with h3063 | h3063
                                      · linarith only [h2849, h3063, hlam]
                                      · linarith only [h2512, h3063, hlam]
                                    · linarith only [h3062, hlam, p3042_0]
                                  · linarith only [h0, h3061, hlam]
                              · have p3042_0 := h3042c.1
                                have p3042_1 := h3042c.2.1
                                have p3042_2 := h3042c.2.2.1
                                have p3042_3 := h3042c.2.2.2
                                linarith only [h2846, hlam, p3042_1]
                              · have p3042_0 := h3042c.1
                                have p3042_1 := h3042c.2.1
                                have p3042_2 := h3042c.2.2.1
                                have p3042_3 := h3042c.2.2.2
                                linarith only [hlam, p3042_0]
                              · have p3042_0 := h3042c.1
                                have p3042_1 := h3042c.2.1
                                have p3042_2 := h3042c.2.2.1
                                have p3042_3 := h3042c.2.2.2
                                linarith only [h2736, h2844, h2851, h3038, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3042_1, u3ehi2]
                              · have p3042_0 := h3042c.1
                                have p3042_1 := h3042c.2.1
                                have p3042_2 := h3042c.2.2.1
                                have p3042_3 := h3042c.2.2.2
                                linarith only [h2736, h2844, h2846, h3038, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3042_1, u3ehi2]
                              · have p3042_0 := h3042c.1
                                have p3042_1 := h3042c.2.1
                                have p3042_2 := h3042c.2.2.1
                                have p3042_3 := h3042c.2.2.2
                                rcases p3042_3 (m.d 0 1) (by simp) with h3072 | h3072
                                · linarith only [h3072, hlam, p3042_0]
                                · rcases p3042_3 (m.d 1 2) (by simp) with h3074 | h3074
                                  · rcases p3042_3 (m.d 1 3) (by simp) with h3075 | h3075
                                    · rcases p3042_3 (m.d 1 4) (by simp) with h3076 | h3076
                                      · rcases p3042_3 (m.d 1 5) (by simp) with h3077 | h3077
                                        · linarith only [h2851, h3077, hlam]
                                        · linarith only [h2736, h3077, hlam]
                                      · linarith only [h3076, hlam, p3042_0]
                                    · linarith only [h2319, h3075, hlam]
                                  · linarith only [h0, h3074, hlam]
                              · have p3042_0 := h3042c.1
                                have p3042_1 := h3042c.2.1
                                have p3042_2 := h3042c.2.2.1
                                have p3042_3 := h3042c.2.2.2
                                linarith only [h2847, hlam, p3042_1]
                              · have p3042_0 := h3042c.1
                                have p3042_1 := h3042c.2.1
                                have p3042_2 := h3042c.2.2.1
                                have p3042_3 := h3042c.2.2.2
                                linarith only [h2849, hlam, p3042_0]
                              · have p3042_0 := h3042c.1
                                have p3042_1 := h3042c.2.1
                                have p3042_2 := h3042c.2.2.1
                                have p3042_3 := h3042c.2.2.2
                                linarith only [hlam, p3042_0]
                              · have p3042_0 := h3042c.1
                                have p3042_1 := h3042c.2.1
                                have p3042_2 := h3042c.2.2.1
                                have p3042_3 := h3042c.2.2.2
                                linarith only [h2736, h2844, h3038, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3042_1, u3ehi2]
                              · have p3042_0 := h3042c.1
                                have p3042_1 := h3042c.2.1
                                have p3042_2 := h3042c.2.2.1
                                have p3042_3 := h3042c.2.2.2
                                rcases p3042_3 (m.d 0 1) (by simp) with h3087 | h3087
                                · linarith only [h3087, hlam, p3042_0]
                                · rcases p3042_3 (m.d 1 2) (by simp) with h3089 | h3089
                                  · rcases p3042_3 (m.d 1 3) (by simp) with h3090 | h3090
                                    · rcases p3042_3 (m.d 1 4) (by simp) with h3091 | h3091
                                      · rcases p3042_3 (m.d 1 5) (by simp) with h3092 | h3092
                                        · rcases h5bigk with h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c
                                          · have p3093_0 := h3093c.1
                                            have p3093_1 := h3093c.2.1
                                            have p3093_2 := h3093c.2.2.1
                                            have p3093_3 := h3093c.2.2.2
                                            linarith only [hlam, p3093_0]
                                          · have p3093_0 := h3093c.1
                                            have p3093_1 := h3093c.2.1
                                            have p3093_2 := h3093c.2.2.1
                                            have p3093_3 := h3093c.2.2.2
                                            linarith only [h2736, hlam, p3093_1]
                                          · have p3093_0 := h3093c.1
                                            have p3093_1 := h3093c.2.1
                                            have p3093_2 := h3093c.2.2.1
                                            have p3093_3 := h3093c.2.2.2
                                            linarith only [h2319, h2843, h2845, h2846, h3038, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3093_1, u3ehi2]
                                          · have p3093_0 := h3093c.1
                                            have p3093_1 := h3093c.2.1
                                            have p3093_2 := h3093c.2.2.1
                                            have p3093_3 := h3093c.2.2.2
                                            linarith only [h2319, h2843, h2845, h2846, h3038, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3093_1, u3ehi2]
                                          · have p3093_0 := h3093c.1
                                            have p3093_1 := h3093c.2.1
                                            have p3093_2 := h3093c.2.2.1
                                            have p3093_3 := h3093c.2.2.2
                                            rcases p3093_3 (m.d 0 5) (by simp) with h3098 | h3098
                                            · rcases p3093_3 (m.d 1 5) (by simp) with h3099 | h3099
                                              · rcases p3093_3 (m.d 2 5) (by simp) with h3100 | h3100
                                                · linarith only [h2842, h3100, hlam]
                                                · linarith only [h3040, h3100, hlam]
                                              · linarith only [h2851, h3099, hlam]
                                            · linarith only [h2845, h3098, hlam]
                                          · have p3093_0 := h3093c.1
                                            have p3093_1 := h3093c.2.1
                                            have p3093_2 := h3093c.2.2.1
                                            have p3093_3 := h3093c.2.2.2
                                            linarith only [h2736, h2846, h2849, h2851, hc01, hc12, hlam, hphi, p3093_1]
                                          · have p3093_0 := h3093c.1
                                            have p3093_1 := h3093c.2.1
                                            have p3093_2 := h3093c.2.2.1
                                            have p3093_3 := h3093c.2.2.2
                                            linarith only [hlam, p3093_0]
                                          · have p3093_0 := h3093c.1
                                            have p3093_1 := h3093c.2.1
                                            have p3093_2 := h3093c.2.2.1
                                            have p3093_3 := h3093c.2.2.2
                                            linarith only [h2846, h2849, h2851, h3038, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3093_1, u3ehi2]
                                          · have p3093_0 := h3093c.1
                                            have p3093_1 := h3093c.2.1
                                            have p3093_2 := h3093c.2.2.1
                                            have p3093_3 := h3093c.2.2.2
                                            linarith only [h2846, h2849, h2851, h3038, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3093_1, u3ehi2]
                                          · have p3093_0 := h3093c.1
                                            have p3093_1 := h3093c.2.1
                                            have p3093_2 := h3093c.2.2.1
                                            have p3093_3 := h3093c.2.2.2
                                            rcases p3093_3 (m.d 0 5) (by simp) with h3109 | h3109
                                            · linarith only [h2736, h3109, hlam]
                                            · linarith only [h2845, h3109, hlam]
                                          · have p3093_0 := h3093c.1
                                            have p3093_1 := h3093c.2.1
                                            have p3093_2 := h3093c.2.2.1
                                            have p3093_3 := h3093c.2.2.2
                                            linarith only [h2842, hlam, p3093_1]
                                          · have p3093_0 := h3093c.1
                                            have p3093_1 := h3093c.2.1
                                            have p3093_2 := h3093c.2.2.1
                                            have p3093_3 := h3093c.2.2.2
                                            linarith only [h2848, hlam, p3093_1]
                                          · have p3093_0 := h3093c.1
                                            have p3093_1 := h3093c.2.1
                                            have p3093_2 := h3093c.2.2.1
                                            have p3093_3 := h3093c.2.2.2
                                            linarith only [hlam, p3093_0]
                                          · have p3093_0 := h3093c.1
                                            have p3093_1 := h3093c.2.1
                                            have p3093_2 := h3093c.2.2.1
                                            have p3093_3 := h3093c.2.2.2
                                            linarith only [h3038, hlam, p3093_1]
                                          · have p3093_0 := h3093c.1
                                            have p3093_1 := h3093c.2.1
                                            have p3093_2 := h3093c.2.2.1
                                            have p3093_3 := h3093c.2.2.2
                                            linarith only [h0, h2842, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3093_1]
                                          · have p3093_0 := h3093c.1
                                            have p3093_1 := h3093c.2.1
                                            have p3093_2 := h3093c.2.2.1
                                            have p3093_3 := h3093c.2.2.2
                                            linarith only [h2844, hlam, p3093_0]
                                          · have p3093_0 := h3093c.1
                                            have p3093_1 := h3093c.2.1
                                            have p3093_2 := h3093c.2.2.1
                                            have p3093_3 := h3093c.2.2.2
                                            linarith only [h2850, hlam, p3093_0]
                                          · have p3093_0 := h3093c.1
                                            have p3093_1 := h3093c.2.1
                                            have p3093_2 := h3093c.2.2.1
                                            have p3093_3 := h3093c.2.2.2
                                            linarith only [h2319, h2844, h2846, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p3093_1]
                                          · have p3093_0 := h3093c.1
                                            have p3093_1 := h3093c.2.1
                                            have p3093_2 := h3093c.2.2.1
                                            have p3093_3 := h3093c.2.2.2
                                            linarith only [hlam, p3093_0]
                                          · have p3093_0 := h3093c.1
                                            have p3093_1 := h3093c.2.1
                                            have p3093_2 := h3093c.2.2.1
                                            have p3093_3 := h3093c.2.2.2
                                            linarith only [h2319, h2843, h2846, h3041, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3093_1]
                                          · have p3093_0 := h3093c.1
                                            have p3093_1 := h3093c.2.1
                                            have p3093_2 := h3093c.2.2.1
                                            have p3093_3 := h3093c.2.2.2
                                            linarith only [h2845, hlam, p3093_0]
                                          · have p3093_0 := h3093c.1
                                            have p3093_1 := h3093c.2.1
                                            have p3093_2 := h3093c.2.2.1
                                            have p3093_3 := h3093c.2.2.2
                                            linarith only [h2851, hlam, p3093_0]
                                          · have p3093_0 := h3093c.1
                                            have p3093_1 := h3093c.2.1
                                            have p3093_2 := h3093c.2.2.1
                                            have p3093_3 := h3093c.2.2.2
                                            linarith only [h3040, hlam, p3093_0]
                                          · have p3093_0 := h3093c.1
                                            have p3093_1 := h3093c.2.1
                                            have p3093_2 := h3093c.2.2.1
                                            have p3093_3 := h3093c.2.2.2
                                            linarith only [h3041, hlam, p3093_0]
                                          · have p3093_0 := h3093c.1
                                            have p3093_1 := h3093c.2.1
                                            have p3093_2 := h3093c.2.2.1
                                            have p3093_3 := h3093c.2.2.2
                                            linarith only [hlam, p3093_0]
                                        · linarith only [h3092, hlam, p3042_0]
                                      · linarith only [h2512, h3091, hlam]
                                    · linarith only [h2319, h3090, hlam]
                                  · linarith only [h0, h3089, hlam]
                              · have p3042_0 := h3042c.1
                                have p3042_1 := h3042c.2.1
                                have p3042_2 := h3042c.2.2.1
                                have p3042_3 := h3042c.2.2.2
                                linarith only [h2848, hlam, p3042_1]
                              · have p3042_0 := h3042c.1
                                have p3042_1 := h3042c.2.1
                                have p3042_2 := h3042c.2.2.1
                                have p3042_3 := h3042c.2.2.2
                                linarith only [h2850, hlam, p3042_0]
                              · have p3042_0 := h3042c.1
                                have p3042_1 := h3042c.2.1
                                have p3042_2 := h3042c.2.2.1
                                have p3042_3 := h3042c.2.2.2
                                linarith only [h2851, hlam, p3042_0]
                              · have p3042_0 := h3042c.1
                                have p3042_1 := h3042c.2.1
                                have p3042_2 := h3042c.2.2.1
                                have p3042_3 := h3042c.2.2.2
                                linarith only [hlam, p3042_0]
                            · linarith only [h2319, h2843, h2845, h2846, h2852, h3041, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3136 | h3136
                            · linarith only [h2852, h3040, h3136, hc34, hlam, hphi, u3ehi2]
                            · linarith only [h2319, h2843, h2845, h2846, h2852, h3136, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h2319, h2512, h2843, h2845, h2846, h2851, hc01, hc12, hlam, hphi]
                  · linarith only [h2319, h2843, h2850, hc35, hlam, hphi, u3ehi3]
                · linarith only [h2319, h2844, h2849, hc34, hlam, hphi, u3ehi4]
              · linarith only [h0, h2842, h2848, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3143 | h3143
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3144 | h3144
                · linarith only [h2846, h2847, h3144, hlam]
                · linarith only [h0, h2841, h2843, h2847, h3144, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
              · linarith only [h0, h2842, h3143, hlam]
          · linarith only [h0, h2841, h2846, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3149 | h3149
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3150 | h3150
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3151 | h3151
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3152 | h3152
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3153 | h3153
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3154 | h3154
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3155 | h3155
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3156 | h3156
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3157 | h3157
                          · linarith only [h2841, h2843, h2845, h3155, h3157, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3159 | h3159
                            · linarith only [h2843, h2845, h3159, hlam]
                            · rcases h1bigk with h3161c | h3161c | h3161c | h3161c | h3161c | h3161c | h3161c | h3161c | h3161c | h3161c | h3161c | h3161c | h3161c | h3161c | h3161c | h3161c | h3161c | h3161c | h3161c | h3161c | h3161c | h3161c | h3161c | h3161c | h3161c
                              · have p3161_0 := h3161c.1
                                have p3161_1 := h3161c.2.1
                                have p3161_2 := h3161c.2.2.1
                                have p3161_3 := h3161c.2.2.2
                                linarith only [hlam, p3161_0]
                              · have p3161_0 := h3161c.1
                                have p3161_1 := h3161c.2.1
                                have p3161_2 := h3161c.2.2.1
                                have p3161_3 := h3161c.2.2.2
                                linarith only [h0, hlam, p3161_0]
                              · have p3161_0 := h3161c.1
                                have p3161_1 := h3161c.2.1
                                have p3161_2 := h3161c.2.2.1
                                have p3161_3 := h3161c.2.2.2
                                linarith only [h2319, hlam, p3161_0]
                              · have p3161_0 := h3161c.1
                                have p3161_1 := h3161c.2.1
                                have p3161_2 := h3161c.2.2.1
                                have p3161_3 := h3161c.2.2.2
                                linarith only [h2512, hlam, p3161_0]
                              · have p3161_0 := h3161c.1
                                have p3161_1 := h3161c.2.1
                                have p3161_2 := h3161c.2.2.1
                                have p3161_3 := h3161c.2.2.2
                                linarith only [h2736, hlam, p3161_0]
                              · have p3161_0 := h3161c.1
                                have p3161_1 := h3161c.2.1
                                have p3161_2 := h3161c.2.2.1
                                have p3161_3 := h3161c.2.2.2
                                rcases p3161_3 (m.d 0 1) (by simp) with h3167 | h3167
                                · linarith only [h3167, hlam, p3161_0]
                                · rcases p3161_3 (m.d 1 2) (by simp) with h3169 | h3169
                                  · rcases p3161_3 (m.d 1 3) (by simp) with h3170 | h3170
                                    · linarith only [h3149, h3170, hlam]
                                    · linarith only [h2319, h3170, hlam]
                                  · linarith only [h3169, hlam, p3161_0]
                              · have p3161_0 := h3161c.1
                                have p3161_1 := h3161c.2.1
                                have p3161_2 := h3161c.2.2.1
                                have p3161_3 := h3161c.2.2.2
                                linarith only [hlam, p3161_0]
                              · have p3161_0 := h3161c.1
                                have p3161_1 := h3161c.2.1
                                have p3161_2 := h3161c.2.2.1
                                have p3161_3 := h3161c.2.2.2
                                linarith only [h2843, h2845, h3152, h3154, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3161_1, u3ehi3]
                              · have p3161_0 := h3161c.1
                                have p3161_1 := h3161c.2.1
                                have p3161_2 := h3161c.2.2.1
                                have p3161_3 := h3161c.2.2.2
                                linarith only [h2843, h2845, h3154, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3161_1, u3ehi3]
                              · have p3161_0 := h3161c.1
                                have p3161_1 := h3161c.2.1
                                have p3161_2 := h3161c.2.2.1
                                have p3161_3 := h3161c.2.2.2
                                linarith only [h2843, h2845, h3154, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3161_1, u3ehi3]
                              · have p3161_0 := h3161c.1
                                have p3161_1 := h3161c.2.1
                                have p3161_2 := h3161c.2.2.1
                                have p3161_3 := h3161c.2.2.2
                                rcases p3161_3 (m.d 0 1) (by simp) with h3178 | h3178
                                · linarith only [h3178, hlam, p3161_0]
                                · rcases p3161_3 (m.d 1 2) (by simp) with h3180 | h3180
                                  · rcases p3161_3 (m.d 1 3) (by simp) with h3181 | h3181
                                    · rcases p3161_3 (m.d 1 4) (by simp) with h3182 | h3182
                                      · linarith only [h3152, h3182, hlam]
                                      · linarith only [h2512, h3182, hlam]
                                    · linarith only [h3181, hlam, p3161_0]
                                  · linarith only [h0, h3180, hlam]
                              · have p3161_0 := h3161c.1
                                have p3161_1 := h3161c.2.1
                                have p3161_2 := h3161c.2.2.1
                                have p3161_3 := h3161c.2.2.2
                                linarith only [h3149, hlam, p3161_1]
                              · have p3161_0 := h3161c.1
                                have p3161_1 := h3161c.2.1
                                have p3161_2 := h3161c.2.2.1
                                have p3161_3 := h3161c.2.2.2
                                linarith only [hlam, p3161_0]
                              · have p3161_0 := h3161c.1
                                have p3161_1 := h3161c.2.1
                                have p3161_2 := h3161c.2.2.1
                                have p3161_3 := h3161c.2.2.2
                                linarith only [h2843, h2845, h3154, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3161_1, u3ehi3]
                              · have p3161_0 := h3161c.1
                                have p3161_1 := h3161c.2.1
                                have p3161_2 := h3161c.2.2.1
                                have p3161_3 := h3161c.2.2.2
                                linarith only [h2843, h2845, h3149, h3154, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3161_1, u3ehi3]
                              · have p3161_0 := h3161c.1
                                have p3161_1 := h3161c.2.1
                                have p3161_2 := h3161c.2.2.1
                                have p3161_3 := h3161c.2.2.2
                                rcases p3161_3 (m.d 0 1) (by simp) with h3191 | h3191
                                · linarith only [h3191, hlam, p3161_0]
                                · rcases p3161_3 (m.d 1 2) (by simp) with h3193 | h3193
                                  · rcases p3161_3 (m.d 1 3) (by simp) with h3194 | h3194
                                    · rcases p3161_3 (m.d 1 4) (by simp) with h3195 | h3195
                                      · rcases p3161_3 (m.d 1 5) (by simp) with h3196 | h3196
                                        · linarith only [h3154, h3196, hlam]
                                        · linarith only [h2736, h3196, hlam]
                                      · linarith only [h3195, hlam, p3161_0]
                                    · linarith only [h2319, h3194, hlam]
                                  · linarith only [h0, h3193, hlam]
                              · have p3161_0 := h3161c.1
                                have p3161_1 := h3161c.2.1
                                have p3161_2 := h3161c.2.2.1
                                have p3161_3 := h3161c.2.2.2
                                linarith only [h3150, hlam, p3161_1]
                              · have p3161_0 := h3161c.1
                                have p3161_1 := h3161c.2.1
                                have p3161_2 := h3161c.2.2.1
                                have p3161_3 := h3161c.2.2.2
                                linarith only [h3152, hlam, p3161_0]
                              · have p3161_0 := h3161c.1
                                have p3161_1 := h3161c.2.1
                                have p3161_2 := h3161c.2.2.1
                                have p3161_3 := h3161c.2.2.2
                                linarith only [hlam, p3161_0]
                              · have p3161_0 := h3161c.1
                                have p3161_1 := h3161c.2.1
                                have p3161_2 := h3161c.2.2.1
                                have p3161_3 := h3161c.2.2.2
                                linarith only [h2843, h2845, h3154, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3161_1, u3ehi3]
                              · have p3161_0 := h3161c.1
                                have p3161_1 := h3161c.2.1
                                have p3161_2 := h3161c.2.2.1
                                have p3161_3 := h3161c.2.2.2
                                rcases p3161_3 (m.d 0 1) (by simp) with h3206 | h3206
                                · linarith only [h3206, hlam, p3161_0]
                                · rcases p3161_3 (m.d 1 2) (by simp) with h3208 | h3208
                                  · rcases p3161_3 (m.d 1 3) (by simp) with h3209 | h3209
                                    · rcases p3161_3 (m.d 1 4) (by simp) with h3210 | h3210
                                      · rcases p3161_3 (m.d 1 5) (by simp) with h3211 | h3211
                                        · rcases h5bigk with h3212c | h3212c | h3212c | h3212c | h3212c | h3212c | h3212c | h3212c | h3212c | h3212c | h3212c | h3212c | h3212c | h3212c | h3212c | h3212c | h3212c | h3212c | h3212c | h3212c | h3212c | h3212c | h3212c | h3212c | h3212c
                                          · have p3212_0 := h3212c.1
                                            have p3212_1 := h3212c.2.1
                                            have p3212_2 := h3212c.2.2.1
                                            have p3212_3 := h3212c.2.2.2
                                            linarith only [hlam, p3212_0]
                                          · have p3212_0 := h3212c.1
                                            have p3212_1 := h3212c.2.1
                                            have p3212_2 := h3212c.2.2.1
                                            have p3212_3 := h3212c.2.2.2
                                            linarith only [h2736, hlam, p3212_1]
                                          · have p3212_0 := h3212c.1
                                            have p3212_1 := h3212c.2.1
                                            have p3212_2 := h3212c.2.2.1
                                            have p3212_3 := h3212c.2.2.2
                                            linarith only [h2845, h3149, h3152, h3154, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p3212_1]
                                          · have p3212_0 := h3212c.1
                                            have p3212_1 := h3212c.2.1
                                            have p3212_2 := h3212c.2.2.1
                                            have p3212_3 := h3212c.2.2.2
                                            linarith only [h2845, h3159, hc45, hlam, hphi, ht34, p3212_1, u3ehi3]
                                          · have p3212_0 := h3212c.1
                                            have p3212_1 := h3212c.2.1
                                            have p3212_2 := h3212c.2.2.1
                                            have p3212_3 := h3212c.2.2.2
                                            linarith only [h2845, hlam, p3212_1]
                                          · have p3212_0 := h3212c.1
                                            have p3212_1 := h3212c.2.1
                                            have p3212_2 := h3212c.2.2.1
                                            have p3212_3 := h3212c.2.2.2
                                            linarith only [h2736, hc01, hc15, hlam, hphi, p3212_1]
                                          · have p3212_0 := h3212c.1
                                            have p3212_1 := h3212c.2.1
                                            have p3212_2 := h3212c.2.2.1
                                            have p3212_3 := h3212c.2.2.2
                                            linarith only [hlam, p3212_0]
                                          · have p3212_0 := h3212c.1
                                            have p3212_1 := h3212c.2.1
                                            have p3212_2 := h3212c.2.2.1
                                            have p3212_3 := h3212c.2.2.2
                                            linarith only [h3149, h3152, h3154, h3156, h3159, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3212_1, u3ehi3]
                                          · have p3212_0 := h3212c.1
                                            have p3212_1 := h3212c.2.1
                                            have p3212_2 := h3212c.2.2.1
                                            have p3212_3 := h3212c.2.2.2
                                            linarith only [h3149, h3152, h3154, h3159, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3212_1, u3ehi3]
                                          · have p3212_0 := h3212c.1
                                            have p3212_1 := h3212c.2.1
                                            have p3212_2 := h3212c.2.2.1
                                            have p3212_3 := h3212c.2.2.2
                                            linarith only [h2843, h2845, h3149, h3152, h3154, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3212_1, u3ehi3]
                                          · have p3212_0 := h3212c.1
                                            have p3212_1 := h3212c.2.1
                                            have p3212_2 := h3212c.2.2.1
                                            have p3212_3 := h3212c.2.2.2
                                            linarith only [h2842, hlam, p3212_1]
                                          · have p3212_0 := h3212c.1
                                            have p3212_1 := h3212c.2.1
                                            have p3212_2 := h3212c.2.2.1
                                            have p3212_3 := h3212c.2.2.2
                                            linarith only [h3151, hlam, p3212_1]
                                          · have p3212_0 := h3212c.1
                                            have p3212_1 := h3212c.2.1
                                            have p3212_2 := h3212c.2.2.1
                                            have p3212_3 := h3212c.2.2.2
                                            linarith only [hlam, p3212_0]
                                          · have p3212_0 := h3212c.1
                                            have p3212_1 := h3212c.2.1
                                            have p3212_2 := h3212c.2.2.1
                                            have p3212_3 := h3212c.2.2.2
                                            linarith only [h2842, h3159, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p3212_1, u3ehi3]
                                          · have p3212_0 := h3212c.1
                                            have p3212_1 := h3212c.2.1
                                            have p3212_2 := h3212c.2.2.1
                                            have p3212_3 := h3212c.2.2.2
                                            linarith only [h3157, hlam, p3212_1]
                                          · have p3212_0 := h3212c.1
                                            have p3212_1 := h3212c.2.1
                                            have p3212_2 := h3212c.2.2.1
                                            have p3212_3 := h3212c.2.2.2
                                            linarith only [h2844, hlam, p3212_0]
                                          · have p3212_0 := h3212c.1
                                            have p3212_1 := h3212c.2.1
                                            have p3212_2 := h3212c.2.2.1
                                            have p3212_3 := h3212c.2.2.2
                                            linarith only [h3153, hlam, p3212_0]
                                          · have p3212_0 := h3212c.1
                                            have p3212_1 := h3212c.2.1
                                            have p3212_2 := h3212c.2.2.1
                                            have p3212_3 := h3212c.2.2.2
                                            linarith only [h3156, hlam, p3212_0]
                                          · have p3212_0 := h3212c.1
                                            have p3212_1 := h3212c.2.1
                                            have p3212_2 := h3212c.2.2.1
                                            have p3212_3 := h3212c.2.2.2
                                            linarith only [hlam, p3212_0]
                                          · have p3212_0 := h3212c.1
                                            have p3212_1 := h3212c.2.1
                                            have p3212_2 := h3212c.2.2.1
                                            have p3212_3 := h3212c.2.2.2
                                            linarith only [h3159, hlam, p3212_1]
                                          · have p3212_0 := h3212c.1
                                            have p3212_1 := h3212c.2.1
                                            have p3212_2 := h3212c.2.2.1
                                            have p3212_3 := h3212c.2.2.2
                                            linarith only [h2736, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3212_1]
                                          · have p3212_0 := h3212c.1
                                            have p3212_1 := h3212c.2.1
                                            have p3212_2 := h3212c.2.2.1
                                            have p3212_3 := h3212c.2.2.2
                                            linarith only [h3154, hlam, p3212_0]
                                          · have p3212_0 := h3212c.1
                                            have p3212_1 := h3212c.2.1
                                            have p3212_2 := h3212c.2.2.1
                                            have p3212_3 := h3212c.2.2.2
                                            linarith only [h3149, h3152, h3154, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p3212_1]
                                          · have p3212_0 := h3212c.1
                                            have p3212_1 := h3212c.2.1
                                            have p3212_2 := h3212c.2.2.1
                                            have p3212_3 := h3212c.2.2.2
                                            linarith only [h3149, h3152, h3154, h3159, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3212_1, u3ehi3]
                                          · have p3212_0 := h3212c.1
                                            have p3212_1 := h3212c.2.1
                                            have p3212_2 := h3212c.2.2.1
                                            have p3212_3 := h3212c.2.2.2
                                            linarith only [hlam, p3212_0]
                                        · linarith only [h3211, hlam, p3161_0]
                                      · linarith only [h2512, h3210, hlam]
                                    · linarith only [h2319, h3209, hlam]
                                  · linarith only [h0, h3208, hlam]
                              · have p3161_0 := h3161c.1
                                have p3161_1 := h3161c.2.1
                                have p3161_2 := h3161c.2.2.1
                                have p3161_3 := h3161c.2.2.2
                                linarith only [h3151, hlam, p3161_1]
                              · have p3161_0 := h3161c.1
                                have p3161_1 := h3161c.2.1
                                have p3161_2 := h3161c.2.2.1
                                have p3161_3 := h3161c.2.2.2
                                linarith only [h3153, hlam, p3161_0]
                              · have p3161_0 := h3161c.1
                                have p3161_1 := h3161c.2.1
                                have p3161_2 := h3161c.2.2.1
                                have p3161_3 := h3161c.2.2.2
                                linarith only [h3154, hlam, p3161_0]
                              · have p3161_0 := h3161c.1
                                have p3161_1 := h3161c.2.1
                                have p3161_2 := h3161c.2.2.1
                                have p3161_3 := h3161c.2.2.2
                                linarith only [hlam, p3161_0]
                        · linarith only [h2844, h2845, h3149, h3152, h3154, h3155, h3156, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h2843, h2845, h3149, h3152, h3154, h3155, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3248 | h3248
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3249 | h3249
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3250 | h3250
                          · linarith only [h2843, h2845, h3150, h3250, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3252 | h3252
                            · linarith only [h2512, h3154, h3248, h3252, hc01, hc23, hlam, hphi, ht12]
                            · rcases h1bigk with h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c
                              · have p3254_0 := h3254c.1
                                have p3254_1 := h3254c.2.1
                                have p3254_2 := h3254c.2.2.1
                                have p3254_3 := h3254c.2.2.2
                                linarith only [hlam, p3254_0]
                              · have p3254_0 := h3254c.1
                                have p3254_1 := h3254c.2.1
                                have p3254_2 := h3254c.2.2.1
                                have p3254_3 := h3254c.2.2.2
                                linarith only [h0, hlam, p3254_0]
                              · have p3254_0 := h3254c.1
                                have p3254_1 := h3254c.2.1
                                have p3254_2 := h3254c.2.2.1
                                have p3254_3 := h3254c.2.2.2
                                linarith only [h2319, hlam, p3254_0]
                              · have p3254_0 := h3254c.1
                                have p3254_1 := h3254c.2.1
                                have p3254_2 := h3254c.2.2.1
                                have p3254_3 := h3254c.2.2.2
                                linarith only [h2512, hlam, p3254_0]
                              · have p3254_0 := h3254c.1
                                have p3254_1 := h3254c.2.1
                                have p3254_2 := h3254c.2.2.1
                                have p3254_3 := h3254c.2.2.2
                                linarith only [h2736, hlam, p3254_0]
                              · have p3254_0 := h3254c.1
                                have p3254_1 := h3254c.2.1
                                have p3254_2 := h3254c.2.2.1
                                have p3254_3 := h3254c.2.2.2
                                rcases p3254_3 (m.d 0 1) (by simp) with h3260 | h3260
                                · linarith only [h3260, hlam, p3254_0]
                                · rcases p3254_3 (m.d 1 2) (by simp) with h3262 | h3262
                                  · rcases p3254_3 (m.d 1 3) (by simp) with h3263 | h3263
                                    · linarith only [h3149, h3263, hlam]
                                    · linarith only [h2319, h3263, hlam]
                                  · linarith only [h3262, hlam, p3254_0]
                              · have p3254_0 := h3254c.1
                                have p3254_1 := h3254c.2.1
                                have p3254_2 := h3254c.2.2.1
                                have p3254_3 := h3254c.2.2.2
                                linarith only [hlam, p3254_0]
                              · have p3254_0 := h3254c.1
                                have p3254_1 := h3254c.2.1
                                have p3254_2 := h3254c.2.2.1
                                have p3254_3 := h3254c.2.2.2
                                linarith only [h2319, hc01, hc12, hlam, hphi, p3254_1]
                              · have p3254_0 := h3254c.1
                                have p3254_1 := h3254c.2.1
                                have p3254_2 := h3254c.2.2.1
                                have p3254_3 := h3254c.2.2.2
                                linarith only [h2512, hc01, hc12, hlam, hphi, p3254_1]
                              · have p3254_0 := h3254c.1
                                have p3254_1 := h3254c.2.1
                                have p3254_2 := h3254c.2.2.1
                                have p3254_3 := h3254c.2.2.2
                                linarith only [h2736, hc01, hc12, hlam, hphi, p3254_1]
                              · have p3254_0 := h3254c.1
                                have p3254_1 := h3254c.2.1
                                have p3254_2 := h3254c.2.2.1
                                have p3254_3 := h3254c.2.2.2
                                rcases p3254_3 (m.d 0 1) (by simp) with h3271 | h3271
                                · linarith only [h3271, hlam, p3254_0]
                                · rcases p3254_3 (m.d 1 2) (by simp) with h3273 | h3273
                                  · rcases p3254_3 (m.d 1 3) (by simp) with h3274 | h3274
                                    · rcases p3254_3 (m.d 1 4) (by simp) with h3275 | h3275
                                      · linarith only [h3152, h3275, hlam]
                                      · linarith only [h2512, h3275, hlam]
                                    · linarith only [h3274, hlam, p3254_0]
                                  · linarith only [h0, h3273, hlam]
                              · have p3254_0 := h3254c.1
                                have p3254_1 := h3254c.2.1
                                have p3254_2 := h3254c.2.2.1
                                have p3254_3 := h3254c.2.2.2
                                linarith only [h3149, hlam, p3254_1]
                              · have p3254_0 := h3254c.1
                                have p3254_1 := h3254c.2.1
                                have p3254_2 := h3254c.2.2.1
                                have p3254_3 := h3254c.2.2.2
                                linarith only [hlam, p3254_0]
                              · have p3254_0 := h3254c.1
                                have p3254_1 := h3254c.2.1
                                have p3254_2 := h3254c.2.2.1
                                have p3254_3 := h3254c.2.2.2
                                linarith only [h2512, hc01, hc13, hlam, hphi, p3254_1]
                              · have p3254_0 := h3254c.1
                                have p3254_1 := h3254c.2.1
                                have p3254_2 := h3254c.2.2.1
                                have p3254_3 := h3254c.2.2.2
                                linarith only [h2512, h3149, h3154, hc01, hc12, hlam, hphi, p3254_1]
                              · have p3254_0 := h3254c.1
                                have p3254_1 := h3254c.2.1
                                have p3254_2 := h3254c.2.2.1
                                have p3254_3 := h3254c.2.2.2
                                linarith only [h0, h2841, h3154, h3249, h3252, hc01, hc12, hc45, hlam, hphi, ht34, p3254_1, u3ehi3]
                              · have p3254_0 := h3254c.1
                                have p3254_1 := h3254c.2.1
                                have p3254_2 := h3254c.2.2.1
                                have p3254_3 := h3254c.2.2.2
                                linarith only [h3150, hlam, p3254_1]
                              · have p3254_0 := h3254c.1
                                have p3254_1 := h3254c.2.1
                                have p3254_2 := h3254c.2.2.1
                                have p3254_3 := h3254c.2.2.2
                                linarith only [h3152, hlam, p3254_0]
                              · have p3254_0 := h3254c.1
                                have p3254_1 := h3254c.2.1
                                have p3254_2 := h3254c.2.2.1
                                have p3254_3 := h3254c.2.2.2
                                linarith only [hlam, p3254_0]
                              · have p3254_0 := h3254c.1
                                have p3254_1 := h3254c.2.1
                                have p3254_2 := h3254c.2.2.1
                                have p3254_3 := h3254c.2.2.2
                                linarith only [h3154, hlam, p3254_1]
                              · have p3254_0 := h3254c.1
                                have p3254_1 := h3254c.2.1
                                have p3254_2 := h3254c.2.2.1
                                have p3254_3 := h3254c.2.2.2
                                rcases p3254_3 (m.d 0 1) (by simp) with h3289 | h3289
                                · linarith only [h3289, hlam, p3254_0]
                                · rcases p3254_3 (m.d 1 2) (by simp) with h3291 | h3291
                                  · rcases p3254_3 (m.d 1 3) (by simp) with h3292 | h3292
                                    · rcases p3254_3 (m.d 1 4) (by simp) with h3293 | h3293
                                      · linarith only [h3154, h3293, hlam]
                                      · linarith only [h2512, h3293, hlam]
                                    · linarith only [h2319, h3292, hlam]
                                  · linarith only [h0, h3291, hlam]
                              · have p3254_0 := h3254c.1
                                have p3254_1 := h3254c.2.1
                                have p3254_2 := h3254c.2.2.1
                                have p3254_3 := h3254c.2.2.2
                                linarith only [h3151, hlam, p3254_1]
                              · have p3254_0 := h3254c.1
                                have p3254_1 := h3254c.2.1
                                have p3254_2 := h3254c.2.2.1
                                have p3254_3 := h3254c.2.2.2
                                linarith only [h3153, hlam, p3254_0]
                              · have p3254_0 := h3254c.1
                                have p3254_1 := h3254c.2.1
                                have p3254_2 := h3254c.2.2.1
                                have p3254_3 := h3254c.2.2.2
                                linarith only [h2512, hc01, hc15, hlam, hphi, p3254_1]
                              · have p3254_0 := h3254c.1
                                have p3254_1 := h3254c.2.1
                                have p3254_2 := h3254c.2.2.1
                                have p3254_3 := h3254c.2.2.2
                                linarith only [hlam, p3254_0]
                        · linarith only [h2319, h2844, h3149, h3248, h3249, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h2843, h2845, h3248, hc45, hlam, hphi, ht34, u3ehi2]
                  · linarith only [h2319, h2844, h3153, hlam]
                · linarith only [h2319, h2843, h2845, h3152, hc45, hlam, hphi, ht34, u3ehi0]
              · linarith only [h0, h2842, h3151, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3307 | h3307
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3308 | h3308
                · linarith only [h3149, h3150, h3308, hlam]
                · linarith only [h2319, h2843, h3308, hlam]
              · linarith only [h0, h2842, h3307, hlam]
          · linarith only [h0, h2841, h3149, hlam]
      · linarith only [h2843, h2844, hc35, hlam, hphi, u3ehi3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3314 | h3314
      · linarith only [h2843, h3314, hc34, hlam, hphi, u3ehi4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3316 | h3316
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3317 | h3317
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3318 | h3318
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3319 | h3319
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3320 | h3320
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3321 | h3321
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3322 | h3322
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3323 | h3323
                      · linarith only [h2841, h2843, h3323, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3325 | h3325
                        · linarith only [h2841, h3314, h3325, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3327 | h3327
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3328 | h3328
                            · rcases h1bigk with h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [hlam, p3329_0]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [h0, hlam, p3329_0]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [h2319, hlam, p3329_0]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [h2512, hlam, p3329_0]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [h2736, hlam, p3329_0]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                rcases p3329_3 (m.d 0 1) (by simp) with h3335 | h3335
                                · linarith only [h3335, hlam, p3329_0]
                                · rcases p3329_3 (m.d 1 2) (by simp) with h3337 | h3337
                                  · rcases p3329_3 (m.d 1 3) (by simp) with h3338 | h3338
                                    · linarith only [h3317, h3338, hlam]
                                    · linarith only [h2319, h3338, hlam]
                                  · linarith only [h3337, hlam, p3329_0]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [hlam, p3329_0]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [h2841, h3314, h3320, h3328, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3329_1, u3ehi2]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [h2841, h3314, h3321, h3322, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3329_1, u3ehi2]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [h2841, h3314, h3321, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3329_1, u3ehi2]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                rcases p3329_3 (m.d 0 1) (by simp) with h3346 | h3346
                                · linarith only [h3346, hlam, p3329_0]
                                · rcases p3329_3 (m.d 1 2) (by simp) with h3348 | h3348
                                  · rcases p3329_3 (m.d 1 3) (by simp) with h3349 | h3349
                                    · rcases p3329_3 (m.d 1 4) (by simp) with h3350 | h3350
                                      · linarith only [h3320, h3350, hlam]
                                      · linarith only [h2512, h3350, hlam]
                                    · linarith only [h3349, hlam, p3329_0]
                                  · linarith only [h0, h3348, hlam]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [h3317, hlam, p3329_1]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [hlam, p3329_0]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [h2841, h3314, h3321, h3322, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3329_1, u3ehi2]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [h2841, h3314, h3317, h3321, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3329_1, u3ehi2]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                rcases p3329_3 (m.d 0 1) (by simp) with h3359 | h3359
                                · linarith only [h3359, hlam, p3329_0]
                                · rcases p3329_3 (m.d 1 2) (by simp) with h3361 | h3361
                                  · rcases p3329_3 (m.d 1 3) (by simp) with h3362 | h3362
                                    · rcases p3329_3 (m.d 1 4) (by simp) with h3363 | h3363
                                      · rcases p3329_3 (m.d 1 5) (by simp) with h3364 | h3364
                                        · linarith only [h3322, h3364, hlam]
                                        · linarith only [h2736, h3364, hlam]
                                      · linarith only [h3363, hlam, p3329_0]
                                    · linarith only [h2319, h3362, hlam]
                                  · linarith only [h0, h3361, hlam]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [h3318, hlam, p3329_1]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [h3320, hlam, p3329_0]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [hlam, p3329_0]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [h2841, h3314, h3321, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3329_1, u3ehi2]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                rcases p3329_3 (m.d 0 1) (by simp) with h3374 | h3374
                                · linarith only [h3374, hlam, p3329_0]
                                · rcases p3329_3 (m.d 1 2) (by simp) with h3376 | h3376
                                  · rcases p3329_3 (m.d 1 3) (by simp) with h3377 | h3377
                                    · rcases p3329_3 (m.d 1 4) (by simp) with h3378 | h3378
                                      · rcases p3329_3 (m.d 1 5) (by simp) with h3379 | h3379
                                        · rcases h5bigk with h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c
                                          · have p3380_0 := h3380c.1
                                            have p3380_1 := h3380c.2.1
                                            have p3380_2 := h3380c.2.2.1
                                            have p3380_3 := h3380c.2.2.2
                                            linarith only [hlam, p3380_0]
                                          · have p3380_0 := h3380c.1
                                            have p3380_1 := h3380c.2.1
                                            have p3380_2 := h3380c.2.2.1
                                            have p3380_3 := h3380c.2.2.2
                                            linarith only [h2736, hlam, p3380_1]
                                          · have p3380_0 := h3380c.1
                                            have p3380_1 := h3380c.2.1
                                            have p3380_2 := h3380c.2.2.1
                                            have p3380_3 := h3380c.2.2.2
                                            linarith only [h2843, h3316, h3317, h3320, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p3380_1]
                                          · have p3380_0 := h3380c.1
                                            have p3380_1 := h3380c.2.1
                                            have p3380_2 := h3380c.2.2.1
                                            have p3380_3 := h3380c.2.2.2
                                            linarith only [h3314, hlam, p3380_1]
                                          · have p3380_0 := h3380c.1
                                            have p3380_1 := h3380c.2.1
                                            have p3380_2 := h3380c.2.2.1
                                            have p3380_3 := h3380c.2.2.2
                                            linarith only [h2843, h3316, h3317, h3320, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3380_1]
                                          · have p3380_0 := h3380c.1
                                            have p3380_1 := h3380c.2.1
                                            have p3380_2 := h3380c.2.2.1
                                            have p3380_3 := h3380c.2.2.2
                                            linarith only [h2736, hc01, hc15, hlam, hphi, p3380_1]
                                          · have p3380_0 := h3380c.1
                                            have p3380_1 := h3380c.2.1
                                            have p3380_2 := h3380c.2.2.1
                                            have p3380_3 := h3380c.2.2.2
                                            linarith only [hlam, p3380_0]
                                          · have p3380_0 := h3380c.1
                                            have p3380_1 := h3380c.2.1
                                            have p3380_2 := h3380c.2.2.1
                                            have p3380_3 := h3380c.2.2.2
                                            linarith only [h3317, h3320, h3322, h3325, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3380_1, u3ehi2]
                                          · have p3380_0 := h3380c.1
                                            have p3380_1 := h3380c.2.1
                                            have p3380_2 := h3380c.2.2.1
                                            have p3380_3 := h3380c.2.2.2
                                            linarith only [h2841, h3314, h3317, h3320, h3322, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3380_1, u3ehi2]
                                          · have p3380_0 := h3380c.1
                                            have p3380_1 := h3380c.2.1
                                            have p3380_2 := h3380c.2.2.1
                                            have p3380_3 := h3380c.2.2.2
                                            rcases p3380_3 (m.d 0 5) (by simp) with h3390 | h3390
                                            · linarith only [h2736, h3390, hlam]
                                            · linarith only [h3316, h3390, hlam]
                                          · have p3380_0 := h3380c.1
                                            have p3380_1 := h3380c.2.1
                                            have p3380_2 := h3380c.2.2.1
                                            have p3380_3 := h3380c.2.2.2
                                            linarith only [h2842, hlam, p3380_1]
                                          · have p3380_0 := h3380c.1
                                            have p3380_1 := h3380c.2.1
                                            have p3380_2 := h3380c.2.2.1
                                            have p3380_3 := h3380c.2.2.2
                                            linarith only [h3319, hlam, p3380_1]
                                          · have p3380_0 := h3380c.1
                                            have p3380_1 := h3380c.2.1
                                            have p3380_2 := h3380c.2.2.1
                                            have p3380_3 := h3380c.2.2.2
                                            linarith only [hlam, p3380_0]
                                          · have p3380_0 := h3380c.1
                                            have p3380_1 := h3380c.2.1
                                            have p3380_2 := h3380c.2.2.1
                                            have p3380_3 := h3380c.2.2.2
                                            linarith only [h3325, hlam, p3380_1]
                                          · have p3380_0 := h3380c.1
                                            have p3380_1 := h3380c.2.1
                                            have p3380_2 := h3380c.2.2.1
                                            have p3380_3 := h3380c.2.2.2
                                            linarith only [h0, h2842, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3380_1]
                                          · have p3380_0 := h3380c.1
                                            have p3380_1 := h3380c.2.1
                                            have p3380_2 := h3380c.2.2.1
                                            have p3380_3 := h3380c.2.2.2
                                            linarith only [h2736, hc01, hc35, hlam, hphi, ht12, ht23, p3380_1]
                                          · have p3380_0 := h3380c.1
                                            have p3380_1 := h3380c.2.1
                                            have p3380_2 := h3380c.2.2.1
                                            have p3380_3 := h3380c.2.2.2
                                            linarith only [h3321, hlam, p3380_0]
                                          · have p3380_0 := h3380c.1
                                            have p3380_1 := h3380c.2.1
                                            have p3380_2 := h3380c.2.2.1
                                            have p3380_3 := h3380c.2.2.2
                                            linarith only [h3317, h3321, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p3380_1]
                                          · have p3380_0 := h3380c.1
                                            have p3380_1 := h3380c.2.1
                                            have p3380_2 := h3380c.2.2.1
                                            have p3380_3 := h3380c.2.2.2
                                            linarith only [hlam, p3380_0]
                                          · have p3380_0 := h3380c.1
                                            have p3380_1 := h3380c.2.1
                                            have p3380_2 := h3380c.2.2.1
                                            have p3380_3 := h3380c.2.2.2
                                            linarith only [h3317, h3320, h3328, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3380_1]
                                          · have p3380_0 := h3380c.1
                                            have p3380_1 := h3380c.2.1
                                            have p3380_2 := h3380c.2.2.1
                                            have p3380_3 := h3380c.2.2.2
                                            linarith only [h3316, hlam, p3380_0]
                                          · have p3380_0 := h3380c.1
                                            have p3380_1 := h3380c.2.1
                                            have p3380_2 := h3380c.2.2.1
                                            have p3380_3 := h3380c.2.2.2
                                            linarith only [h3322, hlam, p3380_0]
                                          · have p3380_0 := h3380c.1
                                            have p3380_1 := h3380c.2.1
                                            have p3380_2 := h3380c.2.2.1
                                            have p3380_3 := h3380c.2.2.2
                                            linarith only [h3327, hlam, p3380_0]
                                          · have p3380_0 := h3380c.1
                                            have p3380_1 := h3380c.2.1
                                            have p3380_2 := h3380c.2.2.1
                                            have p3380_3 := h3380c.2.2.2
                                            linarith only [h3328, hlam, p3380_0]
                                          · have p3380_0 := h3380c.1
                                            have p3380_1 := h3380c.2.1
                                            have p3380_2 := h3380c.2.2.1
                                            have p3380_3 := h3380c.2.2.2
                                            linarith only [hlam, p3380_0]
                                        · linarith only [h3379, hlam, p3329_0]
                                      · linarith only [h2512, h3378, hlam]
                                    · linarith only [h2319, h3377, hlam]
                                  · linarith only [h0, h3376, hlam]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [h3319, hlam, p3329_1]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [h3321, hlam, p3329_0]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [h3322, hlam, p3329_0]
                              · have p3329_0 := h3329c.1
                                have p3329_1 := h3329c.2.1
                                have p3329_2 := h3329c.2.2.1
                                have p3329_3 := h3329c.2.2.2
                                linarith only [hlam, p3329_0]
                            · linarith only [h2841, h2843, h3328, hc45, hlam, hphi, ht34, u3ehi2]
                          · linarith only [h2843, h3316, h3323, h3327, hc34, hlam, hphi, u3ehi2]
                    · linarith only [h2512, h3316, h3322, hlam]
                  · linarith only [h3320, h3321, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3420 | h3420
                  · linarith only [h3320, h3420, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3422 | h3422
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3423 | h3423
                      · linarith only [h2841, h3320, h3423, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3425 | h3425
                        · linarith only [h2319, h2841, h3420, h3425, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3427 | h3427
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3428 | h3428
                            · rcases h1bigk with h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c
                              · have p3429_0 := h3429c.1
                                have p3429_1 := h3429c.2.1
                                have p3429_2 := h3429c.2.2.1
                                have p3429_3 := h3429c.2.2.2
                                linarith only [hlam, p3429_0]
                              · have p3429_0 := h3429c.1
                                have p3429_1 := h3429c.2.1
                                have p3429_2 := h3429c.2.2.1
                                have p3429_3 := h3429c.2.2.2
                                linarith only [h0, hlam, p3429_0]
                              · have p3429_0 := h3429c.1
                                have p3429_1 := h3429c.2.1
                                have p3429_2 := h3429c.2.2.1
                                have p3429_3 := h3429c.2.2.2
                                linarith only [h2319, hlam, p3429_0]
                              · have p3429_0 := h3429c.1
                                have p3429_1 := h3429c.2.1
                                have p3429_2 := h3429c.2.2.1
                                have p3429_3 := h3429c.2.2.2
                                linarith only [h2512, hlam, p3429_0]
                              · have p3429_0 := h3429c.1
                                have p3429_1 := h3429c.2.1
                                have p3429_2 := h3429c.2.2.1
                                have p3429_3 := h3429c.2.2.2
                                linarith only [h2736, hlam, p3429_0]
                              · have p3429_0 := h3429c.1
                                have p3429_1 := h3429c.2.1
                                have p3429_2 := h3429c.2.2.1
                                have p3429_3 := h3429c.2.2.2
                                rcases p3429_3 (m.d 0 1) (by simp) with h3435 | h3435
                                · linarith only [h3435, hlam, p3429_0]
                                · rcases p3429_3 (m.d 1 2) (by simp) with h3437 | h3437
                                  · rcases p3429_3 (m.d 1 3) (by simp) with h3438 | h3438
                                    · linarith only [h3317, h3438, hlam]
                                    · linarith only [h2319, h3438, hlam]
                                  · linarith only [h3437, hlam, p3429_0]
                              · have p3429_0 := h3429c.1
                                have p3429_1 := h3429c.2.1
                                have p3429_2 := h3429c.2.2.1
                                have p3429_3 := h3429c.2.2.2
                                linarith only [hlam, p3429_0]
                              · have p3429_0 := h3429c.1
                                have p3429_1 := h3429c.2.1
                                have p3429_2 := h3429c.2.2.1
                                have p3429_3 := h3429c.2.2.2
                                linarith only [h2319, hc01, hc12, hlam, hphi, p3429_1]
                              · have p3429_0 := h3429c.1
                                have p3429_1 := h3429c.2.1
                                have p3429_2 := h3429c.2.2.1
                                have p3429_3 := h3429c.2.2.2
                                linarith only [h2512, hc01, hc12, hlam, hphi, p3429_1]
                              · have p3429_0 := h3429c.1
                                have p3429_1 := h3429c.2.1
                                have p3429_2 := h3429c.2.2.1
                                have p3429_3 := h3429c.2.2.2
                                linarith only [h2736, hc01, hc12, hlam, hphi, p3429_1]
                              · have p3429_0 := h3429c.1
                                have p3429_1 := h3429c.2.1
                                have p3429_2 := h3429c.2.2.1
                                have p3429_3 := h3429c.2.2.2
                                linarith only [h3320, hc01, hc34, hlam, hphi, ht12, ht23, p3429_1]
                              · have p3429_0 := h3429c.1
                                have p3429_1 := h3429c.2.1
                                have p3429_2 := h3429c.2.2.1
                                have p3429_3 := h3429c.2.2.2
                                linarith only [h3317, hlam, p3429_1]
                              · have p3429_0 := h3429c.1
                                have p3429_1 := h3429c.2.1
                                have p3429_2 := h3429c.2.2.1
                                have p3429_3 := h3429c.2.2.2
                                linarith only [hlam, p3429_0]
                              · have p3429_0 := h3429c.1
                                have p3429_1 := h3429c.2.1
                                have p3429_2 := h3429c.2.2.1
                                have p3429_3 := h3429c.2.2.2
                                linarith only [h3320, hlam, p3429_1]
                              · have p3429_0 := h3429c.1
                                have p3429_1 := h3429c.2.1
                                have p3429_2 := h3429c.2.2.1
                                have p3429_3 := h3429c.2.2.2
                                linarith only [h3420, hlam, p3429_1]
                              · have p3429_0 := h3429c.1
                                have p3429_1 := h3429c.2.1
                                have p3429_2 := h3429c.2.2.1
                                have p3429_3 := h3429c.2.2.2
                                rcases p3429_3 (m.d 0 1) (by simp) with h3451 | h3451
                                · linarith only [h3451, hlam, p3429_0]
                                · rcases p3429_3 (m.d 1 2) (by simp) with h3453 | h3453
                                  · rcases p3429_3 (m.d 1 3) (by simp) with h3454 | h3454
                                    · linarith only [h3320, h3454, hlam]
                                    · linarith only [h2319, h3454, hlam]
                                  · linarith only [h0, h3453, hlam]
                              · have p3429_0 := h3429c.1
                                have p3429_1 := h3429c.2.1
                                have p3429_2 := h3429c.2.2.1
                                have p3429_3 := h3429c.2.2.2
                                linarith only [h3318, hlam, p3429_1]
                              · have p3429_0 := h3429c.1
                                have p3429_1 := h3429c.2.1
                                have p3429_2 := h3429c.2.2.1
                                have p3429_3 := h3429c.2.2.2
                                linarith only [h2319, hc01, hc14, hlam, hphi, p3429_1]
                              · have p3429_0 := h3429c.1
                                have p3429_1 := h3429c.2.1
                                have p3429_2 := h3429c.2.2.1
                                have p3429_3 := h3429c.2.2.2
                                linarith only [hlam, p3429_0]
                              · have p3429_0 := h3429c.1
                                have p3429_1 := h3429c.2.1
                                have p3429_2 := h3429c.2.2.1
                                have p3429_3 := h3429c.2.2.2
                                linarith only [h2736, h2841, h3314, h3320, hc34, hlam, hphi, p3429_1, u3ehi2]
                              · have p3429_0 := h3429c.1
                                have p3429_1 := h3429c.2.1
                                have p3429_2 := h3429c.2.2.1
                                have p3429_3 := h3429c.2.2.2
                                rcases p3429_3 (m.d 0 1) (by simp) with h3462 | h3462
                                · linarith only [h3462, hlam, p3429_0]
                                · rcases p3429_3 (m.d 1 2) (by simp) with h3464 | h3464
                                  · rcases p3429_3 (m.d 1 3) (by simp) with h3465 | h3465
                                    · linarith only [h3420, h3465, hlam]
                                    · linarith only [h2319, h3465, hlam]
                                  · linarith only [h0, h3464, hlam]
                              · have p3429_0 := h3429c.1
                                have p3429_1 := h3429c.2.1
                                have p3429_2 := h3429c.2.2.1
                                have p3429_3 := h3429c.2.2.2
                                linarith only [h3319, hlam, p3429_1]
                              · have p3429_0 := h3429c.1
                                have p3429_1 := h3429c.2.1
                                have p3429_2 := h3429c.2.2.1
                                have p3429_3 := h3429c.2.2.2
                                linarith only [h2319, hc01, hc15, hlam, hphi, p3429_1]
                              · have p3429_0 := h3429c.1
                                have p3429_1 := h3429c.2.1
                                have p3429_2 := h3429c.2.2.1
                                have p3429_3 := h3429c.2.2.2
                                linarith only [h3422, hlam, p3429_0]
                              · have p3429_0 := h3429c.1
                                have p3429_1 := h3429c.2.1
                                have p3429_2 := h3429c.2.2.1
                                have p3429_3 := h3429c.2.2.2
                                linarith only [hlam, p3429_0]
                            · linarith only [h0, h2512, h2842, h3320, h3427, h3428, hc01, hc12, hlam, hphi]
                          · linarith only [h2512, h3316, h3320, h3423, h3427, hc34, hlam, hphi, u3ehi2]
                    · linarith only [h2512, h3316, h3422, hlam]
              · linarith only [h0, h2842, h3319, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3477 | h3477
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3478 | h3478
                · linarith only [h2841, h2843, h3317, h3318, h3478, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3480 | h3480
                  · linarith only [h3478, h3480, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3482 | h3482
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3483 | h3483
                      · linarith only [h2319, h3478, h3483, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h2841, h3318, h3483, hc34, hlam, hphi, u3ehi2]
                    · linarith only [h2512, h3316, h3482, hlam]
              · linarith only [h0, h2842, h3477, hlam]
          · linarith only [h0, h2841, h3317, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3489 | h3489
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3490 | h3490
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3491 | h3491
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3492 | h3492
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3493 | h3493
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3494 | h3494
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3495 | h3495
                      · linarith only [h2841, h2843, h3495, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3497 | h3497
                        · linarith only [h2841, h3314, h3497, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3499 | h3499
                          · linarith only [h2841, h2843, h3316, h3495, h3499, hc34, hlam, hphi, u3ehi2]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3501 | h3501
                            · linarith only [h2841, h2843, h3316, h3489, h3492, h3501, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · linarith only [h2841, h2843, h3501, hc45, hlam, hphi, ht34, u3ehi2]
                    · linarith only [h2841, h2843, h3492, h3494, hc45, hlam, hphi, ht34, u3ehi2]
                  · linarith only [h2841, h2843, h3492, h3493, hc35, hlam, hphi, u3ehi2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3506 | h3506
                  · linarith only [h3492, h3506, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3508 | h3508
                    · linarith only [h2841, h2843, h3316, h3492, h3508, hc34, hlam, hphi, u3ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3510 | h3510
                      · linarith only [h2319, h2841, h3492, h3508, h3510, hc45, hlam, hphi, ht34, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3512 | h3512
                        · linarith only [h2319, h2841, h3492, h3508, h3512, hc45, hlam, hphi, ht34, u3ehi4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3514 | h3514
                          · linarith only [h2319, h3492, h3508, h3514, hc01, hc24, hlam, hphi, ht12]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3516 | h3516
                            · linarith only [h2319, h3492, h3508, h3516, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h2843, h3516, hc45, hlam, hphi, ht34, u3ehi0]
              · linarith only [h0, h2842, h3491, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3520 | h3520
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3521 | h3521
                · linarith only [h2841, h2843, h3489, h3490, h3521, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3523 | h3523
                  · linarith only [h3521, h3523, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3525 | h3525
                    · linarith only [h2841, h2843, h3316, h3521, h3525, hc34, hlam, hphi, u3ehi2]
                    · linarith only [h0, h2841, h3490, h3525, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h0, h2842, h3520, hlam]
          · linarith only [h0, h2841, h3489, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3530 | h3530
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3531 | h3531
      · linarith only [h2841, h2842, h3531, hlam]
      · linarith only [h3530, h3531, hc35, hlam, hphi, u3ehi3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3534 | h3534
      · linarith only [h3530, h3534, hc34, hlam, hphi, u3ehi4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3536 | h3536
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3537 | h3537
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3538 | h3538
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3539 | h3539
              · linarith only [h2841, h2842, h3539, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3541 | h3541
                · linarith only [h2841, h2842, h3530, h3536, h3537, h3539, h3541, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3543 | h3543
                  · linarith only [h2841, h2842, h3534, h3541, h3543, hc34, hlam, hphi, u3ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3545 | h3545
                    · linarith only [h3538, h3539, h3545, hlam]
                    · linarith only [h2512, h3536, h3545, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3548 | h3548
              · linarith only [h2841, h2842, h3548, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3550 | h3550
                · linarith only [h2841, h3530, h3537, h3538, h3550, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3552 | h3552
                  · linarith only [h3550, h3552, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3554 | h3554
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3555 | h3555
                      · linarith only [h2841, h3550, h3555, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h0, h2841, h3538, h3555, hc34, hlam, hphi, u3ehi2]
                    · linarith only [h2512, h3536, h3554, hlam]
          · linarith only [h0, h2841, h3537, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3560 | h3560
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3561 | h3561
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3562 | h3562
              · linarith only [h2841, h2842, h3562, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3564 | h3564
                · linarith only [h2841, h3530, h3560, h3562, h3564, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3566 | h3566
                  · linarith only [h2841, h2842, h3534, h3560, h3562, h3566, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3568 | h3568
                    · linarith only [h2512, h3536, h3561, h3562, h3568, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3570 | h3570
                      · linarith only [h0, h2841, h3562, h3570, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3572 | h3572
                        · linarith only [h0, h2841, h3562, h3566, h3572, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                        · linarith only [h0, h2841, h3562, h3572, hc35, hlam, hphi, u3ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3575 | h3575
              · linarith only [h2841, h2842, h3561, h3575, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3577 | h3577
                · linarith only [h2841, h3530, h3560, h3561, h3577, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3579 | h3579
                  · linarith only [h3577, h3579, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3581 | h3581
                    · linarith only [h2841, h3530, h3536, h3577, h3581, hc34, hlam, hphi, u3ehi2]
                    · linarith only [h0, h2841, h3561, h3581, hc45, hlam, hphi, ht34, u3ehi2]
          · linarith only [h0, h2841, h3560, hlam]

end R2N4
