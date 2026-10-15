import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7634000 in
theorem r1l7_10_12_13_25_L_0_L_I_L_I_M_IR_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1494 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2055 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h2897 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h5ehi := hb5.2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h2898 | h2898
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2899 | h2899
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2900 | h2900
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2901 | h2901
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2902 | h2902
          · linarith only [h2055, h2897, h2901, h2902, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2904 | h2904
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2905 | h2905
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2906 | h2906
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2907 | h2907
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2908 | h2908
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2909 | h2909
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2910 | h2910
                        · linarith only [h2897, h2910, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2912 | h2912
                          · linarith only [h2908, h2910, h2912, hlam]
                          · rcases h2bigk with h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c
                            · have p2914_0 := h2914c.1
                              have p2914_1 := h2914c.2.1
                              have p2914_2 := h2914c.2.2.1
                              have p2914_3 := h2914c.2.2.2
                              linarith only [hlam, p2914_0]
                            · have p2914_0 := h2914c.1
                              have p2914_1 := h2914c.2.1
                              have p2914_2 := h2914c.2.2.1
                              have p2914_3 := h2914c.2.2.2
                              linarith only [h0, hlam, p2914_1]
                            · have p2914_0 := h2914c.1
                              have p2914_1 := h2914c.2.1
                              have p2914_2 := h2914c.2.2.1
                              have p2914_3 := h2914c.2.2.2
                              linarith only [h2055, hlam, p2914_0]
                            · have p2914_0 := h2914c.1
                              have p2914_1 := h2914c.2.1
                              have p2914_2 := h2914c.2.2.1
                              have p2914_3 := h2914c.2.2.2
                              rcases p2914_3 (m.d 0 2) (by simp) with h2918 | h2918
                              · rcases p2914_3 (m.d 1 2) (by simp) with h2919 | h2919
                                · rcases p2914_3 (m.d 2 3) (by simp) with h2920 | h2920
                                  · rcases p2914_3 (m.d 2 4) (by simp) with h2921 | h2921
                                    · linarith only [h2921, hlam, p2914_0]
                                    · rcases p2914_3 (m.d 2 5) (by simp) with h2923 | h2923
                                      · linarith only [h2898, h2923, hlam]
                                      · linarith only [h2910, h2923, hlam]
                                  · linarith only [h2908, h2920, hlam]
                                · linarith only [h2904, h2919, hlam]
                              · linarith only [h2918, hlam, p2914_0]
                            · have p2914_0 := h2914c.1
                              have p2914_1 := h2914c.2.1
                              have p2914_2 := h2914c.2.2.1
                              have p2914_3 := h2914c.2.2.2
                              linarith only [h0, h2902, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2914_1, u5ehi2]
                            · have p2914_0 := h2914c.1
                              have p2914_1 := h2914c.2.1
                              have p2914_2 := h2914c.2.2.1
                              have p2914_3 := h2914c.2.2.2
                              linarith only [h2897, h2901, h2902, h2908, h2910, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2914_1]
                            · have p2914_0 := h2914c.1
                              have p2914_1 := h2914c.2.1
                              have p2914_2 := h2914c.2.2.1
                              have p2914_3 := h2914c.2.2.2
                              linarith only [hlam, p2914_0]
                            · have p2914_0 := h2914c.1
                              have p2914_1 := h2914c.2.1
                              have p2914_2 := h2914c.2.2.1
                              have p2914_3 := h2914c.2.2.2
                              linarith only [h2902, hlam, p2914_0]
                            · have p2914_0 := h2914c.1
                              have p2914_1 := h2914c.2.1
                              have p2914_2 := h2914c.2.2.1
                              have p2914_3 := h2914c.2.2.2
                              rcases p2914_3 (m.d 0 2) (by simp) with h2933 | h2933
                              · linarith only [h0, h2933, hlam]
                              · linarith only [h2897, h2933, hlam]
                            · have p2914_0 := h2914c.1
                              have p2914_1 := h2914c.2.1
                              have p2914_2 := h2914c.2.2.1
                              have p2914_3 := h2914c.2.2.2
                              linarith only [h2902, h2909, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2914_1, u5ehi3]
                            · have p2914_0 := h2914c.1
                              have p2914_1 := h2914c.2.1
                              have p2914_2 := h2914c.2.2.1
                              have p2914_3 := h2914c.2.2.2
                              linarith only [h2897, h2901, h2908, h2910, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2914_1]
                            · have p2914_0 := h2914c.1
                              have p2914_1 := h2914c.2.1
                              have p2914_2 := h2914c.2.2.1
                              have p2914_3 := h2914c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p2914_1]
                            · have p2914_0 := h2914c.1
                              have p2914_1 := h2914c.2.1
                              have p2914_2 := h2914c.2.2.1
                              have p2914_3 := h2914c.2.2.2
                              linarith only [hlam, p2914_0]
                            · have p2914_0 := h2914c.1
                              have p2914_1 := h2914c.2.1
                              have p2914_2 := h2914c.2.2.1
                              have p2914_3 := h2914c.2.2.2
                              linarith only [h2055, h2897, h2901, h2910, hlam, p2914_2]
                            · have p2914_0 := h2914c.1
                              have p2914_1 := h2914c.2.1
                              have p2914_2 := h2914c.2.2.1
                              have p2914_3 := h2914c.2.2.2
                              rcases p2914_3 (m.d 0 2) (by simp) with h2941 | h2941
                              · linarith only [h2055, h2941, hlam]
                              · linarith only [h2898, h2941, hlam]
                            · have p2914_0 := h2914c.1
                              have p2914_1 := h2914c.2.1
                              have p2914_2 := h2914c.2.2.1
                              have p2914_3 := h2914c.2.2.2
                              linarith only [h2897, hlam, p2914_0]
                            · have p2914_0 := h2914c.1
                              have p2914_1 := h2914c.2.1
                              have p2914_2 := h2914c.2.2.1
                              have p2914_3 := h2914c.2.2.2
                              linarith only [h2904, hlam, p2914_0]
                            · have p2914_0 := h2914c.1
                              have p2914_1 := h2914c.2.1
                              have p2914_2 := h2914c.2.2.1
                              have p2914_3 := h2914c.2.2.2
                              linarith only [h2908, hlam, p2914_1]
                            · have p2914_0 := h2914c.1
                              have p2914_1 := h2914c.2.1
                              have p2914_2 := h2914c.2.2.1
                              have p2914_3 := h2914c.2.2.2
                              linarith only [hlam, p2914_0]
                            · have p2914_0 := h2914c.1
                              have p2914_1 := h2914c.2.1
                              have p2914_2 := h2914c.2.2.1
                              have p2914_3 := h2914c.2.2.2
                              linarith only [h2910, hlam, p2914_1]
                            · have p2914_0 := h2914c.1
                              have p2914_1 := h2914c.2.1
                              have p2914_2 := h2914c.2.2.1
                              have p2914_3 := h2914c.2.2.2
                              linarith only [h2898, hlam, p2914_0]
                            · have p2914_0 := h2914c.1
                              have p2914_1 := h2914c.2.1
                              have p2914_2 := h2914c.2.2.1
                              have p2914_3 := h2914c.2.2.2
                              linarith only [h2905, hlam, p2914_0]
                            · have p2914_0 := h2914c.1
                              have p2914_1 := h2914c.2.1
                              have p2914_2 := h2914c.2.2.1
                              have p2914_3 := h2914c.2.2.2
                              linarith only [h2909, hlam, p2914_1]
                            · have p2914_0 := h2914c.1
                              have p2914_1 := h2914c.2.1
                              have p2914_2 := h2914c.2.2.1
                              have p2914_3 := h2914c.2.2.2
                              linarith only [h2898, h2908, hc34, hlam, hphi, ht0b, ht45, ht5b, p2914_1, u0elo1]
                            · have p2914_0 := h2914c.1
                              have p2914_1 := h2914c.2.1
                              have p2914_2 := h2914c.2.2.1
                              have p2914_3 := h2914c.2.2.2
                              linarith only [hlam, p2914_0]
                      · linarith only [h0, h2898, h2902, h2909, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h0, h2897, h2901, h2902, h2908, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                  · linarith only [h1494, h2900, h2907, hlam]
                · linarith only [h1494, h2899, h2906, hlam]
              · linarith only [h0, h2898, h2905, hlam]
            · linarith only [h0, h2897, h2904, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2960 | h2960
          · linarith only [h2055, h2898, h2960, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2962 | h2962
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2963 | h2963
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2964 | h2964
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2965 | h2965
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2966 | h2966
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2967 | h2967
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2968 | h2968
                        · linarith only [h2897, h2901, h2968, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2970 | h2970
                          · linarith only [h2897, h2901, h2966, h2970, hlam]
                          · rcases h2bigk with h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c | h2972c
                            · have p2972_0 := h2972c.1
                              have p2972_1 := h2972c.2.1
                              have p2972_2 := h2972c.2.2.1
                              have p2972_3 := h2972c.2.2.2
                              linarith only [hlam, p2972_0]
                            · have p2972_0 := h2972c.1
                              have p2972_1 := h2972c.2.1
                              have p2972_2 := h2972c.2.2.1
                              have p2972_3 := h2972c.2.2.2
                              linarith only [h0, hlam, p2972_1]
                            · have p2972_0 := h2972c.1
                              have p2972_1 := h2972c.2.1
                              have p2972_2 := h2972c.2.2.1
                              have p2972_3 := h2972c.2.2.2
                              linarith only [h2055, hlam, p2972_0]
                            · have p2972_0 := h2972c.1
                              have p2972_1 := h2972c.2.1
                              have p2972_2 := h2972c.2.2.1
                              have p2972_3 := h2972c.2.2.2
                              rcases p2972_3 (m.d 0 2) (by simp) with h2976 | h2976
                              · rcases p2972_3 (m.d 1 2) (by simp) with h2977 | h2977
                                · rcases p2972_3 (m.d 2 3) (by simp) with h2978 | h2978
                                  · rcases p2972_3 (m.d 2 4) (by simp) with h2979 | h2979
                                    · linarith only [h2979, hlam, p2972_0]
                                    · rcases p2972_3 (m.d 2 5) (by simp) with h2981 | h2981
                                      · linarith only [h2898, h2981, hlam]
                                      · linarith only [h2968, h2981, hlam]
                                  · linarith only [h2966, h2978, hlam]
                                · linarith only [h2962, h2977, hlam]
                              · linarith only [h2976, hlam, p2972_0]
                            · have p2972_0 := h2972c.1
                              have p2972_1 := h2972c.2.1
                              have p2972_2 := h2972c.2.2.1
                              have p2972_3 := h2972c.2.2.2
                              linarith only [h0, h2960, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2972_1, u5ehi2]
                            · have p2972_0 := h2972c.1
                              have p2972_1 := h2972c.2.1
                              have p2972_2 := h2972c.2.2.1
                              have p2972_3 := h2972c.2.2.2
                              linarith only [h2960, hc02, hc23, hlam, hphi, p2972_1]
                            · have p2972_0 := h2972c.1
                              have p2972_1 := h2972c.2.1
                              have p2972_2 := h2972c.2.2.1
                              have p2972_3 := h2972c.2.2.2
                              linarith only [hlam, p2972_0]
                            · have p2972_0 := h2972c.1
                              have p2972_1 := h2972c.2.1
                              have p2972_2 := h2972c.2.2.1
                              have p2972_3 := h2972c.2.2.2
                              linarith only [h2960, hlam, p2972_0]
                            · have p2972_0 := h2972c.1
                              have p2972_1 := h2972c.2.1
                              have p2972_2 := h2972c.2.2.1
                              have p2972_3 := h2972c.2.2.2
                              rcases p2972_3 (m.d 0 2) (by simp) with h2991 | h2991
                              · linarith only [h0, h2991, hlam]
                              · linarith only [h2897, h2991, hlam]
                            · have p2972_0 := h2972c.1
                              have p2972_1 := h2972c.2.1
                              have p2972_2 := h2972c.2.2.1
                              have p2972_3 := h2972c.2.2.2
                              linarith only [h2960, h2967, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2972_1, u5ehi3]
                            · have p2972_0 := h2972c.1
                              have p2972_1 := h2972c.2.1
                              have p2972_2 := h2972c.2.2.1
                              have p2972_3 := h2972c.2.2.2
                              linarith only [h2898, h2967, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2972_1, u5ehi3]
                            · have p2972_0 := h2972c.1
                              have p2972_1 := h2972c.2.1
                              have p2972_2 := h2972c.2.2.1
                              have p2972_3 := h2972c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p2972_1]
                            · have p2972_0 := h2972c.1
                              have p2972_1 := h2972c.2.1
                              have p2972_2 := h2972c.2.2.1
                              have p2972_3 := h2972c.2.2.2
                              linarith only [hlam, p2972_0]
                            · have p2972_0 := h2972c.1
                              have p2972_1 := h2972c.2.1
                              have p2972_2 := h2972c.2.2.1
                              have p2972_3 := h2972c.2.2.2
                              rcases p2972_3 (m.d 0 2) (by simp) with h2998 | h2998
                              · linarith only [h2055, h2998, hlam]
                              · linarith only [h2897, h2998, hlam]
                            · have p2972_0 := h2972c.1
                              have p2972_1 := h2972c.2.1
                              have p2972_2 := h2972c.2.2.1
                              have p2972_3 := h2972c.2.2.2
                              rcases p2972_3 (m.d 0 2) (by simp) with h3001 | h3001
                              · linarith only [h2055, h3001, hlam]
                              · linarith only [h2898, h3001, hlam]
                            · have p2972_0 := h2972c.1
                              have p2972_1 := h2972c.2.1
                              have p2972_2 := h2972c.2.2.1
                              have p2972_3 := h2972c.2.2.2
                              linarith only [h2897, hlam, p2972_0]
                            · have p2972_0 := h2972c.1
                              have p2972_1 := h2972c.2.1
                              have p2972_2 := h2972c.2.2.1
                              have p2972_3 := h2972c.2.2.2
                              linarith only [h2962, hlam, p2972_0]
                            · have p2972_0 := h2972c.1
                              have p2972_1 := h2972c.2.1
                              have p2972_2 := h2972c.2.2.1
                              have p2972_3 := h2972c.2.2.2
                              linarith only [h2966, hlam, p2972_1]
                            · have p2972_0 := h2972c.1
                              have p2972_1 := h2972c.2.1
                              have p2972_2 := h2972c.2.2.1
                              have p2972_3 := h2972c.2.2.2
                              linarith only [hlam, p2972_0]
                            · have p2972_0 := h2972c.1
                              have p2972_1 := h2972c.2.1
                              have p2972_2 := h2972c.2.2.1
                              have p2972_3 := h2972c.2.2.2
                              linarith only [h2968, hlam, p2972_1]
                            · have p2972_0 := h2972c.1
                              have p2972_1 := h2972c.2.1
                              have p2972_2 := h2972c.2.2.1
                              have p2972_3 := h2972c.2.2.2
                              linarith only [h2898, hlam, p2972_0]
                            · have p2972_0 := h2972c.1
                              have p2972_1 := h2972c.2.1
                              have p2972_2 := h2972c.2.2.1
                              have p2972_3 := h2972c.2.2.2
                              linarith only [h2963, hlam, p2972_0]
                            · have p2972_0 := h2972c.1
                              have p2972_1 := h2972c.2.1
                              have p2972_2 := h2972c.2.2.1
                              have p2972_3 := h2972c.2.2.2
                              linarith only [h2967, hlam, p2972_1]
                            · have p2972_0 := h2972c.1
                              have p2972_1 := h2972c.2.1
                              have p2972_2 := h2972c.2.2.1
                              have p2972_3 := h2972c.2.2.2
                              linarith only [h2898, hc24, hlam, hphi, ht0b, ht45, ht5b, p2972_1, u0elo1]
                            · have p2972_0 := h2972c.1
                              have p2972_1 := h2972c.2.1
                              have p2972_2 := h2972c.2.2.1
                              have p2972_3 := h2972c.2.2.2
                              linarith only [hlam, p2972_0]
                      · linarith only [h0, h2898, h2960, h2967, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h0, h2898, h2960, h2966, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                  · linarith only [h1494, h2900, h2965, hlam]
                · linarith only [h1494, h2898, h2899, h2900, h2901, h2964, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
              · linarith only [h0, h2898, h2963, hlam]
            · linarith only [h0, h2897, h2962, hlam]
      · linarith only [h2055, h2898, h2900, hlam]
    · linarith only [h2055, h2897, h2899, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3022 | h3022
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3023 | h3023
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3024 | h3024
        · linarith only [h2897, h2898, h3024, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3026 | h3026
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3027 | h3027
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3028 | h3028
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3029 | h3029
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3030 | h3030
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3031 | h3031
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3032 | h3032
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3033 | h3033
                        · linarith only [h2897, h3024, h3033, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3035 | h3035
                          · linarith only [h2897, h2898, h3031, h3033, h3035, hlam]
                          · rcases h2bigk with h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c
                            · have p3037_0 := h3037c.1
                              have p3037_1 := h3037c.2.1
                              have p3037_2 := h3037c.2.2.1
                              have p3037_3 := h3037c.2.2.2
                              linarith only [hlam, p3037_0]
                            · have p3037_0 := h3037c.1
                              have p3037_1 := h3037c.2.1
                              have p3037_2 := h3037c.2.2.1
                              have p3037_3 := h3037c.2.2.2
                              linarith only [h0, hlam, p3037_1]
                            · have p3037_0 := h3037c.1
                              have p3037_1 := h3037c.2.1
                              have p3037_2 := h3037c.2.2.1
                              have p3037_3 := h3037c.2.2.2
                              linarith only [h2055, hlam, p3037_0]
                            · have p3037_0 := h3037c.1
                              have p3037_1 := h3037c.2.1
                              have p3037_2 := h3037c.2.2.1
                              have p3037_3 := h3037c.2.2.2
                              linarith only [h2898, h3026, h3032, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3037_1]
                            · have p3037_0 := h3037c.1
                              have p3037_1 := h3037c.2.1
                              have p3037_2 := h3037c.2.2.1
                              have p3037_3 := h3037c.2.2.2
                              linarith only [h2898, hlam, p3037_0]
                            · have p3037_0 := h3037c.1
                              have p3037_1 := h3037c.2.1
                              have p3037_2 := h3037c.2.2.1
                              have p3037_3 := h3037c.2.2.2
                              rcases p3037_3 (m.d 0 2) (by simp) with h3043 | h3043
                              · linarith only [h0, h3043, hlam]
                              · rcases p3037_3 (m.d 1 2) (by simp) with h3045 | h3045
                                · rcases p3037_3 (m.d 2 3) (by simp) with h3046 | h3046
                                  · linarith only [h3026, h3046, hlam]
                                  · linarith only [h2055, h3046, hlam]
                                · linarith only [h0, h3045, hlam]
                            · have p3037_0 := h3037c.1
                              have p3037_1 := h3037c.2.1
                              have p3037_2 := h3037c.2.2.1
                              have p3037_3 := h3037c.2.2.2
                              linarith only [hlam, p3037_0]
                            · have p3037_0 := h3037c.1
                              have p3037_1 := h3037c.2.1
                              have p3037_2 := h3037c.2.2.1
                              have p3037_3 := h3037c.2.2.2
                              linarith only [h0, h2898, h3032, hc01, hc12, hlam, hphi, p3037_1]
                            · have p3037_0 := h3037c.1
                              have p3037_1 := h3037c.2.1
                              have p3037_2 := h3037c.2.2.1
                              have p3037_3 := h3037c.2.2.2
                              linarith only [h2055, h2897, h3026, hlam, p3037_2]
                            · have p3037_0 := h3037c.1
                              have p3037_1 := h3037c.2.1
                              have p3037_2 := h3037c.2.2.1
                              have p3037_3 := h3037c.2.2.2
                              linarith only [h2897, h2898, h3031, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3037_1]
                            · have p3037_0 := h3037c.1
                              have p3037_1 := h3037c.2.1
                              have p3037_2 := h3037c.2.2.1
                              have p3037_3 := h3037c.2.2.2
                              linarith only [h2897, h3026, h3031, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3037_1]
                            · have p3037_0 := h3037c.1
                              have p3037_1 := h3037c.2.1
                              have p3037_2 := h3037c.2.2.1
                              have p3037_3 := h3037c.2.2.2
                              linarith only [h3026, hlam, p3037_0]
                            · have p3037_0 := h3037c.1
                              have p3037_1 := h3037c.2.1
                              have p3037_2 := h3037c.2.2.1
                              have p3037_3 := h3037c.2.2.2
                              linarith only [hlam, p3037_0]
                            · have p3037_0 := h3037c.1
                              have p3037_1 := h3037c.2.1
                              have p3037_2 := h3037c.2.2.1
                              have p3037_3 := h3037c.2.2.2
                              rcases p3037_3 (m.d 0 2) (by simp) with h3057 | h3057
                              · linarith only [h2055, h3057, hlam]
                              · linarith only [h2897, h3057, hlam]
                            · have p3037_0 := h3037c.1
                              have p3037_1 := h3037c.2.1
                              have p3037_2 := h3037c.2.2.1
                              have p3037_3 := h3037c.2.2.2
                              linarith only [h2897, h2898, h3026, h3031, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3037_1]
                            · have p3037_0 := h3037c.1
                              have p3037_1 := h3037c.2.1
                              have p3037_2 := h3037c.2.2.1
                              have p3037_3 := h3037c.2.2.2
                              linarith only [h2897, hlam, p3037_0]
                            · have p3037_0 := h3037c.1
                              have p3037_1 := h3037c.2.1
                              have p3037_2 := h3037c.2.2.1
                              have p3037_3 := h3037c.2.2.2
                              linarith only [h3027, hlam, p3037_0]
                            · have p3037_0 := h3037c.1
                              have p3037_1 := h3037c.2.1
                              have p3037_2 := h3037c.2.2.1
                              have p3037_3 := h3037c.2.2.2
                              linarith only [h3031, hlam, p3037_1]
                            · have p3037_0 := h3037c.1
                              have p3037_1 := h3037c.2.1
                              have p3037_2 := h3037c.2.2.1
                              have p3037_3 := h3037c.2.2.2
                              linarith only [hlam, p3037_0]
                            · have p3037_0 := h3037c.1
                              have p3037_1 := h3037c.2.1
                              have p3037_2 := h3037c.2.2.1
                              have p3037_3 := h3037c.2.2.2
                              linarith only [h3033, hlam, p3037_1]
                            · have p3037_0 := h3037c.1
                              have p3037_1 := h3037c.2.1
                              have p3037_2 := h3037c.2.2.1
                              have p3037_3 := h3037c.2.2.2
                              linarith only [h2897, h3031, h3033, hc34, hc45, hlam, hphi, p3037_1]
                            · have p3037_0 := h3037c.1
                              have p3037_1 := h3037c.2.1
                              have p3037_2 := h3037c.2.2.1
                              have p3037_3 := h3037c.2.2.2
                              linarith only [h3028, hlam, p3037_0]
                            · have p3037_0 := h3037c.1
                              have p3037_1 := h3037c.2.1
                              have p3037_2 := h3037c.2.2.1
                              have p3037_3 := h3037c.2.2.2
                              linarith only [h3032, hlam, p3037_1]
                            · have p3037_0 := h3037c.1
                              have p3037_1 := h3037c.2.1
                              have p3037_2 := h3037c.2.2.1
                              have p3037_3 := h3037c.2.2.2
                              rcases p3037_3 (m.d 0 2) (by simp) with h3069 | h3069
                              · linarith only [h2898, h3069, hlam]
                              · linarith only [h2897, h3069, hlam]
                            · have p3037_0 := h3037c.1
                              have p3037_1 := h3037c.2.1
                              have p3037_2 := h3037c.2.2.1
                              have p3037_3 := h3037c.2.2.2
                              linarith only [hlam, p3037_0]
                      · linarith only [h2055, h2897, h3023, h3031, h3032, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · linarith only [h2055, h3022, h3031, hlam]
                  · linarith only [h1494, h3023, h3030, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h2055, h2897, h3022, h3026, h3029, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
              · linarith only [h2055, h2897, h3026, h3028, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h2055, h2897, h3026, h3027, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3079 | h3079
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3080 | h3080
              · linarith only [h2897, h2898, h3026, h3080, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3082 | h3082
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3083 | h3083
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3084 | h3084
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3085 | h3085
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3086 | h3086
                        · linarith only [h2897, h3086, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3088 | h3088
                          · linarith only [h0, h3080, h3086, h3088, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases h2bigk with h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c | h3090c
                            · have p3090_0 := h3090c.1
                              have p3090_1 := h3090c.2.1
                              have p3090_2 := h3090c.2.2.1
                              have p3090_3 := h3090c.2.2.2
                              linarith only [hlam, p3090_0]
                            · have p3090_0 := h3090c.1
                              have p3090_1 := h3090c.2.1
                              have p3090_2 := h3090c.2.2.1
                              have p3090_3 := h3090c.2.2.2
                              linarith only [h0, hlam, p3090_1]
                            · have p3090_0 := h3090c.1
                              have p3090_1 := h3090c.2.1
                              have p3090_2 := h3090c.2.2.1
                              have p3090_3 := h3090c.2.2.2
                              linarith only [h2055, hlam, p3090_0]
                            · have p3090_0 := h3090c.1
                              have p3090_1 := h3090c.2.1
                              have p3090_2 := h3090c.2.2.1
                              have p3090_3 := h3090c.2.2.2
                              linarith only [h0, h3080, h3084, h3086, hc34, hc45, hlam, hphi, p3090_1]
                            · have p3090_0 := h3090c.1
                              have p3090_1 := h3090c.2.1
                              have p3090_2 := h3090c.2.2.1
                              have p3090_3 := h3090c.2.2.2
                              linarith only [h2898, hlam, p3090_0]
                            · have p3090_0 := h3090c.1
                              have p3090_1 := h3090c.2.1
                              have p3090_2 := h3090c.2.2.1
                              have p3090_3 := h3090c.2.2.2
                              linarith only [h3080, hc02, hc25, hlam, hphi, p3090_1]
                            · have p3090_0 := h3090c.1
                              have p3090_1 := h3090c.2.1
                              have p3090_2 := h3090c.2.2.1
                              have p3090_3 := h3090c.2.2.2
                              linarith only [hlam, p3090_0]
                            · have p3090_0 := h3090c.1
                              have p3090_1 := h3090c.2.1
                              have p3090_2 := h3090c.2.2.1
                              have p3090_3 := h3090c.2.2.2
                              linarith only [h3026, hlam, p3090_0]
                            · have p3090_0 := h3090c.1
                              have p3090_1 := h3090c.2.1
                              have p3090_2 := h3090c.2.2.1
                              have p3090_3 := h3090c.2.2.2
                              linarith only [h3080, h3084, h3086, hc34, hc45, hlam, hphi, p3090_1]
                            · have p3090_0 := h3090c.1
                              have p3090_1 := h3090c.2.1
                              have p3090_2 := h3090c.2.2.1
                              have p3090_3 := h3090c.2.2.2
                              linarith only [h3080, hlam, p3090_0]
                            · have p3090_0 := h3090c.1
                              have p3090_1 := h3090c.2.1
                              have p3090_2 := h3090c.2.2.1
                              have p3090_3 := h3090c.2.2.2
                              rcases p3090_3 (m.d 0 2) (by simp) with h3101 | h3101
                              · linarith only [h3101, hlam, p3090_0]
                              · rcases p3090_3 (m.d 1 2) (by simp) with h3103 | h3103
                                · linarith only [h3026, h3103, hlam]
                                · linarith only [h0, h3103, hlam]
                            · have p3090_0 := h3090c.1
                              have p3090_1 := h3090c.2.1
                              have p3090_2 := h3090c.2.2.1
                              have p3090_3 := h3090c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p3090_1]
                            · have p3090_0 := h3090c.1
                              have p3090_1 := h3090c.2.1
                              have p3090_2 := h3090c.2.2.1
                              have p3090_3 := h3090c.2.2.2
                              linarith only [hlam, p3090_0]
                            · have p3090_0 := h3090c.1
                              have p3090_1 := h3090c.2.1
                              have p3090_2 := h3090c.2.2.1
                              have p3090_3 := h3090c.2.2.2
                              rcases p3090_3 (m.d 0 2) (by simp) with h3108 | h3108
                              · linarith only [h2055, h3108, hlam]
                              · linarith only [h2897, h3108, hlam]
                            · have p3090_0 := h3090c.1
                              have p3090_1 := h3090c.2.1
                              have p3090_2 := h3090c.2.2.1
                              have p3090_3 := h3090c.2.2.2
                              linarith only [h2897, h2898, h3084, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3090_1]
                            · have p3090_0 := h3090c.1
                              have p3090_1 := h3090c.2.1
                              have p3090_2 := h3090c.2.2.1
                              have p3090_3 := h3090c.2.2.2
                              linarith only [h2897, hlam, p3090_0]
                            · have p3090_0 := h3090c.1
                              have p3090_1 := h3090c.2.1
                              have p3090_2 := h3090c.2.2.1
                              have p3090_3 := h3090c.2.2.2
                              linarith only [h3079, hlam, p3090_0]
                            · have p3090_0 := h3090c.1
                              have p3090_1 := h3090c.2.1
                              have p3090_2 := h3090c.2.2.1
                              have p3090_3 := h3090c.2.2.2
                              linarith only [h3084, hlam, p3090_1]
                            · have p3090_0 := h3090c.1
                              have p3090_1 := h3090c.2.1
                              have p3090_2 := h3090c.2.2.1
                              have p3090_3 := h3090c.2.2.2
                              linarith only [hlam, p3090_0]
                            · have p3090_0 := h3090c.1
                              have p3090_1 := h3090c.2.1
                              have p3090_2 := h3090c.2.2.1
                              have p3090_3 := h3090c.2.2.2
                              linarith only [h3086, hlam, p3090_1]
                            · have p3090_0 := h3090c.1
                              have p3090_1 := h3090c.2.1
                              have p3090_2 := h3090c.2.2.1
                              have p3090_3 := h3090c.2.2.2
                              linarith only [h2897, h3084, h3086, hc34, hc45, hlam, hphi, p3090_1]
                            · have p3090_0 := h3090c.1
                              have p3090_1 := h3090c.2.1
                              have p3090_2 := h3090c.2.2.1
                              have p3090_3 := h3090c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3090_1]
                            · have p3090_0 := h3090c.1
                              have p3090_1 := h3090c.2.1
                              have p3090_2 := h3090c.2.2.1
                              have p3090_3 := h3090c.2.2.2
                              linarith only [h3085, hlam, p3090_1]
                            · have p3090_0 := h3090c.1
                              have p3090_1 := h3090c.2.1
                              have p3090_2 := h3090c.2.2.1
                              have p3090_3 := h3090c.2.2.2
                              rcases p3090_3 (m.d 0 2) (by simp) with h3120 | h3120
                              · linarith only [h2898, h3120, hlam]
                              · linarith only [h2897, h3120, hlam]
                            · have p3090_0 := h3090c.1
                              have p3090_1 := h3090c.2.1
                              have p3090_2 := h3090c.2.2.1
                              have p3090_3 := h3090c.2.2.2
                              linarith only [hlam, p3090_0]
                      · linarith only [h2055, h3023, h3085, hlam]
                    · linarith only [h1494, h3022, h3026, h3084, hlam]
                  · linarith only [h1494, h3023, h3083, hlam]
                · linarith only [h1494, h3022, h3082, hlam]
            · linarith only [h0, h2897, h3079, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3129 | h3129
        · linarith only [h2897, h2898, h3129, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3131 | h3131
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3132 | h3132
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3133 | h3133
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3134 | h3134
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3135 | h3135
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3136 | h3136
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3137 | h3137
                      · linarith only [h2055, h2897, h3023, h3131, h3136, h3137, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h2055, h2897, h3131, h3135, h3136, h3137, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h2055, h2897, h3022, h3136, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3141 | h3141
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3142 | h3142
                      · linarith only [h1494, h3135, h3142, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3144 | h3144
                        · linarith only [h2055, h2897, h3023, h3129, h3144, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3146 | h3146
                          · linarith only [h2055, h2897, h3141, h3142, h3144, h3146, hlam]
                          · linarith only [h2055, h2897, h3131, h3135, h3141, h3146, hc34, hc45, hlam, hphi]
                    · linarith only [h2055, h2897, h3022, h3141, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · linarith only [h2055, h2897, h3022, h3131, h3134, hlam]
              · linarith only [h2055, h2897, h3131, h3133, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h2055, h2897, h3131, h3132, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3153 | h3153
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3154 | h3154
              · linarith only [h2897, h2898, h3131, h3154, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3156 | h3156
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3157 | h3157
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3158 | h3158
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3159 | h3159
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3160 | h3160
                        · linarith only [h2897, h3160, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3162 | h3162
                          · linarith only [h2055, h2897, h3023, h3131, h3154, h3157, h3158, h3160, h3162, hc12, hc23, hlam, hphi]
                          · rcases h2bigk with h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c | h3164c
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [hlam, p3164_0]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [h0, hlam, p3164_1]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [h2055, hlam, p3164_0]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [h2055, h3023, h3131, h3157, h3158, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3164_1]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [h2898, hlam, p3164_0]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [h3154, hc02, hc25, hlam, hphi, p3164_1]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [hlam, p3164_0]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [h3131, hlam, p3164_0]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [h3154, h3158, h3160, hc34, hc45, hlam, hphi, p3164_1]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [h3154, hlam, p3164_0]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              rcases p3164_3 (m.d 0 2) (by simp) with h3175 | h3175
                              · linarith only [h3175, hlam, p3164_0]
                              · rcases p3164_3 (m.d 1 2) (by simp) with h3177 | h3177
                                · linarith only [h3131, h3177, hlam]
                                · linarith only [h0, h3177, hlam]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p3164_1]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [hlam, p3164_0]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [h2055, h2897, h3023, h3131, h3157, hlam, p3164_2]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [h2897, h2898, h3158, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3164_1]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [h2897, hlam, p3164_0]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [h3153, hlam, p3164_0]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [h3158, hlam, p3164_1]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [hlam, p3164_0]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [h3160, hlam, p3164_1]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [h2897, h3158, h3160, hc34, hc45, hlam, hphi, p3164_1]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3164_1]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [h3159, hlam, p3164_1]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              rcases p3164_3 (m.d 0 2) (by simp) with h3192 | h3192
                              · linarith only [h2898, h3192, hlam]
                              · linarith only [h2897, h3192, hlam]
                            · have p3164_0 := h3164c.1
                              have p3164_1 := h3164c.2.1
                              have p3164_2 := h3164c.2.2.1
                              have p3164_3 := h3164c.2.2.2
                              linarith only [hlam, p3164_0]
                      · linarith only [h0, h3131, h3159, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h2055, h2897, h3023, h3131, h3157, h3158, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3198 | h3198
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3199 | h3199
                      · linarith only [h1494, h3157, h3199, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h3131, h3199, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h3131, h3198, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h3022, h3023, h3131, h3156, hc12, hc35, hlam, hphi, ht23]
            · linarith only [h0, h2897, h3153, hlam]
    · linarith only [h2055, h2897, h3022, hlam]

end R2N4
