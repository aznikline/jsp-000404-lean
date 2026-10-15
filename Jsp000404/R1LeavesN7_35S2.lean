import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5224000 in
theorem r1l7_20_11_13_14_H_L_L_I_L_I_L_I_s1_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg811 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1501 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1980 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2294 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h2945 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h811 := hg811
  rcases m.htr 0 3 4 (by decide) (by decide) with h2946 | h2946
  · rcases m.htr 0 3 5 (by decide) (by decide) with h2947 | h2947
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2948 | h2948
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2949 | h2949
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2950 | h2950
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2951 | h2951
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2952 | h2952
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2953 | h2953
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2954 | h2954
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2955 | h2955
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2956 | h2956
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2957 | h2957
                        · linarith only [h2294, h2945, h2949, h2957, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h2294, h2945, h2948, h2949, h2957, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h2294, h2947, h2956, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h2294, h2945, h2946, h2948, h2955, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                  · linarith only [h2945, h2948, h2954, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · linarith only [h2947, h2953, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
              · linarith only [h2294, h2946, h2949, h2952, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
            · linarith only [h2294, h2945, h2949, h2951, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
          · linarith only [h2294, h2945, h2949, h2950, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2967 | h2967
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2968 | h2968
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2969 | h2969
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2970 | h2970
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2971 | h2971
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2972 | h2972
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2973 | h2973
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2974 | h2974
                        · linarith only [h2945, h2974, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                        · linarith only [h2294, h2945, h2948, h2974, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h1980, h2947, h2949, h2967, h2971, h2973, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h0, h2949, h2972, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h1501, h2945, h2948, h2971, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h2947, h2949, h2970, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
              · linarith only [h2946, h2969, h811, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2982 | h2982
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2983 | h2983
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2984 | h2984
                  · linarith only [h2967, h2968, h2984, hlam]
                  · linarith only [h1501, h2948, h2984, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                · linarith only [h2947, h2983, h811, hlam]
              · linarith only [h2946, h2982, h811, hlam]
          · linarith only [h2945, h2967, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2990 | h2990
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2991 | h2991
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2992 | h2992
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2993 | h2993
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2994 | h2994
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2995 | h2995
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2996 | h2996
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2997 | h2997
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2998 | h2998
                        · linarith only [h2294, h2945, h2948, h2990, h2998, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3000 | h3000
                          · linarith only [h1501, h2294, h2945, h2948, h2990, h2996, h3000, hc01, hc12, hlam, hphi]
                          · rcases h1bigk with h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c | h3002c
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [hlam, p3002_0]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [h0, hlam, p3002_0]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [h811, hlam, p3002_0]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [h1501, hlam, p3002_0]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [h1980, hlam, p3002_0]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              rcases p3002_3 (m.d 0 1) (by simp) with h3008 | h3008
                              · linarith only [h3008, hlam, p3002_0]
                              · rcases p3002_3 (m.d 1 2) (by simp) with h3010 | h3010
                                · rcases p3002_3 (m.d 1 3) (by simp) with h3011 | h3011
                                  · linarith only [h2990, h3011, hlam]
                                  · linarith only [h3011, h811, hlam]
                                · linarith only [h3010, hlam, p3002_0]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [hlam, p3002_0]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [h811, hc01, hc12, hlam, hphi, p3002_1]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [h1501, hc01, hc12, hlam, hphi, p3002_1]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [h1501, h2948, h2995, hc01, hc12, hlam, hphi, p3002_1]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              rcases p3002_3 (m.d 0 1) (by simp) with h3019 | h3019
                              · linarith only [h3019, hlam, p3002_0]
                              · rcases p3002_3 (m.d 1 2) (by simp) with h3021 | h3021
                                · rcases p3002_3 (m.d 1 3) (by simp) with h3022 | h3022
                                  · rcases p3002_3 (m.d 1 4) (by simp) with h3023 | h3023
                                    · linarith only [h2993, h3023, hlam]
                                    · linarith only [h1501, h3023, hlam]
                                  · linarith only [h3022, hlam, p3002_0]
                                · linarith only [h0, h3021, hlam]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [h2990, hlam, p3002_1]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [hlam, p3002_0]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [h1501, h2948, h2995, hc01, hc13, hlam, hphi, p3002_1]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [h1501, h2948, h2990, h2995, hc01, hc12, hlam, hphi, p3002_1]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              rcases p3002_3 (m.d 0 1) (by simp) with h3032 | h3032
                              · linarith only [h3032, hlam, p3002_0]
                              · rcases p3002_3 (m.d 1 2) (by simp) with h3034 | h3034
                                · rcases p3002_3 (m.d 1 3) (by simp) with h3035 | h3035
                                  · rcases p3002_3 (m.d 1 4) (by simp) with h3036 | h3036
                                    · rcases p3002_3 (m.d 1 5) (by simp) with h3037 | h3037
                                      · linarith only [h2995, h3037, hlam]
                                      · linarith only [h1980, h3037, hlam]
                                    · linarith only [h3036, hlam, p3002_0]
                                  · linarith only [h3035, h811, hlam]
                                · linarith only [h0, h3034, hlam]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [h2991, hlam, p3002_1]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [h2993, hlam, p3002_0]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [hlam, p3002_0]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [h1501, h2948, h2995, hc01, hc14, hlam, hphi, p3002_1]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              rcases p3002_3 (m.d 0 1) (by simp) with h3047 | h3047
                              · linarith only [h3047, hlam, p3002_0]
                              · rcases p3002_3 (m.d 1 2) (by simp) with h3049 | h3049
                                · rcases p3002_3 (m.d 1 3) (by simp) with h3050 | h3050
                                  · rcases p3002_3 (m.d 1 4) (by simp) with h3051 | h3051
                                    · rcases p3002_3 (m.d 1 5) (by simp) with h3052 | h3052
                                      · rcases h3bigk with h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c | h3053c
                                        · have p3053_0 := h3053c.1
                                          have p3053_1 := h3053c.2.1
                                          have p3053_2 := h3053c.2.2.1
                                          have p3053_3 := h3053c.2.2.2
                                          linarith only [hlam, p3053_0]
                                        · have p3053_0 := h3053c.1
                                          have p3053_1 := h3053c.2.1
                                          have p3053_2 := h3053c.2.2.1
                                          have p3053_3 := h3053c.2.2.2
                                          linarith only [h811, hlam, p3053_1]
                                        · have p3053_0 := h3053c.1
                                          have p3053_1 := h3053c.2.1
                                          have p3053_2 := h3053c.2.2.1
                                          have p3053_3 := h3053c.2.2.2
                                          linarith only [h2294, hlam, p3053_1]
                                        · have p3053_0 := h3053c.1
                                          have p3053_1 := h3053c.2.1
                                          have p3053_2 := h3053c.2.2.1
                                          have p3053_3 := h3053c.2.2.2
                                          linarith only [hc34, hlam, hphi, ht0b, ht45, ht5b, p3053_1, u0elo2]
                                        · have p3053_0 := h3053c.1
                                          have p3053_1 := h3053c.2.1
                                          have p3053_2 := h3053c.2.2.1
                                          have p3053_3 := h3053c.2.2.2
                                          linarith only [hc35, hlam, hphi, ht0b, ht5b, p3053_1, u0elo2]
                                        · have p3053_0 := h3053c.1
                                          have p3053_1 := h3053c.2.1
                                          have p3053_2 := h3053c.2.2.1
                                          have p3053_3 := h3053c.2.2.2
                                          rcases p3053_3 (m.d 0 3) (by simp) with h3059 | h3059
                                          · linarith only [h3059, h811, hlam]
                                          · rcases p3053_3 (m.d 1 3) (by simp) with h3061 | h3061
                                            · rcases p3053_3 (m.d 2 3) (by simp) with h3062 | h3062
                                              · linarith only [h2990, h3062, hlam]
                                              · linarith only [h2294, h3062, hlam]
                                            · linarith only [h3061, h811, hlam]
                                        · have p3053_0 := h3053c.1
                                          have p3053_1 := h3053c.2.1
                                          have p3053_2 := h3053c.2.2.1
                                          have p3053_3 := h3053c.2.2.2
                                          linarith only [hlam, p3053_0]
                                        · have p3053_0 := h3053c.1
                                          have p3053_1 := h3053c.2.1
                                          have p3053_2 := h3053c.2.2.1
                                          have p3053_3 := h3053c.2.2.2
                                          linarith only [h2294, h2945, h2990, h2996, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3053_1]
                                        · have p3053_0 := h3053c.1
                                          have p3053_1 := h3053c.2.1
                                          have p3053_2 := h3053c.2.2.1
                                          have p3053_3 := h3053c.2.2.2
                                          rcases p3053_3 (m.d 0 3) (by simp) with h3068 | h3068
                                          · linarith only [h3068, h811, hlam]
                                          · linarith only [h2946, h3068, hlam]
                                        · have p3053_0 := h3053c.1
                                          have p3053_1 := h3053c.2.1
                                          have p3053_2 := h3053c.2.2.1
                                          have p3053_3 := h3053c.2.2.2
                                          rcases p3053_3 (m.d 0 3) (by simp) with h3071 | h3071
                                          · linarith only [h3071, h811, hlam]
                                          · linarith only [h2947, h3071, hlam]
                                        · have p3053_0 := h3053c.1
                                          have p3053_1 := h3053c.2.1
                                          have p3053_2 := h3053c.2.2.1
                                          have p3053_3 := h3053c.2.2.2
                                          linarith only [h2294, h2945, h2990, h2996, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3053_1]
                                        · have p3053_0 := h3053c.1
                                          have p3053_1 := h3053c.2.1
                                          have p3053_2 := h3053c.2.2.1
                                          have p3053_3 := h3053c.2.2.2
                                          linarith only [h2990, hlam, p3053_0]
                                        · have p3053_0 := h3053c.1
                                          have p3053_1 := h3053c.2.1
                                          have p3053_2 := h3053c.2.2.1
                                          have p3053_3 := h3053c.2.2.2
                                          linarith only [hlam, p3053_0]
                                        · have p3053_0 := h3053c.1
                                          have p3053_1 := h3053c.2.1
                                          have p3053_2 := h3053c.2.2.1
                                          have p3053_3 := h3053c.2.2.2
                                          rcases p3053_3 (m.d 0 3) (by simp) with h3077 | h3077
                                          · linarith only [h2294, h3077, hlam]
                                          · linarith only [h2946, h3077, hlam]
                                        · have p3053_0 := h3053c.1
                                          have p3053_1 := h3053c.2.1
                                          have p3053_2 := h3053c.2.2.1
                                          have p3053_3 := h3053c.2.2.2
                                          rcases p3053_3 (m.d 0 3) (by simp) with h3080 | h3080
                                          · linarith only [h2294, h3080, hlam]
                                          · linarith only [h2947, h3080, hlam]
                                        · have p3053_0 := h3053c.1
                                          have p3053_1 := h3053c.2.1
                                          have p3053_2 := h3053c.2.2.1
                                          have p3053_3 := h3053c.2.2.2
                                          linarith only [h2946, hlam, p3053_0]
                                        · have p3053_0 := h3053c.1
                                          have p3053_1 := h3053c.2.1
                                          have p3053_2 := h3053c.2.2.1
                                          have p3053_3 := h3053c.2.2.2
                                          linarith only [h2993, hlam, p3053_0]
                                        · have p3053_0 := h3053c.1
                                          have p3053_1 := h3053c.2.1
                                          have p3053_2 := h3053c.2.2.1
                                          have p3053_3 := h3053c.2.2.2
                                          linarith only [h2996, hlam, p3053_0]
                                        · have p3053_0 := h3053c.1
                                          have p3053_1 := h3053c.2.1
                                          have p3053_2 := h3053c.2.2.1
                                          have p3053_3 := h3053c.2.2.2
                                          linarith only [hlam, p3053_0]
                                        · have p3053_0 := h3053c.1
                                          have p3053_1 := h3053c.2.1
                                          have p3053_2 := h3053c.2.2.1
                                          have p3053_3 := h3053c.2.2.2
                                          linarith only [h3000, hlam, p3053_1]
                                        · have p3053_0 := h3053c.1
                                          have p3053_1 := h3053c.2.1
                                          have p3053_2 := h3053c.2.2.1
                                          have p3053_3 := h3053c.2.2.2
                                          linarith only [h2947, hlam, p3053_0]
                                        · have p3053_0 := h3053c.1
                                          have p3053_1 := h3053c.2.1
                                          have p3053_2 := h3053c.2.2.1
                                          have p3053_3 := h3053c.2.2.2
                                          linarith only [h2994, hlam, p3053_0]
                                        · have p3053_0 := h3053c.1
                                          have p3053_1 := h3053c.2.1
                                          have p3053_2 := h3053c.2.2.1
                                          have p3053_3 := h3053c.2.2.2
                                          linarith only [h2997, hlam, p3053_0]
                                        · have p3053_0 := h3053c.1
                                          have p3053_1 := h3053c.2.1
                                          have p3053_2 := h3053c.2.2.1
                                          have p3053_3 := h3053c.2.2.2
                                          linarith only [h2947, hc34, hlam, hphi, ht0b, ht45, ht5b, p3053_1, u0elo2]
                                        · have p3053_0 := h3053c.1
                                          have p3053_1 := h3053c.2.1
                                          have p3053_2 := h3053c.2.2.1
                                          have p3053_3 := h3053c.2.2.2
                                          linarith only [hlam, p3053_0]
                                      · linarith only [h3052, hlam, p3002_0]
                                    · linarith only [h1501, h3051, hlam]
                                  · linarith only [h3050, h811, hlam]
                                · linarith only [h0, h3049, hlam]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [h2992, hlam, p3002_1]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [h2994, hlam, p3002_0]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [h2995, hlam, p3002_0]
                            · have p3002_0 := h3002c.1
                              have p3002_1 := h3002c.2.1
                              have p3002_2 := h3002c.2.2.1
                              have p3002_3 := h3002c.2.2.2
                              linarith only [hlam, p3002_0]
                      · linarith only [h2947, h2997, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h2294, h2945, h2946, h2996, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3103 | h3103
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3104 | h3104
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3105 | h3105
                        · linarith only [h2945, h2995, h3105, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3107 | h3107
                          · linarith only [h2946, h2995, h3107, hc15, hlam, hphi, ht0b, ht5b, u0elo2]
                          · rcases h1bigk with h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c
                            · have p3109_0 := h3109c.1
                              have p3109_1 := h3109c.2.1
                              have p3109_2 := h3109c.2.2.1
                              have p3109_3 := h3109c.2.2.2
                              linarith only [hlam, p3109_0]
                            · have p3109_0 := h3109c.1
                              have p3109_1 := h3109c.2.1
                              have p3109_2 := h3109c.2.2.1
                              have p3109_3 := h3109c.2.2.2
                              linarith only [h0, hlam, p3109_0]
                            · have p3109_0 := h3109c.1
                              have p3109_1 := h3109c.2.1
                              have p3109_2 := h3109c.2.2.1
                              have p3109_3 := h3109c.2.2.2
                              linarith only [h811, hlam, p3109_0]
                            · have p3109_0 := h3109c.1
                              have p3109_1 := h3109c.2.1
                              have p3109_2 := h3109c.2.2.1
                              have p3109_3 := h3109c.2.2.2
                              linarith only [h1501, hlam, p3109_0]
                            · have p3109_0 := h3109c.1
                              have p3109_1 := h3109c.2.1
                              have p3109_2 := h3109c.2.2.1
                              have p3109_3 := h3109c.2.2.2
                              linarith only [h1980, hlam, p3109_0]
                            · have p3109_0 := h3109c.1
                              have p3109_1 := h3109c.2.1
                              have p3109_2 := h3109c.2.2.1
                              have p3109_3 := h3109c.2.2.2
                              rcases p3109_3 (m.d 0 1) (by simp) with h3115 | h3115
                              · linarith only [h3115, hlam, p3109_0]
                              · rcases p3109_3 (m.d 1 2) (by simp) with h3117 | h3117
                                · rcases p3109_3 (m.d 1 3) (by simp) with h3118 | h3118
                                  · linarith only [h2990, h3118, hlam]
                                  · linarith only [h3118, h811, hlam]
                                · linarith only [h3117, hlam, p3109_0]
                            · have p3109_0 := h3109c.1
                              have p3109_1 := h3109c.2.1
                              have p3109_2 := h3109c.2.2.1
                              have p3109_3 := h3109c.2.2.2
                              linarith only [hlam, p3109_0]
                            · have p3109_0 := h3109c.1
                              have p3109_1 := h3109c.2.1
                              have p3109_2 := h3109c.2.2.1
                              have p3109_3 := h3109c.2.2.2
                              linarith only [h811, hc01, hc12, hlam, hphi, p3109_1]
                            · have p3109_0 := h3109c.1
                              have p3109_1 := h3109c.2.1
                              have p3109_2 := h3109c.2.2.1
                              have p3109_3 := h3109c.2.2.2
                              linarith only [h1501, hc01, hc12, hlam, hphi, p3109_1]
                            · have p3109_0 := h3109c.1
                              have p3109_1 := h3109c.2.1
                              have p3109_2 := h3109c.2.2.1
                              have p3109_3 := h3109c.2.2.2
                              linarith only [h1501, h2995, hc01, hc12, hlam, hphi, p3109_1]
                            · have p3109_0 := h3109c.1
                              have p3109_1 := h3109c.2.1
                              have p3109_2 := h3109c.2.2.1
                              have p3109_3 := h3109c.2.2.2
                              rcases p3109_3 (m.d 0 1) (by simp) with h3126 | h3126
                              · linarith only [h3126, hlam, p3109_0]
                              · rcases p3109_3 (m.d 1 2) (by simp) with h3128 | h3128
                                · rcases p3109_3 (m.d 1 3) (by simp) with h3129 | h3129
                                  · rcases p3109_3 (m.d 1 4) (by simp) with h3130 | h3130
                                    · linarith only [h2993, h3130, hlam]
                                    · linarith only [h1501, h3130, hlam]
                                  · linarith only [h3129, hlam, p3109_0]
                                · linarith only [h0, h3128, hlam]
                            · have p3109_0 := h3109c.1
                              have p3109_1 := h3109c.2.1
                              have p3109_2 := h3109c.2.2.1
                              have p3109_3 := h3109c.2.2.2
                              linarith only [h2990, hlam, p3109_1]
                            · have p3109_0 := h3109c.1
                              have p3109_1 := h3109c.2.1
                              have p3109_2 := h3109c.2.2.1
                              have p3109_3 := h3109c.2.2.2
                              linarith only [hlam, p3109_0]
                            · have p3109_0 := h3109c.1
                              have p3109_1 := h3109c.2.1
                              have p3109_2 := h3109c.2.2.1
                              have p3109_3 := h3109c.2.2.2
                              linarith only [h1501, hc01, hc13, hlam, hphi, p3109_1]
                            · have p3109_0 := h3109c.1
                              have p3109_1 := h3109c.2.1
                              have p3109_2 := h3109c.2.2.1
                              have p3109_3 := h3109c.2.2.2
                              linarith only [h1501, h2990, h2995, hc01, hc12, hlam, hphi, p3109_1]
                            · have p3109_0 := h3109c.1
                              have p3109_1 := h3109c.2.1
                              have p3109_2 := h3109c.2.2.1
                              have p3109_3 := h3109c.2.2.2
                              linarith only [h2995, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3109_1]
                            · have p3109_0 := h3109c.1
                              have p3109_1 := h3109c.2.1
                              have p3109_2 := h3109c.2.2.1
                              have p3109_3 := h3109c.2.2.2
                              linarith only [h2991, hlam, p3109_1]
                            · have p3109_0 := h3109c.1
                              have p3109_1 := h3109c.2.1
                              have p3109_2 := h3109c.2.2.1
                              have p3109_3 := h3109c.2.2.2
                              linarith only [h2993, hlam, p3109_0]
                            · have p3109_0 := h3109c.1
                              have p3109_1 := h3109c.2.1
                              have p3109_2 := h3109c.2.2.1
                              have p3109_3 := h3109c.2.2.2
                              linarith only [hlam, p3109_0]
                            · have p3109_0 := h3109c.1
                              have p3109_1 := h3109c.2.1
                              have p3109_2 := h3109c.2.2.1
                              have p3109_3 := h3109c.2.2.2
                              linarith only [h2995, hlam, p3109_1]
                            · have p3109_0 := h3109c.1
                              have p3109_1 := h3109c.2.1
                              have p3109_2 := h3109c.2.2.1
                              have p3109_3 := h3109c.2.2.2
                              rcases p3109_3 (m.d 0 1) (by simp) with h3144 | h3144
                              · linarith only [h3144, hlam, p3109_0]
                              · rcases p3109_3 (m.d 1 2) (by simp) with h3146 | h3146
                                · rcases p3109_3 (m.d 1 3) (by simp) with h3147 | h3147
                                  · rcases p3109_3 (m.d 1 4) (by simp) with h3148 | h3148
                                    · linarith only [h2995, h3148, hlam]
                                    · linarith only [h1501, h3148, hlam]
                                  · linarith only [h3147, h811, hlam]
                                · linarith only [h0, h3146, hlam]
                            · have p3109_0 := h3109c.1
                              have p3109_1 := h3109c.2.1
                              have p3109_2 := h3109c.2.2.1
                              have p3109_3 := h3109c.2.2.2
                              linarith only [h2992, hlam, p3109_1]
                            · have p3109_0 := h3109c.1
                              have p3109_1 := h3109c.2.1
                              have p3109_2 := h3109c.2.2.1
                              have p3109_3 := h3109c.2.2.2
                              linarith only [h2994, hlam, p3109_0]
                            · have p3109_0 := h3109c.1
                              have p3109_1 := h3109c.2.1
                              have p3109_2 := h3109c.2.2.1
                              have p3109_3 := h3109c.2.2.2
                              linarith only [h1501, hc01, hc15, hlam, hphi, p3109_1]
                            · have p3109_0 := h3109c.1
                              have p3109_1 := h3109c.2.1
                              have p3109_2 := h3109c.2.2.1
                              have p3109_3 := h3109c.2.2.2
                              linarith only [hlam, p3109_0]
                      · linarith only [h2294, h2947, h3104, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h2294, h2945, h2946, h3103, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · linarith only [h2947, h2994, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
              · linarith only [h2294, h2945, h2946, h2990, h2993, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
            · linarith only [h2294, h2945, h2990, h2992, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
          · linarith only [h2294, h2945, h2990, h2991, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3163 | h3163
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3164 | h3164
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3165 | h3165
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3166 | h3166
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3167 | h3167
                  · linarith only [h1501, h2948, h2990, h3163, h3167, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3169 | h3169
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3170 | h3170
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3171 | h3171
                        · linarith only [h2945, h3167, h3171, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3173 | h3173
                          · linarith only [h1501, h3167, h3173, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases h1bigk with h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c | h3175c
                            · have p3175_0 := h3175c.1
                              have p3175_1 := h3175c.2.1
                              have p3175_2 := h3175c.2.2.1
                              have p3175_3 := h3175c.2.2.2
                              linarith only [hlam, p3175_0]
                            · have p3175_0 := h3175c.1
                              have p3175_1 := h3175c.2.1
                              have p3175_2 := h3175c.2.2.1
                              have p3175_3 := h3175c.2.2.2
                              linarith only [h0, hlam, p3175_0]
                            · have p3175_0 := h3175c.1
                              have p3175_1 := h3175c.2.1
                              have p3175_2 := h3175c.2.2.1
                              have p3175_3 := h3175c.2.2.2
                              linarith only [h811, hlam, p3175_0]
                            · have p3175_0 := h3175c.1
                              have p3175_1 := h3175c.2.1
                              have p3175_2 := h3175c.2.2.1
                              have p3175_3 := h3175c.2.2.2
                              linarith only [h1501, hlam, p3175_0]
                            · have p3175_0 := h3175c.1
                              have p3175_1 := h3175c.2.1
                              have p3175_2 := h3175c.2.2.1
                              have p3175_3 := h3175c.2.2.2
                              linarith only [h1980, hlam, p3175_0]
                            · have p3175_0 := h3175c.1
                              have p3175_1 := h3175c.2.1
                              have p3175_2 := h3175c.2.2.1
                              have p3175_3 := h3175c.2.2.2
                              linarith only [h2990, hc01, hc23, hlam, hphi, ht12, p3175_1]
                            · have p3175_0 := h3175c.1
                              have p3175_1 := h3175c.2.1
                              have p3175_2 := h3175c.2.2.1
                              have p3175_3 := h3175c.2.2.2
                              linarith only [hlam, p3175_0]
                            · have p3175_0 := h3175c.1
                              have p3175_1 := h3175c.2.1
                              have p3175_2 := h3175c.2.2.1
                              have p3175_3 := h3175c.2.2.2
                              linarith only [h2990, hlam, p3175_0]
                            · have p3175_0 := h3175c.1
                              have p3175_1 := h3175c.2.1
                              have p3175_2 := h3175c.2.2.1
                              have p3175_3 := h3175c.2.2.2
                              linarith only [h1501, h2990, hc01, hc23, hlam, hphi, ht12, p3175_1]
                            · have p3175_0 := h3175c.1
                              have p3175_1 := h3175c.2.1
                              have p3175_2 := h3175c.2.2.1
                              have p3175_3 := h3175c.2.2.2
                              linarith only [h1980, h2990, hc01, hc23, hlam, hphi, ht12, p3175_1]
                            · have p3175_0 := h3175c.1
                              have p3175_1 := h3175c.2.1
                              have p3175_2 := h3175c.2.2.1
                              have p3175_3 := h3175c.2.2.2
                              rcases p3175_3 (m.d 0 1) (by simp) with h3186 | h3186
                              · linarith only [h3186, hlam, p3175_0]
                              · rcases p3175_3 (m.d 1 2) (by simp) with h3188 | h3188
                                · linarith only [h2990, h3188, hlam]
                                · linarith only [h0, h3188, hlam]
                            · have p3175_0 := h3175c.1
                              have p3175_1 := h3175c.2.1
                              have p3175_2 := h3175c.2.2.1
                              have p3175_3 := h3175c.2.2.2
                              linarith only [h0, hc01, hc13, hlam, hphi, p3175_1]
                            · have p3175_0 := h3175c.1
                              have p3175_1 := h3175c.2.1
                              have p3175_2 := h3175c.2.2.1
                              have p3175_3 := h3175c.2.2.2
                              linarith only [hlam, p3175_0]
                            · have p3175_0 := h3175c.1
                              have p3175_1 := h3175c.2.1
                              have p3175_2 := h3175c.2.2.1
                              have p3175_3 := h3175c.2.2.2
                              linarith only [h1501, h2990, hc01, hc23, hlam, hphi, ht12, p3175_1]
                            · have p3175_0 := h3175c.1
                              have p3175_1 := h3175c.2.1
                              have p3175_2 := h3175c.2.2.1
                              have p3175_3 := h3175c.2.2.2
                              linarith only [h1501, h2990, h3167, hc01, hc23, hlam, hphi, ht12, p3175_1]
                            · have p3175_0 := h3175c.1
                              have p3175_1 := h3175c.2.1
                              have p3175_2 := h3175c.2.2.1
                              have p3175_3 := h3175c.2.2.2
                              linarith only [h3167, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3175_1]
                            · have p3175_0 := h3175c.1
                              have p3175_1 := h3175c.2.1
                              have p3175_2 := h3175c.2.2.1
                              have p3175_3 := h3175c.2.2.2
                              linarith only [h3163, hlam, p3175_1]
                            · have p3175_0 := h3175c.1
                              have p3175_1 := h3175c.2.1
                              have p3175_2 := h3175c.2.2.1
                              have p3175_3 := h3175c.2.2.2
                              linarith only [h3165, hlam, p3175_0]
                            · have p3175_0 := h3175c.1
                              have p3175_1 := h3175c.2.1
                              have p3175_2 := h3175c.2.2.1
                              have p3175_3 := h3175c.2.2.2
                              linarith only [hlam, p3175_0]
                            · have p3175_0 := h3175c.1
                              have p3175_1 := h3175c.2.1
                              have p3175_2 := h3175c.2.2.1
                              have p3175_3 := h3175c.2.2.2
                              linarith only [h3167, hlam, p3175_1]
                            · have p3175_0 := h3175c.1
                              have p3175_1 := h3175c.2.1
                              have p3175_2 := h3175c.2.2.1
                              have p3175_3 := h3175c.2.2.2
                              linarith only [h2990, h3164, hc01, hc23, hlam, hphi, ht12, p3175_1]
                            · have p3175_0 := h3175c.1
                              have p3175_1 := h3175c.2.1
                              have p3175_2 := h3175c.2.2.1
                              have p3175_3 := h3175c.2.2.2
                              linarith only [h3164, hlam, p3175_1]
                            · have p3175_0 := h3175c.1
                              have p3175_1 := h3175c.2.1
                              have p3175_2 := h3175c.2.2.1
                              have p3175_3 := h3175c.2.2.2
                              linarith only [h3166, hlam, p3175_0]
                            · have p3175_0 := h3175c.1
                              have p3175_1 := h3175c.2.1
                              have p3175_2 := h3175c.2.2.1
                              have p3175_3 := h3175c.2.2.2
                              linarith only [h1501, h2990, h3164, hc01, hc23, hlam, hphi, ht12, p3175_1]
                            · have p3175_0 := h3175c.1
                              have p3175_1 := h3175c.2.1
                              have p3175_2 := h3175c.2.2.1
                              have p3175_3 := h3175c.2.2.2
                              linarith only [hlam, p3175_0]
                      · linarith only [h2947, h2990, h3170, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h1501, h2946, h2990, h3164, h3167, h3169, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h2947, h3166, h811, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
              · linarith only [h2946, h2947, h3165, h811, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3209 | h3209
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3210 | h3210
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3211 | h3211
                  · linarith only [h1501, h2948, h2990, h3163, h3211, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3213 | h3213
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3214 | h3214
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3215 | h3215
                        · linarith only [h2945, h3211, h3215, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3217 | h3217
                          · linarith only [h0, h3164, h3215, h3217, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases h1bigk with h3219c | h3219c | h3219c | h3219c | h3219c | h3219c | h3219c | h3219c | h3219c | h3219c | h3219c | h3219c | h3219c | h3219c | h3219c | h3219c | h3219c | h3219c | h3219c | h3219c | h3219c | h3219c | h3219c | h3219c | h3219c
                            · have p3219_0 := h3219c.1
                              have p3219_1 := h3219c.2.1
                              have p3219_2 := h3219c.2.2.1
                              have p3219_3 := h3219c.2.2.2
                              linarith only [hlam, p3219_0]
                            · have p3219_0 := h3219c.1
                              have p3219_1 := h3219c.2.1
                              have p3219_2 := h3219c.2.2.1
                              have p3219_3 := h3219c.2.2.2
                              linarith only [h0, hlam, p3219_0]
                            · have p3219_0 := h3219c.1
                              have p3219_1 := h3219c.2.1
                              have p3219_2 := h3219c.2.2.1
                              have p3219_3 := h3219c.2.2.2
                              linarith only [h811, hlam, p3219_0]
                            · have p3219_0 := h3219c.1
                              have p3219_1 := h3219c.2.1
                              have p3219_2 := h3219c.2.2.1
                              have p3219_3 := h3219c.2.2.2
                              linarith only [h1501, hlam, p3219_0]
                            · have p3219_0 := h3219c.1
                              have p3219_1 := h3219c.2.1
                              have p3219_2 := h3219c.2.2.1
                              have p3219_3 := h3219c.2.2.2
                              linarith only [h1980, hlam, p3219_0]
                            · have p3219_0 := h3219c.1
                              have p3219_1 := h3219c.2.1
                              have p3219_2 := h3219c.2.2.1
                              have p3219_3 := h3219c.2.2.2
                              linarith only [h3164, hc01, hc25, hlam, hphi, ht12, p3219_1]
                            · have p3219_0 := h3219c.1
                              have p3219_1 := h3219c.2.1
                              have p3219_2 := h3219c.2.2.1
                              have p3219_3 := h3219c.2.2.2
                              linarith only [hlam, p3219_0]
                            · have p3219_0 := h3219c.1
                              have p3219_1 := h3219c.2.1
                              have p3219_2 := h3219c.2.2.1
                              have p3219_3 := h3219c.2.2.2
                              linarith only [h2990, hlam, p3219_0]
                            · have p3219_0 := h3219c.1
                              have p3219_1 := h3219c.2.1
                              have p3219_2 := h3219c.2.2.1
                              have p3219_3 := h3219c.2.2.2
                              linarith only [h1501, h3164, h3215, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3219_1]
                            · have p3219_0 := h3219c.1
                              have p3219_1 := h3219c.2.1
                              have p3219_2 := h3219c.2.2.1
                              have p3219_3 := h3219c.2.2.2
                              linarith only [h3164, hlam, p3219_0]
                            · have p3219_0 := h3219c.1
                              have p3219_1 := h3219c.2.1
                              have p3219_2 := h3219c.2.2.1
                              have p3219_3 := h3219c.2.2.2
                              rcases p3219_3 (m.d 0 1) (by simp) with h3230 | h3230
                              · linarith only [h3230, hlam, p3219_0]
                              · rcases p3219_3 (m.d 1 2) (by simp) with h3232 | h3232
                                · linarith only [h2990, h3232, hlam]
                                · linarith only [h0, h3232, hlam]
                            · have p3219_0 := h3219c.1
                              have p3219_1 := h3219c.2.1
                              have p3219_2 := h3219c.2.2.1
                              have p3219_3 := h3219c.2.2.2
                              linarith only [h0, hc01, hc13, hlam, hphi, p3219_1]
                            · have p3219_0 := h3219c.1
                              have p3219_1 := h3219c.2.1
                              have p3219_2 := h3219c.2.2.1
                              have p3219_3 := h3219c.2.2.2
                              linarith only [hlam, p3219_0]
                            · have p3219_0 := h3219c.1
                              have p3219_1 := h3219c.2.1
                              have p3219_2 := h3219c.2.2.1
                              have p3219_3 := h3219c.2.2.2
                              linarith only [h1501, h2990, hc01, hc23, hlam, hphi, ht12, p3219_1]
                            · have p3219_0 := h3219c.1
                              have p3219_1 := h3219c.2.1
                              have p3219_2 := h3219c.2.2.1
                              have p3219_3 := h3219c.2.2.2
                              linarith only [h1501, h2990, h3163, h3164, hc01, hc23, hlam, hphi, ht12, p3219_1]
                            · have p3219_0 := h3219c.1
                              have p3219_1 := h3219c.2.1
                              have p3219_2 := h3219c.2.2.1
                              have p3219_3 := h3219c.2.2.2
                              linarith only [h2990, h3163, hc01, hc23, hlam, hphi, ht12, p3219_1]
                            · have p3219_0 := h3219c.1
                              have p3219_1 := h3219c.2.1
                              have p3219_2 := h3219c.2.2.1
                              have p3219_3 := h3219c.2.2.2
                              linarith only [h3163, hlam, p3219_1]
                            · have p3219_0 := h3219c.1
                              have p3219_1 := h3219c.2.1
                              have p3219_2 := h3219c.2.2.1
                              have p3219_3 := h3219c.2.2.2
                              linarith only [h3209, hlam, p3219_0]
                            · have p3219_0 := h3219c.1
                              have p3219_1 := h3219c.2.1
                              have p3219_2 := h3219c.2.2.1
                              have p3219_3 := h3219c.2.2.2
                              linarith only [hlam, p3219_0]
                            · have p3219_0 := h3219c.1
                              have p3219_1 := h3219c.2.1
                              have p3219_2 := h3219c.2.2.1
                              have p3219_3 := h3219c.2.2.2
                              linarith only [h3211, hlam, p3219_1]
                            · have p3219_0 := h3219c.1
                              have p3219_1 := h3219c.2.1
                              have p3219_2 := h3219c.2.2.1
                              have p3219_3 := h3219c.2.2.2
                              rcases p3219_3 (m.d 0 1) (by simp) with h3244 | h3244
                              · linarith only [h3244, hlam, p3219_0]
                              · rcases p3219_3 (m.d 1 2) (by simp) with h3246 | h3246
                                · linarith only [h3164, h3246, hlam]
                                · linarith only [h0, h3246, hlam]
                            · have p3219_0 := h3219c.1
                              have p3219_1 := h3219c.2.1
                              have p3219_2 := h3219c.2.2.1
                              have p3219_3 := h3219c.2.2.2
                              linarith only [h0, hc01, hc15, hlam, hphi, p3219_1]
                            · have p3219_0 := h3219c.1
                              have p3219_1 := h3219c.2.1
                              have p3219_2 := h3219c.2.2.1
                              have p3219_3 := h3219c.2.2.2
                              linarith only [h3210, hlam, p3219_0]
                            · have p3219_0 := h3219c.1
                              have p3219_1 := h3219c.2.1
                              have p3219_2 := h3219c.2.2.1
                              have p3219_3 := h3219c.2.2.2
                              linarith only [h1501, h3164, h3215, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3219_1]
                            · have p3219_0 := h3219c.1
                              have p3219_1 := h3219c.2.1
                              have p3219_2 := h3219c.2.2.1
                              have p3219_3 := h3219c.2.2.2
                              linarith only [hlam, p3219_0]
                      · linarith only [h2294, h2947, h3214, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h1501, h2990, h3163, h3213, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h2947, h3210, h811, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
              · linarith only [h2946, h2947, h3209, h811, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
          · linarith only [h0, h2945, h3163, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3258 | h3258
      · linarith only [h2294, h2945, h2947, h3258, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3260 | h3260
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3261 | h3261
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3262 | h3262
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3263 | h3263
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3264 | h3264
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3265 | h3265
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3266 | h3266
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3267 | h3267
                      · linarith only [h2294, h2945, h2947, h3260, h3267, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h2294, h2945, h3264, h3266, h3267, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h2294, h2945, h2946, h2947, h3266, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3271 | h3271
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3272 | h3272
                      · linarith only [h2947, h3260, h3272, h811, hc01, hc12, hlam, hphi]
                      · linarith only [h2294, h2945, h3260, h3264, h3271, h3272, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h2294, h2945, h2946, h3271, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3276 | h3276
                  · linarith only [h1501, h3258, h3263, h3264, h3276, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3278 | h3278
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3279 | h3279
                      · linarith only [h3264, h3279, h811, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3281 | h3281
                        · linarith only [h2945, h3276, h3281, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3283 | h3283
                          · linarith only [h2946, h2947, h3276, h3283, hc15, hlam, hphi, ht0b, ht5b, u0elo4]
                          · linarith only [h2294, h2945, h3260, h3264, h3283, hc24, hc45, hlam, hphi]
                    · linarith only [h2294, h2945, h2946, h2947, h3278, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
              · linarith only [h2294, h2945, h2946, h2947, h3260, h3263, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
            · linarith only [h2294, h2945, h3260, h3262, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
          · linarith only [h2294, h2945, h3260, h3261, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3290 | h3290
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3291 | h3291
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3292 | h3292
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3293 | h3293
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3294 | h3294
                  · linarith only [h1501, h3258, h3260, h3290, h3294, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3296 | h3296
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3297 | h3297
                      · linarith only [h2947, h3260, h3291, h3297, h811, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h3260, h3297, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h2294, h2945, h2947, h3260, h3291, h3293, h3296, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h3260, h3291, h3293, hlam]
              · linarith only [h2946, h3260, h3292, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3303 | h3303
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3304 | h3304
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3305 | h3305
                  · linarith only [h1501, h3258, h3290, h3291, h3305, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3307 | h3307
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3308 | h3308
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3309 | h3309
                        · linarith only [h2945, h3305, h3309, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3311 | h3311
                          · linarith only [h2294, h2945, h2947, h3260, h3291, h3304, h3307, h3309, h3311, hc12, hc23, hlam, hphi]
                          · rcases h1bigk with h3313c | h3313c | h3313c | h3313c | h3313c | h3313c | h3313c | h3313c | h3313c | h3313c | h3313c | h3313c | h3313c | h3313c | h3313c | h3313c | h3313c | h3313c | h3313c | h3313c | h3313c | h3313c | h3313c | h3313c | h3313c
                            · have p3313_0 := h3313c.1
                              have p3313_1 := h3313c.2.1
                              have p3313_2 := h3313c.2.2.1
                              have p3313_3 := h3313c.2.2.2
                              linarith only [hlam, p3313_0]
                            · have p3313_0 := h3313c.1
                              have p3313_1 := h3313c.2.1
                              have p3313_2 := h3313c.2.2.1
                              have p3313_3 := h3313c.2.2.2
                              linarith only [h0, hlam, p3313_0]
                            · have p3313_0 := h3313c.1
                              have p3313_1 := h3313c.2.1
                              have p3313_2 := h3313c.2.2.1
                              have p3313_3 := h3313c.2.2.2
                              linarith only [h811, hlam, p3313_0]
                            · have p3313_0 := h3313c.1
                              have p3313_1 := h3313c.2.1
                              have p3313_2 := h3313c.2.2.1
                              have p3313_3 := h3313c.2.2.2
                              linarith only [h1501, hlam, p3313_0]
                            · have p3313_0 := h3313c.1
                              have p3313_1 := h3313c.2.1
                              have p3313_2 := h3313c.2.2.1
                              have p3313_3 := h3313c.2.2.2
                              linarith only [h1980, hlam, p3313_0]
                            · have p3313_0 := h3313c.1
                              have p3313_1 := h3313c.2.1
                              have p3313_2 := h3313c.2.2.1
                              have p3313_3 := h3313c.2.2.2
                              linarith only [h3291, hc01, hc25, hlam, hphi, ht12, p3313_1]
                            · have p3313_0 := h3313c.1
                              have p3313_1 := h3313c.2.1
                              have p3313_2 := h3313c.2.2.1
                              have p3313_3 := h3313c.2.2.2
                              linarith only [hlam, p3313_0]
                            · have p3313_0 := h3313c.1
                              have p3313_1 := h3313c.2.1
                              have p3313_2 := h3313c.2.2.1
                              have p3313_3 := h3313c.2.2.2
                              linarith only [h3260, hlam, p3313_0]
                            · have p3313_0 := h3313c.1
                              have p3313_1 := h3313c.2.1
                              have p3313_2 := h3313c.2.2.1
                              have p3313_3 := h3313c.2.2.2
                              linarith only [h1501, h2294, h2945, h2947, h3260, h3291, h3304, h3307, h3309, hc01, hc23, hc34, hc45, hlam, hphi, ht12, p3313_1]
                            · have p3313_0 := h3313c.1
                              have p3313_1 := h3313c.2.1
                              have p3313_2 := h3313c.2.2.1
                              have p3313_3 := h3313c.2.2.2
                              linarith only [h3291, hlam, p3313_0]
                            · have p3313_0 := h3313c.1
                              have p3313_1 := h3313c.2.1
                              have p3313_2 := h3313c.2.2.1
                              have p3313_3 := h3313c.2.2.2
                              rcases p3313_3 (m.d 0 1) (by simp) with h3324 | h3324
                              · linarith only [h3324, hlam, p3313_0]
                              · rcases p3313_3 (m.d 1 2) (by simp) with h3326 | h3326
                                · linarith only [h3260, h3326, hlam]
                                · linarith only [h0, h3326, hlam]
                            · have p3313_0 := h3313c.1
                              have p3313_1 := h3313c.2.1
                              have p3313_2 := h3313c.2.2.1
                              have p3313_3 := h3313c.2.2.2
                              linarith only [h0, h3260, hc01, hc23, hlam, hphi, ht12, p3313_1]
                            · have p3313_0 := h3313c.1
                              have p3313_1 := h3313c.2.1
                              have p3313_2 := h3313c.2.2.1
                              have p3313_3 := h3313c.2.2.2
                              linarith only [hlam, p3313_0]
                            · have p3313_0 := h3313c.1
                              have p3313_1 := h3313c.2.1
                              have p3313_2 := h3313c.2.2.1
                              have p3313_3 := h3313c.2.2.2
                              linarith only [h1501, h3260, hc01, hc23, hlam, hphi, ht12, p3313_1]
                            · have p3313_0 := h3313c.1
                              have p3313_1 := h3313c.2.1
                              have p3313_2 := h3313c.2.2.1
                              have p3313_3 := h3313c.2.2.2
                              linarith only [h2294, h2945, h2947, h3260, h3304, h3307, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3313_1]
                            · have p3313_0 := h3313c.1
                              have p3313_1 := h3313c.2.1
                              have p3313_2 := h3313c.2.2.1
                              have p3313_3 := h3313c.2.2.2
                              linarith only [h3260, h3290, hc01, hc23, hlam, hphi, ht12, p3313_1]
                            · have p3313_0 := h3313c.1
                              have p3313_1 := h3313c.2.1
                              have p3313_2 := h3313c.2.2.1
                              have p3313_3 := h3313c.2.2.2
                              linarith only [h3290, hlam, p3313_1]
                            · have p3313_0 := h3313c.1
                              have p3313_1 := h3313c.2.1
                              have p3313_2 := h3313c.2.2.1
                              have p3313_3 := h3313c.2.2.2
                              linarith only [h3303, hlam, p3313_0]
                            · have p3313_0 := h3313c.1
                              have p3313_1 := h3313c.2.1
                              have p3313_2 := h3313c.2.2.1
                              have p3313_3 := h3313c.2.2.2
                              linarith only [hlam, p3313_0]
                            · have p3313_0 := h3313c.1
                              have p3313_1 := h3313c.2.1
                              have p3313_2 := h3313c.2.2.1
                              have p3313_3 := h3313c.2.2.2
                              linarith only [h3305, hlam, p3313_1]
                            · have p3313_0 := h3313c.1
                              have p3313_1 := h3313c.2.1
                              have p3313_2 := h3313c.2.2.1
                              have p3313_3 := h3313c.2.2.2
                              rcases p3313_3 (m.d 0 1) (by simp) with h3338 | h3338
                              · linarith only [h3338, hlam, p3313_0]
                              · rcases p3313_3 (m.d 1 2) (by simp) with h3340 | h3340
                                · linarith only [h3291, h3340, hlam]
                                · linarith only [h0, h3340, hlam]
                            · have p3313_0 := h3313c.1
                              have p3313_1 := h3313c.2.1
                              have p3313_2 := h3313c.2.2.1
                              have p3313_3 := h3313c.2.2.2
                              linarith only [h0, hc01, hc15, hlam, hphi, p3313_1]
                            · have p3313_0 := h3313c.1
                              have p3313_1 := h3313c.2.1
                              have p3313_2 := h3313c.2.2.1
                              have p3313_3 := h3313c.2.2.2
                              linarith only [h3304, hlam, p3313_0]
                            · have p3313_0 := h3313c.1
                              have p3313_1 := h3313c.2.1
                              have p3313_2 := h3313c.2.2.1
                              have p3313_3 := h3313c.2.2.2
                              linarith only [h1501, h3291, h3309, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3313_1]
                            · have p3313_0 := h3313c.1
                              have p3313_1 := h3313c.2.1
                              have p3313_2 := h3313c.2.2.1
                              have p3313_3 := h3313c.2.2.2
                              linarith only [hlam, p3313_0]
                      · linarith only [h3260, h3304, h3308, hlam]
                    · linarith only [h2294, h2947, h3260, h3304, h3307, hc02, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3349 | h3349
                  · linarith only [h1501, h3258, h3260, h3290, h3349, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3351 | h3351
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3352 | h3352
                      · linarith only [h0, h3260, h3304, h3352, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h1501, h3260, h3290, h3352, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h1501, h3260, h3290, h3351, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h1501, h2946, h2947, h3260, h3290, h3303, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
          · linarith only [h0, h2945, h3290, hlam]
  · linarith only [h2294, h2945, h2946, hlam]

end R2N4
