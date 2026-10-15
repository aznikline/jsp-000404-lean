import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5416000 in
set_option maxHeartbeats 5416000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s4_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3095 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h3096 | h3096
  · rcases m.htr 0 1 5 (by decide) (by decide) with h3097 | h3097
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3098 | h3098
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3099 | h3099
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3100 | h3100
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3101 | h3101
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3102 | h3102
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3103 | h3103
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3104 | h3104
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3105 | h3105
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3106 | h3106
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3107 | h3107
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3108 | h3108
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3109 | h3109
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3110 | h3110
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3111 | h3111
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3112 | h3112
                                  · linarith only [h0, h3095, h3104, h3109, h3112, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                  · linarith only [h0, h3095, h3107, h3108, h3112, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h0, h3095, h3107, h3108, h3111, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h0, h3095, h3102, h3109, h3110, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h0, h3095, h3107, h3109, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3118 | h3118
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3119 | h3119
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3120 | h3120
                                · linarith only [h3105, h3108, h3120, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3122 | h3122
                                  · linarith only [h3105, h3108, h3118, h3122, hlam]
                                  · rcases h0bigk with h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c | h3124c
                                    · have p3124_0 := h3124c.1
                                      have p3124_1 := h3124c.2.1
                                      have p3124_2 := h3124c.2.2.1
                                      have p3124_3 := h3124c.2.2.2
                                      linarith only [hlam, p3124_0]
                                    · have p3124_0 := h3124c.1
                                      have p3124_1 := h3124c.2.1
                                      have p3124_2 := h3124c.2.2.1
                                      have p3124_3 := h3124c.2.2.2
                                      linarith only [h0, hlam, p3124_1]
                                    · have p3124_0 := h3124c.1
                                      have p3124_1 := h3124c.2.1
                                      have p3124_2 := h3124c.2.2.1
                                      have p3124_3 := h3124c.2.2.2
                                      linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3124_1]
                                    · have p3124_0 := h3124c.1
                                      have p3124_1 := h3124c.2.1
                                      have p3124_2 := h3124c.2.2.1
                                      have p3124_3 := h3124c.2.2.2
                                      linarith only [h0, h3103, h3105, h3108, h3118, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3124_1]
                                    · have p3124_0 := h3124c.1
                                      have p3124_1 := h3124c.2.1
                                      have p3124_2 := h3124c.2.2.1
                                      have p3124_3 := h3124c.2.2.2
                                      linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p3124_1]
                                    · have p3124_0 := h3124c.1
                                      have p3124_1 := h3124c.2.1
                                      have p3124_2 := h3124c.2.2.1
                                      have p3124_3 := h3124c.2.2.2
                                      linarith only [h3095, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3124_1]
                                    · have p3124_0 := h3124c.1
                                      have p3124_1 := h3124c.2.1
                                      have p3124_2 := h3124c.2.2.1
                                      have p3124_3 := h3124c.2.2.2
                                      linarith only [hlam, p3124_0]
                                    · have p3124_0 := h3124c.1
                                      have p3124_1 := h3124c.2.1
                                      have p3124_2 := h3124c.2.2.1
                                      have p3124_3 := h3124c.2.2.2
                                      linarith only [h0, h3101, h3103, h3105, h3108, h3118, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3124_1]
                                    · have p3124_0 := h3124c.1
                                      have p3124_1 := h3124c.2.1
                                      have p3124_2 := h3124c.2.2.1
                                      have p3124_3 := h3124c.2.2.2
                                      linarith only [h0, h3103, h3105, h3108, h3118, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3124_1]
                                    · have p3124_0 := h3124c.1
                                      have p3124_1 := h3124c.2.1
                                      have p3124_2 := h3124c.2.2.1
                                      have p3124_3 := h3124c.2.2.2
                                      linarith only [h0, h3103, h3105, h3108, h3118, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3124_1]
                                    · have p3124_0 := h3124c.1
                                      have p3124_1 := h3124c.2.1
                                      have p3124_2 := h3124c.2.2.1
                                      have p3124_3 := h3124c.2.2.2
                                      linarith only [h3095, hlam, p3124_1]
                                    · have p3124_0 := h3124c.1
                                      have p3124_1 := h3124c.2.1
                                      have p3124_2 := h3124c.2.2.1
                                      have p3124_3 := h3124c.2.2.2
                                      linarith only [h3098, hlam, p3124_1]
                                    · have p3124_0 := h3124c.1
                                      have p3124_1 := h3124c.2.1
                                      have p3124_2 := h3124c.2.2.1
                                      have p3124_3 := h3124c.2.2.2
                                      linarith only [hlam, p3124_0]
                                    · have p3124_0 := h3124c.1
                                      have p3124_1 := h3124c.2.1
                                      have p3124_2 := h3124c.2.2.1
                                      have p3124_3 := h3124c.2.2.2
                                      linarith only [h3095, h3103, h3105, h3108, h3118, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3124_1]
                                    · have p3124_0 := h3124c.1
                                      have p3124_1 := h3124c.2.1
                                      have p3124_2 := h3124c.2.2.1
                                      have p3124_3 := h3124c.2.2.2
                                      linarith only [h0, h3095, h3103, h3105, h3108, h3118, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3124_1]
                                    · have p3124_0 := h3124c.1
                                      have p3124_1 := h3124c.2.1
                                      have p3124_2 := h3124c.2.2.1
                                      have p3124_3 := h3124c.2.2.2
                                      linarith only [h3096, hlam, p3124_0]
                                    · have p3124_0 := h3124c.1
                                      have p3124_1 := h3124c.2.1
                                      have p3124_2 := h3124c.2.2.1
                                      have p3124_3 := h3124c.2.2.2
                                      linarith only [h3099, hlam, p3124_0]
                                    · have p3124_0 := h3124c.1
                                      have p3124_1 := h3124c.2.1
                                      have p3124_2 := h3124c.2.2.1
                                      have p3124_3 := h3124c.2.2.2
                                      linarith only [h3101, hlam, p3124_0]
                                    · have p3124_0 := h3124c.1
                                      have p3124_1 := h3124c.2.1
                                      have p3124_2 := h3124c.2.2.1
                                      have p3124_3 := h3124c.2.2.2
                                      linarith only [hlam, p3124_0]
                                    · have p3124_0 := h3124c.1
                                      have p3124_1 := h3124c.2.1
                                      have p3124_2 := h3124c.2.2.1
                                      have p3124_3 := h3124c.2.2.2
                                      linarith only [h3103, h3105, h3108, h3118, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p3124_1]
                                    · have p3124_0 := h3124c.1
                                      have p3124_1 := h3124c.2.1
                                      have p3124_2 := h3124c.2.2.1
                                      have p3124_3 := h3124c.2.2.2
                                      linarith only [h3097, hlam, p3124_0]
                                    · have p3124_0 := h3124c.1
                                      have p3124_1 := h3124c.2.1
                                      have p3124_2 := h3124c.2.2.1
                                      have p3124_3 := h3124c.2.2.2
                                      linarith only [h3100, hlam, p3124_1]
                                    · have p3124_0 := h3124c.1
                                      have p3124_1 := h3124c.2.1
                                      have p3124_2 := h3124c.2.2.1
                                      have p3124_3 := h3124c.2.2.2
                                      linarith only [h3102, hlam, p3124_0]
                                    · have p3124_0 := h3124c.1
                                      have p3124_1 := h3124c.2.1
                                      have p3124_2 := h3124c.2.2.1
                                      have p3124_3 := h3124c.2.2.2
                                      linarith only [h3103, hlam, p3124_1]
                                    · have p3124_0 := h3124c.1
                                      have p3124_1 := h3124c.2.1
                                      have p3124_2 := h3124c.2.2.1
                                      have p3124_3 := h3124c.2.2.2
                                      linarith only [hlam, p3124_0]
                              · linarith only [h0, h3095, h3102, h3118, h3119, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h0, h3095, h3107, h3118, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3152 | h3152
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3153 | h3153
                            · linarith only [h3104, h3107, h3153, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3155 | h3155
                              · linarith only [h0, h3095, h3101, h3104, h3107, h3155, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3157 | h3157
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3158 | h3158
                                  · rcases h0bigk with h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [hlam, p3159_0]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h0, hlam, p3159_1]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3159_1]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3159_1]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p3159_1]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p3159_1]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [hlam, p3159_0]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h0, h3101, h3104, h3107, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3159_1]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h0, h3101, h3104, h3107, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3159_1]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h0, h3102, h3155, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3159_1]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h3095, hlam, p3159_1]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h3098, hlam, p3159_1]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [hlam, p3159_0]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h3095, h3101, h3104, h3107, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3159_1]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h0, h3095, h3102, h3155, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3159_1]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h3096, hlam, p3159_0]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h3099, hlam, p3159_0]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h3101, hlam, p3159_0]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [hlam, p3159_0]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h3102, h3155, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3159_1]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h3097, hlam, p3159_0]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h3100, hlam, p3159_1]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h3102, hlam, p3159_0]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [h3103, hlam, p3159_1]
                                    · have p3159_0 := h3159c.1
                                      have p3159_1 := h3159c.2.1
                                      have p3159_2 := h3159c.2.2.1
                                      have p3159_3 := h3159c.2.2.2
                                      linarith only [hlam, p3159_0]
                                  · linarith only [h3104, h3107, h3158, hc23, hlam, hphi, ht34, ht45, u5elo4]
                                · linarith only [h0, h3095, h3101, h3107, h3152, h3157, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3187 | h3187
                            · linarith only [h3104, h3107, h3187, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3189 | h3189
                              · linarith only [h0, h3095, h3101, h3103, h3104, h3107, h3152, h3189, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3191 | h3191
                                · linarith only [h3105, h3152, h3191, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3193 | h3193
                                  · linarith only [h0, h3095, h3101, h3104, h3107, h3152, h3193, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                  · linarith only [h3104, h3107, h3193, hc23, hlam, hphi, ht34, ht45, u5elo4]
                      · linarith only [h0, h3106, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                    · linarith only [h0, h3096, h3099, h3105, hlam]
                  · linarith only [h0, h3098, h3104, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3199 | h3199
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3200 | h3200
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3201 | h3201
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3202 | h3202
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3203 | h3203
                          · linarith only [h0, h3096, h3103, h3203, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3205 | h3205
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3206 | h3206
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3207 | h3207
                                · linarith only [h3097, h3103, h3200, h3203, h3207, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3209 | h3209
                                  · linarith only [h3103, h3205, h3207, h3209, hc04, hlam, hphi, ht45, u5elo2]
                                  · rcases h0bigk with h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c | h3211c
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
                                      linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3211_1]
                                    · have p3211_0 := h3211c.1
                                      have p3211_1 := h3211c.2.1
                                      have p3211_2 := h3211c.2.2.1
                                      have p3211_3 := h3211c.2.2.2
                                      linarith only [h0, h3096, h3200, h3205, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3211_1]
                                    · have p3211_0 := h3211c.1
                                      have p3211_1 := h3211c.2.1
                                      have p3211_2 := h3211c.2.2.1
                                      have p3211_3 := h3211c.2.2.2
                                      linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p3211_1]
                                    · have p3211_0 := h3211c.1
                                      have p3211_1 := h3211c.2.1
                                      have p3211_2 := h3211c.2.2.1
                                      have p3211_3 := h3211c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p3211_1]
                                    · have p3211_0 := h3211c.1
                                      have p3211_1 := h3211c.2.1
                                      have p3211_2 := h3211c.2.2.1
                                      have p3211_3 := h3211c.2.2.2
                                      linarith only [hlam, p3211_0]
                                    · have p3211_0 := h3211c.1
                                      have p3211_1 := h3211c.2.1
                                      have p3211_2 := h3211c.2.2.1
                                      have p3211_3 := h3211c.2.2.2
                                      linarith only [h0, h3101, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3211_1]
                                    · have p3211_0 := h3211c.1
                                      have p3211_1 := h3211c.2.1
                                      have p3211_2 := h3211c.2.2.1
                                      have p3211_3 := h3211c.2.2.2
                                      rcases p3211_3 (m.d 0 1) (by simp) with h3220 | h3220
                                      · linarith only [h0, h3220, hlam]
                                      · linarith only [h3096, h3220, hlam]
                                    · have p3211_0 := h3211c.1
                                      have p3211_1 := h3211c.2.1
                                      have p3211_2 := h3211c.2.2.1
                                      have p3211_3 := h3211c.2.2.2
                                      rcases p3211_3 (m.d 0 1) (by simp) with h3223 | h3223
                                      · linarith only [h0, h3223, hlam]
                                      · linarith only [h3097, h3223, hlam]
                                    · have p3211_0 := h3211c.1
                                      have p3211_1 := h3211c.2.1
                                      have p3211_2 := h3211c.2.2.1
                                      have p3211_3 := h3211c.2.2.2
                                      linarith only [h3095, hlam, p3211_1]
                                    · have p3211_0 := h3211c.1
                                      have p3211_1 := h3211c.2.1
                                      have p3211_2 := h3211c.2.2.1
                                      have p3211_3 := h3211c.2.2.2
                                      linarith only [h3098, hlam, p3211_1]
                                    · have p3211_0 := h3211c.1
                                      have p3211_1 := h3211c.2.1
                                      have p3211_2 := h3211c.2.2.1
                                      have p3211_3 := h3211c.2.2.2
                                      linarith only [hlam, p3211_0]
                                    · have p3211_0 := h3211c.1
                                      have p3211_1 := h3211c.2.1
                                      have p3211_2 := h3211c.2.2.1
                                      have p3211_3 := h3211c.2.2.2
                                      linarith only [h0, h3095, h3096, h3200, h3205, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3211_1]
                                    · have p3211_0 := h3211c.1
                                      have p3211_1 := h3211c.2.1
                                      have p3211_2 := h3211c.2.2.1
                                      have p3211_3 := h3211c.2.2.2
                                      linarith only [h0, h3095, h3096, h3103, h3200, h3205, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3211_1]
                                    · have p3211_0 := h3211c.1
                                      have p3211_1 := h3211c.2.1
                                      have p3211_2 := h3211c.2.2.1
                                      have p3211_3 := h3211c.2.2.2
                                      linarith only [h3096, hlam, p3211_0]
                                    · have p3211_0 := h3211c.1
                                      have p3211_1 := h3211c.2.1
                                      have p3211_2 := h3211c.2.2.1
                                      have p3211_3 := h3211c.2.2.2
                                      linarith only [h3099, hlam, p3211_0]
                                    · have p3211_0 := h3211c.1
                                      have p3211_1 := h3211c.2.1
                                      have p3211_2 := h3211c.2.2.1
                                      have p3211_3 := h3211c.2.2.2
                                      linarith only [h3101, hlam, p3211_0]
                                    · have p3211_0 := h3211c.1
                                      have p3211_1 := h3211c.2.1
                                      have p3211_2 := h3211c.2.2.1
                                      have p3211_3 := h3211c.2.2.2
                                      linarith only [hlam, p3211_0]
                                    · have p3211_0 := h3211c.1
                                      have p3211_1 := h3211c.2.1
                                      have p3211_2 := h3211c.2.2.1
                                      have p3211_3 := h3211c.2.2.2
                                      linarith only [h3103, hlam, p3211_0]
                                    · have p3211_0 := h3211c.1
                                      have p3211_1 := h3211c.2.1
                                      have p3211_2 := h3211c.2.2.1
                                      have p3211_3 := h3211c.2.2.2
                                      linarith only [h3097, hlam, p3211_0]
                                    · have p3211_0 := h3211c.1
                                      have p3211_1 := h3211c.2.1
                                      have p3211_2 := h3211c.2.2.1
                                      have p3211_3 := h3211c.2.2.2
                                      linarith only [h3100, hlam, p3211_1]
                                    · have p3211_0 := h3211c.1
                                      have p3211_1 := h3211c.2.1
                                      have p3211_2 := h3211c.2.2.1
                                      have p3211_3 := h3211c.2.2.2
                                      linarith only [h3102, hlam, p3211_0]
                                    · have p3211_0 := h3211c.1
                                      have p3211_1 := h3211c.2.1
                                      have p3211_2 := h3211c.2.2.1
                                      have p3211_3 := h3211c.2.2.2
                                      linarith only [h3096, h3200, h3205, hc34, hlam, hphi, ht45, p3211_1, u5elo0]
                                    · have p3211_0 := h3211c.1
                                      have p3211_1 := h3211c.2.1
                                      have p3211_2 := h3211c.2.2.1
                                      have p3211_3 := h3211c.2.2.2
                                      linarith only [hlam, p3211_0]
                              · linarith only [h0, h3095, h3102, h3205, h3206, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h0, h3095, h3202, h3205, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h3101, h3103, h3202, hc13, hlam, hphi, ht34, ht45, u5elo4]
                      · linarith only [h0, h3201, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                    · linarith only [h0, h3099, h3103, h3200, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h0, h3098, h3199, hlam]
              · linarith only [h3101, h3102, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3248 | h3248
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3249 | h3249
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3250 | h3250
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3251 | h3251
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3252 | h3252
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3253 | h3253
                        · linarith only [h0, h3095, h3101, h3253, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3255 | h3255
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3256 | h3256
                            · linarith only [h3095, h3101, h3250, h3256, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3258 | h3258
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3259 | h3259
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3260 | h3260
                                  · rcases h0bigk with h3261c | h3261c | h3261c | h3261c | h3261c | h3261c | h3261c | h3261c | h3261c | h3261c | h3261c | h3261c | h3261c | h3261c | h3261c | h3261c | h3261c | h3261c | h3261c | h3261c | h3261c | h3261c | h3261c | h3261c | h3261c
                                    · have p3261_0 := h3261c.1
                                      have p3261_1 := h3261c.2.1
                                      have p3261_2 := h3261c.2.2.1
                                      have p3261_3 := h3261c.2.2.2
                                      linarith only [hlam, p3261_0]
                                    · have p3261_0 := h3261c.1
                                      have p3261_1 := h3261c.2.1
                                      have p3261_2 := h3261c.2.2.1
                                      have p3261_3 := h3261c.2.2.2
                                      linarith only [h0, hlam, p3261_1]
                                    · have p3261_0 := h3261c.1
                                      have p3261_1 := h3261c.2.1
                                      have p3261_2 := h3261c.2.2.1
                                      have p3261_3 := h3261c.2.2.2
                                      linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3261_1]
                                    · have p3261_0 := h3261c.1
                                      have p3261_1 := h3261c.2.1
                                      have p3261_2 := h3261c.2.2.1
                                      have p3261_3 := h3261c.2.2.2
                                      linarith only [h0, h3095, h3101, h3250, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3261_1]
                                    · have p3261_0 := h3261c.1
                                      have p3261_1 := h3261c.2.1
                                      have p3261_2 := h3261c.2.2.1
                                      have p3261_3 := h3261c.2.2.2
                                      linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p3261_1]
                                    · have p3261_0 := h3261c.1
                                      have p3261_1 := h3261c.2.1
                                      have p3261_2 := h3261c.2.2.1
                                      have p3261_3 := h3261c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p3261_1]
                                    · have p3261_0 := h3261c.1
                                      have p3261_1 := h3261c.2.1
                                      have p3261_2 := h3261c.2.2.1
                                      have p3261_3 := h3261c.2.2.2
                                      linarith only [hlam, p3261_0]
                                    · have p3261_0 := h3261c.1
                                      have p3261_1 := h3261c.2.1
                                      have p3261_2 := h3261c.2.2.1
                                      have p3261_3 := h3261c.2.2.2
                                      linarith only [h0, h3248, h3260, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3261_1]
                                    · have p3261_0 := h3261c.1
                                      have p3261_1 := h3261c.2.1
                                      have p3261_2 := h3261c.2.2.1
                                      have p3261_3 := h3261c.2.2.2
                                      linarith only [h0, h3101, h3248, h3260, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3261_1]
                                    · have p3261_0 := h3261c.1
                                      have p3261_1 := h3261c.2.1
                                      have p3261_2 := h3261c.2.2.1
                                      have p3261_3 := h3261c.2.2.2
                                      rcases p3261_3 (m.d 0 1) (by simp) with h3271 | h3271
                                      · linarith only [h0, h3271, hlam]
                                      · linarith only [h3097, h3271, hlam]
                                    · have p3261_0 := h3261c.1
                                      have p3261_1 := h3261c.2.1
                                      have p3261_2 := h3261c.2.2.1
                                      have p3261_3 := h3261c.2.2.2
                                      linarith only [h3095, hlam, p3261_1]
                                    · have p3261_0 := h3261c.1
                                      have p3261_1 := h3261c.2.1
                                      have p3261_2 := h3261c.2.2.1
                                      have p3261_3 := h3261c.2.2.2
                                      linarith only [h3098, hlam, p3261_1]
                                    · have p3261_0 := h3261c.1
                                      have p3261_1 := h3261c.2.1
                                      have p3261_2 := h3261c.2.2.1
                                      have p3261_3 := h3261c.2.2.2
                                      linarith only [hlam, p3261_0]
                                    · have p3261_0 := h3261c.1
                                      have p3261_1 := h3261c.2.1
                                      have p3261_2 := h3261c.2.2.1
                                      have p3261_3 := h3261c.2.2.2
                                      linarith only [h3101, hlam, p3261_1]
                                    · have p3261_0 := h3261c.1
                                      have p3261_1 := h3261c.2.1
                                      have p3261_2 := h3261c.2.2.1
                                      have p3261_3 := h3261c.2.2.2
                                      linarith only [h3097, h3101, h3252, h3258, h3260, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3261_1]
                                    · have p3261_0 := h3261c.1
                                      have p3261_1 := h3261c.2.1
                                      have p3261_2 := h3261c.2.2.1
                                      have p3261_3 := h3261c.2.2.2
                                      linarith only [h3096, hlam, p3261_0]
                                    · have p3261_0 := h3261c.1
                                      have p3261_1 := h3261c.2.1
                                      have p3261_2 := h3261c.2.2.1
                                      have p3261_3 := h3261c.2.2.2
                                      linarith only [h3099, hlam, p3261_0]
                                    · have p3261_0 := h3261c.1
                                      have p3261_1 := h3261c.2.1
                                      have p3261_2 := h3261c.2.2.1
                                      have p3261_3 := h3261c.2.2.2
                                      linarith only [h3095, h3250, h3258, h3260, hc04, hc45, hlam, hphi, ht0b, ht5b, p3261_1]
                                    · have p3261_0 := h3261c.1
                                      have p3261_1 := h3261c.2.1
                                      have p3261_2 := h3261c.2.2.1
                                      have p3261_3 := h3261c.2.2.2
                                      linarith only [hlam, p3261_0]
                                    · have p3261_0 := h3261c.1
                                      have p3261_1 := h3261c.2.1
                                      have p3261_2 := h3261c.2.2.1
                                      have p3261_3 := h3261c.2.2.2
                                      linarith only [h0, h3096, h3097, h3252, h3258, h3260, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3261_1]
                                    · have p3261_0 := h3261c.1
                                      have p3261_1 := h3261c.2.1
                                      have p3261_2 := h3261c.2.2.1
                                      have p3261_3 := h3261c.2.2.2
                                      linarith only [h3097, hlam, p3261_0]
                                    · have p3261_0 := h3261c.1
                                      have p3261_1 := h3261c.2.1
                                      have p3261_2 := h3261c.2.2.1
                                      have p3261_3 := h3261c.2.2.2
                                      linarith only [h3100, hlam, p3261_1]
                                    · have p3261_0 := h3261c.1
                                      have p3261_1 := h3261c.2.1
                                      have p3261_2 := h3261c.2.2.1
                                      have p3261_3 := h3261c.2.2.2
                                      linarith only [h3248, hlam, p3261_0]
                                    · have p3261_0 := h3261c.1
                                      have p3261_1 := h3261c.2.1
                                      have p3261_2 := h3261c.2.2.1
                                      have p3261_3 := h3261c.2.2.2
                                      linarith only [h3249, hlam, p3261_1]
                                    · have p3261_0 := h3261c.1
                                      have p3261_1 := h3261c.2.1
                                      have p3261_2 := h3261c.2.2.1
                                      have p3261_3 := h3261c.2.2.2
                                      linarith only [hlam, p3261_0]
                                  · linarith only [h3095, h3101, h3260, hc13, hlam, hphi, ht34, ht45, u5elo4]
                                · linarith only [h0, h3096, h3255, h3259, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h3101, h3248, h3258, hc23, hc34, hlam, hphi]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3292 | h3292
                            · linarith only [h0, h3096, h3101, h3249, h3250, h3253, h3255, h3292, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3294 | h3294
                              · linarith only [h0, h3096, h3249, h3250, h3253, h3255, h3294, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h3101, h3248, h3294, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h3252, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                    · linarith only [h0, h3095, h3099, h3250, h3251, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h3098, h3250, hlam]
                · linarith only [h3101, h3248, h3249, hc35, hlam, hphi, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3301 | h3301
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3302 | h3302
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3303 | h3303
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3304 | h3304
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3305 | h3305
                        · linarith only [h3095, h3248, h3305, hc34, hlam, hphi, ht45, u5elo3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3307 | h3307
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3308 | h3308
                            · linarith only [h3098, h3101, h3308, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3310 | h3310
                              · linarith only [h3095, h3248, h3302, h3310, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3312 | h3312
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3313 | h3313
                                  · rcases h0bigk with h3314c | h3314c | h3314c | h3314c | h3314c | h3314c | h3314c | h3314c | h3314c | h3314c | h3314c | h3314c | h3314c | h3314c | h3314c | h3314c | h3314c | h3314c | h3314c | h3314c | h3314c | h3314c | h3314c | h3314c | h3314c
                                    · have p3314_0 := h3314c.1
                                      have p3314_1 := h3314c.2.1
                                      have p3314_2 := h3314c.2.2.1
                                      have p3314_3 := h3314c.2.2.2
                                      linarith only [hlam, p3314_0]
                                    · have p3314_0 := h3314c.1
                                      have p3314_1 := h3314c.2.1
                                      have p3314_2 := h3314c.2.2.1
                                      have p3314_3 := h3314c.2.2.2
                                      linarith only [h0, hlam, p3314_1]
                                    · have p3314_0 := h3314c.1
                                      have p3314_1 := h3314c.2.1
                                      have p3314_2 := h3314c.2.2.1
                                      have p3314_3 := h3314c.2.2.2
                                      linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3314_1]
                                    · have p3314_0 := h3314c.1
                                      have p3314_1 := h3314c.2.1
                                      have p3314_2 := h3314c.2.2.1
                                      have p3314_3 := h3314c.2.2.2
                                      linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3314_1]
                                    · have p3314_0 := h3314c.1
                                      have p3314_1 := h3314c.2.1
                                      have p3314_2 := h3314c.2.2.1
                                      have p3314_3 := h3314c.2.2.2
                                      linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p3314_1]
                                    · have p3314_0 := h3314c.1
                                      have p3314_1 := h3314c.2.1
                                      have p3314_2 := h3314c.2.2.1
                                      have p3314_3 := h3314c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p3314_1]
                                    · have p3314_0 := h3314c.1
                                      have p3314_1 := h3314c.2.1
                                      have p3314_2 := h3314c.2.2.1
                                      have p3314_3 := h3314c.2.2.2
                                      linarith only [hlam, p3314_0]
                                    · have p3314_0 := h3314c.1
                                      have p3314_1 := h3314c.2.1
                                      have p3314_2 := h3314c.2.2.1
                                      have p3314_3 := h3314c.2.2.2
                                      rcases p3314_3 (m.d 0 1) (by simp) with h3322 | h3322
                                      · linarith only [h0, h3322, hlam]
                                      · linarith only [h3095, h3322, hlam]
                                    · have p3314_0 := h3314c.1
                                      have p3314_1 := h3314c.2.1
                                      have p3314_2 := h3314c.2.2.1
                                      have p3314_3 := h3314c.2.2.2
                                      linarith only [h0, h3096, h3303, h3312, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3314_1]
                                    · have p3314_0 := h3314c.1
                                      have p3314_1 := h3314c.2.1
                                      have p3314_2 := h3314c.2.2.1
                                      have p3314_3 := h3314c.2.2.2
                                      rcases p3314_3 (m.d 0 1) (by simp) with h3326 | h3326
                                      · linarith only [h0, h3326, hlam]
                                      · linarith only [h3097, h3326, hlam]
                                    · have p3314_0 := h3314c.1
                                      have p3314_1 := h3314c.2.1
                                      have p3314_2 := h3314c.2.2.1
                                      have p3314_3 := h3314c.2.2.2
                                      linarith only [h3095, hlam, p3314_1]
                                    · have p3314_0 := h3314c.1
                                      have p3314_1 := h3314c.2.1
                                      have p3314_2 := h3314c.2.2.1
                                      have p3314_3 := h3314c.2.2.2
                                      linarith only [h3098, hlam, p3314_1]
                                    · have p3314_0 := h3314c.1
                                      have p3314_1 := h3314c.2.1
                                      have p3314_2 := h3314c.2.2.1
                                      have p3314_3 := h3314c.2.2.2
                                      linarith only [hlam, p3314_0]
                                    · have p3314_0 := h3314c.1
                                      have p3314_1 := h3314c.2.1
                                      have p3314_2 := h3314c.2.2.1
                                      have p3314_3 := h3314c.2.2.2
                                      linarith only [h3101, hlam, p3314_1]
                                    · have p3314_0 := h3314c.1
                                      have p3314_1 := h3314c.2.1
                                      have p3314_2 := h3314c.2.2.1
                                      have p3314_3 := h3314c.2.2.2
                                      linarith only [h3248, hlam, p3314_1]
                                    · have p3314_0 := h3314c.1
                                      have p3314_1 := h3314c.2.1
                                      have p3314_2 := h3314c.2.2.1
                                      have p3314_3 := h3314c.2.2.2
                                      linarith only [h3096, hlam, p3314_0]
                                    · have p3314_0 := h3314c.1
                                      have p3314_1 := h3314c.2.1
                                      have p3314_2 := h3314c.2.2.1
                                      have p3314_3 := h3314c.2.2.2
                                      linarith only [h3099, hlam, p3314_0]
                                    · have p3314_0 := h3314c.1
                                      have p3314_1 := h3314c.2.1
                                      have p3314_2 := h3314c.2.2.1
                                      have p3314_3 := h3314c.2.2.2
                                      linarith only [h0, h3095, h3096, h3302, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3314_1]
                                    · have p3314_0 := h3314c.1
                                      have p3314_1 := h3314c.2.1
                                      have p3314_2 := h3314c.2.2.1
                                      have p3314_3 := h3314c.2.2.2
                                      linarith only [hlam, p3314_0]
                                    · have p3314_0 := h3314c.1
                                      have p3314_1 := h3314c.2.1
                                      have p3314_2 := h3314c.2.2.1
                                      have p3314_3 := h3314c.2.2.2
                                      linarith only [h0, h3096, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p3314_1]
                                    · have p3314_0 := h3314c.1
                                      have p3314_1 := h3314c.2.1
                                      have p3314_2 := h3314c.2.2.1
                                      have p3314_3 := h3314c.2.2.2
                                      linarith only [h3097, hlam, p3314_0]
                                    · have p3314_0 := h3314c.1
                                      have p3314_1 := h3314c.2.1
                                      have p3314_2 := h3314c.2.2.1
                                      have p3314_3 := h3314c.2.2.2
                                      linarith only [h3100, hlam, p3314_1]
                                    · have p3314_0 := h3314c.1
                                      have p3314_1 := h3314c.2.1
                                      have p3314_2 := h3314c.2.2.1
                                      have p3314_3 := h3314c.2.2.2
                                      linarith only [h3095, h3302, hc23, hlam, hphi, ht34, ht45, p3314_1, u5elo0]
                                    · have p3314_0 := h3314c.1
                                      have p3314_1 := h3314c.2.1
                                      have p3314_2 := h3314c.2.2.1
                                      have p3314_3 := h3314c.2.2.2
                                      linarith only [h3301, hlam, p3314_1]
                                    · have p3314_0 := h3314c.1
                                      have p3314_1 := h3314c.2.1
                                      have p3314_2 := h3314c.2.2.1
                                      have p3314_3 := h3314c.2.2.2
                                      linarith only [hlam, p3314_0]
                                  · linarith only [h0, h3096, h3101, h3303, h3312, h3313, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h0, h3096, h3307, h3312, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3346 | h3346
                            · linarith only [h3101, h3301, h3302, h3305, h3307, h3346, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3348 | h3348
                              · linarith only [h3248, h3302, h3305, h3307, h3348, hc05, hlam, hphi, u5elo4]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3350 | h3350
                                · linarith only [h3303, h3307, h3350, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3352 | h3352
                                  · rcases h0bigk with h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c | h3353c
                                    · have p3353_0 := h3353c.1
                                      have p3353_1 := h3353c.2.1
                                      have p3353_2 := h3353c.2.2.1
                                      have p3353_3 := h3353c.2.2.2
                                      linarith only [hlam, p3353_0]
                                    · have p3353_0 := h3353c.1
                                      have p3353_1 := h3353c.2.1
                                      have p3353_2 := h3353c.2.2.1
                                      have p3353_3 := h3353c.2.2.2
                                      linarith only [h0, hlam, p3353_1]
                                    · have p3353_0 := h3353c.1
                                      have p3353_1 := h3353c.2.1
                                      have p3353_2 := h3353c.2.2.1
                                      have p3353_3 := h3353c.2.2.2
                                      linarith only [h0, h3095, h3302, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3353_1]
                                    · have p3353_0 := h3353c.1
                                      have p3353_1 := h3353c.2.1
                                      have p3353_2 := h3353c.2.2.1
                                      have p3353_3 := h3353c.2.2.2
                                      linarith only [h0, h3301, h3302, h3305, h3307, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3353_1]
                                    · have p3353_0 := h3353c.1
                                      have p3353_1 := h3353c.2.1
                                      have p3353_2 := h3353c.2.2.1
                                      have p3353_3 := h3353c.2.2.2
                                      linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p3353_1]
                                    · have p3353_0 := h3353c.1
                                      have p3353_1 := h3353c.2.1
                                      have p3353_2 := h3353c.2.2.1
                                      have p3353_3 := h3353c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p3353_1]
                                    · have p3353_0 := h3353c.1
                                      have p3353_1 := h3353c.2.1
                                      have p3353_2 := h3353c.2.2.1
                                      have p3353_3 := h3353c.2.2.2
                                      linarith only [hlam, p3353_0]
                                    · have p3353_0 := h3353c.1
                                      have p3353_1 := h3353c.2.1
                                      have p3353_2 := h3353c.2.2.1
                                      have p3353_3 := h3353c.2.2.2
                                      rcases p3353_3 (m.d 0 1) (by simp) with h3361 | h3361
                                      · linarith only [h0, h3361, hlam]
                                      · linarith only [h3095, h3361, hlam]
                                    · have p3353_0 := h3353c.1
                                      have p3353_1 := h3353c.2.1
                                      have p3353_2 := h3353c.2.2.1
                                      have p3353_3 := h3353c.2.2.2
                                      linarith only [h0, h3301, h3302, h3305, h3307, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3353_1]
                                    · have p3353_0 := h3353c.1
                                      have p3353_1 := h3353c.2.1
                                      have p3353_2 := h3353c.2.2.1
                                      have p3353_3 := h3353c.2.2.2
                                      linarith only [h0, h3301, h3302, h3305, h3307, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3353_1]
                                    · have p3353_0 := h3353c.1
                                      have p3353_1 := h3353c.2.1
                                      have p3353_2 := h3353c.2.2.1
                                      have p3353_3 := h3353c.2.2.2
                                      linarith only [h3095, hlam, p3353_1]
                                    · have p3353_0 := h3353c.1
                                      have p3353_1 := h3353c.2.1
                                      have p3353_2 := h3353c.2.2.1
                                      have p3353_3 := h3353c.2.2.2
                                      linarith only [h3098, hlam, p3353_1]
                                    · have p3353_0 := h3353c.1
                                      have p3353_1 := h3353c.2.1
                                      have p3353_2 := h3353c.2.2.1
                                      have p3353_3 := h3353c.2.2.2
                                      linarith only [hlam, p3353_0]
                                    · have p3353_0 := h3353c.1
                                      have p3353_1 := h3353c.2.1
                                      have p3353_2 := h3353c.2.2.1
                                      have p3353_3 := h3353c.2.2.2
                                      linarith only [h3101, hlam, p3353_1]
                                    · have p3353_0 := h3353c.1
                                      have p3353_1 := h3353c.2.1
                                      have p3353_2 := h3353c.2.2.1
                                      have p3353_3 := h3353c.2.2.2
                                      linarith only [h3248, hlam, p3353_1]
                                    · have p3353_0 := h3353c.1
                                      have p3353_1 := h3353c.2.1
                                      have p3353_2 := h3353c.2.2.1
                                      have p3353_3 := h3353c.2.2.2
                                      linarith only [h3096, hlam, p3353_0]
                                    · have p3353_0 := h3353c.1
                                      have p3353_1 := h3353c.2.1
                                      have p3353_2 := h3353c.2.2.1
                                      have p3353_3 := h3353c.2.2.2
                                      linarith only [h3099, hlam, p3353_0]
                                    · have p3353_0 := h3353c.1
                                      have p3353_1 := h3353c.2.1
                                      have p3353_2 := h3353c.2.2.1
                                      have p3353_3 := h3353c.2.2.2
                                      linarith only [h3095, h3101, h3302, hc23, hc34, hlam, hphi, p3353_1]
                                    · have p3353_0 := h3353c.1
                                      have p3353_1 := h3353c.2.1
                                      have p3353_2 := h3353c.2.2.1
                                      have p3353_3 := h3353c.2.2.2
                                      linarith only [hlam, p3353_0]
                                    · have p3353_0 := h3353c.1
                                      have p3353_1 := h3353c.2.1
                                      have p3353_2 := h3353c.2.2.1
                                      have p3353_3 := h3353c.2.2.2
                                      linarith only [h0, h3096, h3301, h3302, h3305, h3307, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3353_1]
                                    · have p3353_0 := h3353c.1
                                      have p3353_1 := h3353c.2.1
                                      have p3353_2 := h3353c.2.2.1
                                      have p3353_3 := h3353c.2.2.2
                                      linarith only [h3097, hlam, p3353_0]
                                    · have p3353_0 := h3353c.1
                                      have p3353_1 := h3353c.2.1
                                      have p3353_2 := h3353c.2.2.1
                                      have p3353_3 := h3353c.2.2.2
                                      linarith only [h3100, hlam, p3353_1]
                                    · have p3353_0 := h3353c.1
                                      have p3353_1 := h3353c.2.1
                                      have p3353_2 := h3353c.2.2.1
                                      have p3353_3 := h3353c.2.2.2
                                      linarith only [h3095, h3302, hc23, hlam, hphi, ht34, ht45, p3353_1, u5elo0]
                                    · have p3353_0 := h3353c.1
                                      have p3353_1 := h3353c.2.1
                                      have p3353_2 := h3353c.2.2.1
                                      have p3353_3 := h3353c.2.2.2
                                      linarith only [h3301, hlam, p3353_1]
                                    · have p3353_0 := h3353c.1
                                      have p3353_1 := h3353c.2.1
                                      have p3353_2 := h3353c.2.2.1
                                      have p3353_3 := h3353c.2.2.2
                                      linarith only [hlam, p3353_0]
                                  · linarith only [h3095, h3101, h3302, h3352, hc23, hlam, hphi, ht34, ht45, u5elo4]
                      · linarith only [h0, h3100, h3248, h3304, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                    · linarith only [h0, h3099, h3303, hlam]
                  · linarith only [h0, h3098, h3302, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3385 | h3385
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3386 | h3386
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3387 | h3387
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3388 | h3388
                        · linarith only [h3095, h3101, h3388, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3390 | h3390
                          · linarith only [h3096, h3301, h3390, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3392 | h3392
                            · linarith only [h3095, h3101, h3385, h3392, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3394 | h3394
                              · linarith only [h3095, h3101, h3301, h3385, h3394, hc35, hlam, hphi, u5elo4]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3396 | h3396
                                · linarith only [h3096, h3301, h3386, h3396, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3398 | h3398
                                  · rcases h0bigk with h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c
                                    · have p3399_0 := h3399c.1
                                      have p3399_1 := h3399c.2.1
                                      have p3399_2 := h3399c.2.2.1
                                      have p3399_3 := h3399c.2.2.2
                                      linarith only [hlam, p3399_0]
                                    · have p3399_0 := h3399c.1
                                      have p3399_1 := h3399c.2.1
                                      have p3399_2 := h3399c.2.2.1
                                      have p3399_3 := h3399c.2.2.2
                                      linarith only [h0, hlam, p3399_1]
                                    · have p3399_0 := h3399c.1
                                      have p3399_1 := h3399c.2.1
                                      have p3399_2 := h3399c.2.2.1
                                      have p3399_3 := h3399c.2.2.2
                                      linarith only [h0, h3095, h3385, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3399_1]
                                    · have p3399_0 := h3399c.1
                                      have p3399_1 := h3399c.2.1
                                      have p3399_2 := h3399c.2.2.1
                                      have p3399_3 := h3399c.2.2.2
                                      linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3399_1]
                                    · have p3399_0 := h3399c.1
                                      have p3399_1 := h3399c.2.1
                                      have p3399_2 := h3399c.2.2.1
                                      have p3399_3 := h3399c.2.2.2
                                      linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p3399_1]
                                    · have p3399_0 := h3399c.1
                                      have p3399_1 := h3399c.2.1
                                      have p3399_2 := h3399c.2.2.1
                                      have p3399_3 := h3399c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p3399_1]
                                    · have p3399_0 := h3399c.1
                                      have p3399_1 := h3399c.2.1
                                      have p3399_2 := h3399c.2.2.1
                                      have p3399_3 := h3399c.2.2.2
                                      linarith only [hlam, p3399_0]
                                    · have p3399_0 := h3399c.1
                                      have p3399_1 := h3399c.2.1
                                      have p3399_2 := h3399c.2.2.1
                                      have p3399_3 := h3399c.2.2.2
                                      rcases p3399_3 (m.d 0 1) (by simp) with h3407 | h3407
                                      · linarith only [h0, h3407, hlam]
                                      · linarith only [h3095, h3407, hlam]
                                    · have p3399_0 := h3399c.1
                                      have p3399_1 := h3399c.2.1
                                      have p3399_2 := h3399c.2.2.1
                                      have p3399_3 := h3399c.2.2.2
                                      rcases p3399_3 (m.d 0 1) (by simp) with h3410 | h3410
                                      · linarith only [h0, h3410, hlam]
                                      · linarith only [h3096, h3410, hlam]
                                    · have p3399_0 := h3399c.1
                                      have p3399_1 := h3399c.2.1
                                      have p3399_2 := h3399c.2.2.1
                                      have p3399_3 := h3399c.2.2.2
                                      rcases p3399_3 (m.d 0 1) (by simp) with h3413 | h3413
                                      · linarith only [h0, h3413, hlam]
                                      · linarith only [h3097, h3413, hlam]
                                    · have p3399_0 := h3399c.1
                                      have p3399_1 := h3399c.2.1
                                      have p3399_2 := h3399c.2.2.1
                                      have p3399_3 := h3399c.2.2.2
                                      linarith only [h3095, hlam, p3399_1]
                                    · have p3399_0 := h3399c.1
                                      have p3399_1 := h3399c.2.1
                                      have p3399_2 := h3399c.2.2.1
                                      have p3399_3 := h3399c.2.2.2
                                      linarith only [h3098, hlam, p3399_1]
                                    · have p3399_0 := h3399c.1
                                      have p3399_1 := h3399c.2.1
                                      have p3399_2 := h3399c.2.2.1
                                      have p3399_3 := h3399c.2.2.2
                                      linarith only [hlam, p3399_0]
                                    · have p3399_0 := h3399c.1
                                      have p3399_1 := h3399c.2.1
                                      have p3399_2 := h3399c.2.2.1
                                      have p3399_3 := h3399c.2.2.2
                                      linarith only [h3101, hlam, p3399_1]
                                    · have p3399_0 := h3399c.1
                                      have p3399_1 := h3399c.2.1
                                      have p3399_2 := h3399c.2.2.1
                                      have p3399_3 := h3399c.2.2.2
                                      linarith only [h3248, hlam, p3399_1]
                                    · have p3399_0 := h3399c.1
                                      have p3399_1 := h3399c.2.1
                                      have p3399_2 := h3399c.2.2.1
                                      have p3399_3 := h3399c.2.2.2
                                      linarith only [h3096, hlam, p3399_0]
                                    · have p3399_0 := h3399c.1
                                      have p3399_1 := h3399c.2.1
                                      have p3399_2 := h3399c.2.2.1
                                      have p3399_3 := h3399c.2.2.2
                                      linarith only [h3099, hlam, p3399_0]
                                    · have p3399_0 := h3399c.1
                                      have p3399_1 := h3399c.2.1
                                      have p3399_2 := h3399c.2.2.1
                                      have p3399_3 := h3399c.2.2.2
                                      linarith only [h3095, h3301, h3385, hc23, hlam, hphi, ht34, ht45, p3399_1, u5elo0]
                                    · have p3399_0 := h3399c.1
                                      have p3399_1 := h3399c.2.1
                                      have p3399_2 := h3399c.2.2.1
                                      have p3399_3 := h3399c.2.2.2
                                      linarith only [hlam, p3399_0]
                                    · have p3399_0 := h3399c.1
                                      have p3399_1 := h3399c.2.1
                                      have p3399_2 := h3399c.2.2.1
                                      have p3399_3 := h3399c.2.2.2
                                      linarith only [h3301, hlam, p3399_0]
                                    · have p3399_0 := h3399c.1
                                      have p3399_1 := h3399c.2.1
                                      have p3399_2 := h3399c.2.2.1
                                      have p3399_3 := h3399c.2.2.2
                                      linarith only [h3097, hlam, p3399_0]
                                    · have p3399_0 := h3399c.1
                                      have p3399_1 := h3399c.2.1
                                      have p3399_2 := h3399c.2.2.1
                                      have p3399_3 := h3399c.2.2.2
                                      linarith only [h3100, hlam, p3399_1]
                                    · have p3399_0 := h3399c.1
                                      have p3399_1 := h3399c.2.1
                                      have p3399_2 := h3399c.2.2.1
                                      have p3399_3 := h3399c.2.2.2
                                      linarith only [h3095, h3248, h3385, hc23, hlam, hphi, ht34, ht45, p3399_1, u5elo3]
                                    · have p3399_0 := h3399c.1
                                      have p3399_1 := h3399c.2.1
                                      have p3399_2 := h3399c.2.2.1
                                      have p3399_3 := h3399c.2.2.2
                                      linarith only [h3248, hc04, hlam, hphi, ht45, p3399_1, u5elo3]
                                    · have p3399_0 := h3399c.1
                                      have p3399_1 := h3399c.2.1
                                      have p3399_2 := h3399c.2.2.1
                                      have p3399_3 := h3399c.2.2.2
                                      linarith only [hlam, p3399_0]
                                  · linarith only [h3095, h3101, h3385, h3398, hc23, hlam, hphi, ht34, ht45, u5elo4]
                      · linarith only [h0, h3387, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                    · linarith only [h0, h3099, h3386, hlam]
                  · linarith only [h0, h3098, h3385, hlam]
          · linarith only [h0, h3095, h3100, hc13, hlam, hphi, ht34, ht45, u5elo2]
        · linarith only [h0, h3096, h3099, hlam]
      · linarith only [h0, h3095, h3098, hlam]
    · linarith only [h3095, h3097, hc13, hlam, hphi, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h3439 | h3439
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3440 | h3440
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3441 | h3441
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3442 | h3442
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3443 | h3443
            · linarith only [h3095, h3096, h3443, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3445 | h3445
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3446 | h3446
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3447 | h3447
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3448 | h3448
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3449 | h3449
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3450 | h3450
                        · linarith only [h3095, h3096, h3443, h3450, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3452 | h3452
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3453 | h3453
                            · linarith only [h3095, h3096, h3440, h3450, h3453, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3455 | h3455
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3456 | h3456
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3457 | h3457
                                  · rcases h0bigk with h3458c | h3458c | h3458c | h3458c | h3458c | h3458c | h3458c | h3458c | h3458c | h3458c | h3458c | h3458c | h3458c | h3458c | h3458c | h3458c | h3458c | h3458c | h3458c | h3458c | h3458c | h3458c | h3458c | h3458c | h3458c
                                    · have p3458_0 := h3458c.1
                                      have p3458_1 := h3458c.2.1
                                      have p3458_2 := h3458c.2.2.1
                                      have p3458_3 := h3458c.2.2.2
                                      linarith only [hlam, p3458_0]
                                    · have p3458_0 := h3458c.1
                                      have p3458_1 := h3458c.2.1
                                      have p3458_2 := h3458c.2.2.1
                                      have p3458_3 := h3458c.2.2.2
                                      linarith only [h0, hlam, p3458_1]
                                    · have p3458_0 := h3458c.1
                                      have p3458_1 := h3458c.2.1
                                      have p3458_2 := h3458c.2.2.1
                                      have p3458_3 := h3458c.2.2.2
                                      linarith only [h3096, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3458_1]
                                    · have p3458_0 := h3458c.1
                                      have p3458_1 := h3458c.2.1
                                      have p3458_2 := h3458c.2.2.1
                                      have p3458_3 := h3458c.2.2.2
                                      linarith only [h3096, hlam, p3458_1]
                                    · have p3458_0 := h3458c.1
                                      have p3458_1 := h3458c.2.1
                                      have p3458_2 := h3458c.2.2.1
                                      have p3458_3 := h3458c.2.2.2
                                      linarith only [h3096, h3450, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3458_1]
                                    · have p3458_0 := h3458c.1
                                      have p3458_1 := h3458c.2.1
                                      have p3458_2 := h3458c.2.2.1
                                      have p3458_3 := h3458c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p3458_1]
                                    · have p3458_0 := h3458c.1
                                      have p3458_1 := h3458c.2.1
                                      have p3458_2 := h3458c.2.2.1
                                      have p3458_3 := h3458c.2.2.2
                                      linarith only [hlam, p3458_0]
                                    · have p3458_0 := h3458c.1
                                      have p3458_1 := h3458c.2.1
                                      have p3458_2 := h3458c.2.2.1
                                      have p3458_3 := h3458c.2.2.2
                                      linarith only [h0, h3095, h3447, h3455, h3457, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3458_1]
                                    · have p3458_0 := h3458c.1
                                      have p3458_1 := h3458c.2.1
                                      have p3458_2 := h3458c.2.2.1
                                      have p3458_3 := h3458c.2.2.2
                                      linarith only [h0, h3095, h3096, h3447, h3455, h3457, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3458_1]
                                    · have p3458_0 := h3458c.1
                                      have p3458_1 := h3458c.2.1
                                      have p3458_2 := h3458c.2.2.1
                                      have p3458_3 := h3458c.2.2.2
                                      rcases p3458_3 (m.d 0 1) (by simp) with h3468 | h3468
                                      · linarith only [h0, h3468, hlam]
                                      · linarith only [h3439, h3468, hlam]
                                    · have p3458_0 := h3458c.1
                                      have p3458_1 := h3458c.2.1
                                      have p3458_2 := h3458c.2.2.1
                                      have p3458_3 := h3458c.2.2.2
                                      linarith only [h3095, hlam, p3458_1]
                                    · have p3458_0 := h3458c.1
                                      have p3458_1 := h3458c.2.1
                                      have p3458_2 := h3458c.2.2.1
                                      have p3458_3 := h3458c.2.2.2
                                      linarith only [h3440, hlam, p3458_1]
                                    · have p3458_0 := h3458c.1
                                      have p3458_1 := h3458c.2.1
                                      have p3458_2 := h3458c.2.2.1
                                      have p3458_3 := h3458c.2.2.2
                                      linarith only [hlam, p3458_0]
                                    · have p3458_0 := h3458c.1
                                      have p3458_1 := h3458c.2.1
                                      have p3458_2 := h3458c.2.2.1
                                      have p3458_3 := h3458c.2.2.2
                                      linarith only [h3443, hlam, p3458_1]
                                    · have p3458_0 := h3458c.1
                                      have p3458_1 := h3458c.2.1
                                      have p3458_2 := h3458c.2.2.1
                                      have p3458_3 := h3458c.2.2.2
                                      linarith only [h3095, h3096, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p3458_1]
                                    · have p3458_0 := h3458c.1
                                      have p3458_1 := h3458c.2.1
                                      have p3458_2 := h3458c.2.2.1
                                      have p3458_3 := h3458c.2.2.2
                                      linarith only [h3095, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3458_1]
                                    · have p3458_0 := h3458c.1
                                      have p3458_1 := h3458c.2.1
                                      have p3458_2 := h3458c.2.2.1
                                      have p3458_3 := h3458c.2.2.2
                                      linarith only [h3441, hlam, p3458_0]
                                    · have p3458_0 := h3458c.1
                                      have p3458_1 := h3458c.2.1
                                      have p3458_2 := h3458c.2.2.1
                                      have p3458_3 := h3458c.2.2.2
                                      linarith only [h3096, h3450, hc03, hc34, hlam, hphi, p3458_1]
                                    · have p3458_0 := h3458c.1
                                      have p3458_1 := h3458c.2.1
                                      have p3458_2 := h3458c.2.2.1
                                      have p3458_3 := h3458c.2.2.2
                                      linarith only [hlam, p3458_0]
                                    · have p3458_0 := h3458c.1
                                      have p3458_1 := h3458c.2.1
                                      have p3458_2 := h3458c.2.2.1
                                      have p3458_3 := h3458c.2.2.2
                                      rcases p3458_3 (m.d 0 1) (by simp) with h3480 | h3480
                                      · linarith only [h3096, h3480, hlam]
                                      · linarith only [h3439, h3480, hlam]
                                    · have p3458_0 := h3458c.1
                                      have p3458_1 := h3458c.2.1
                                      have p3458_2 := h3458c.2.2.1
                                      have p3458_3 := h3458c.2.2.2
                                      linarith only [h3439, hlam, p3458_0]
                                    · have p3458_0 := h3458c.1
                                      have p3458_1 := h3458c.2.1
                                      have p3458_2 := h3458c.2.2.1
                                      have p3458_3 := h3458c.2.2.2
                                      linarith only [h3442, hlam, p3458_1]
                                    · have p3458_0 := h3458c.1
                                      have p3458_1 := h3458c.2.1
                                      have p3458_2 := h3458c.2.2.1
                                      have p3458_3 := h3458c.2.2.2
                                      linarith only [h3445, hlam, p3458_0]
                                    · have p3458_0 := h3458c.1
                                      have p3458_1 := h3458c.2.1
                                      have p3458_2 := h3458c.2.2.1
                                      have p3458_3 := h3458c.2.2.2
                                      linarith only [h3446, hlam, p3458_1]
                                    · have p3458_0 := h3458c.1
                                      have p3458_1 := h3458c.2.1
                                      have p3458_2 := h3458c.2.2.1
                                      have p3458_3 := h3458c.2.2.2
                                      linarith only [hlam, p3458_0]
                                  · linarith only [h3095, h3096, h3447, h3450, h3455, h3457, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                                · linarith only [h3096, h3439, h3452, h3453, h3455, h3456, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h3095, h3096, h3445, h3450, h3455, hc23, hc34, hlam, hphi]
                          · linarith only [h3096, h3452, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                      · linarith only [h0, h3449, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                    · linarith only [h0, h3441, h3448, hlam]
                  · linarith only [h0, h3440, h3447, hlam]
                · linarith only [h3095, h3096, h3446, hc13, hlam, hphi, ht34, ht45, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3496 | h3496
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3497 | h3497
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3498 | h3498
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3499 | h3499
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3500 | h3500
                        · linarith only [h3095, h3445, h3500, hc34, hlam, hphi, ht45, u5elo3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3502 | h3502
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3503 | h3503
                            · linarith only [h3095, h3096, h3445, h3497, h3500, h3503, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3505 | h3505
                              · linarith only [h3095, h3096, h3445, h3497, h3498, h3505, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3507 | h3507
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3508 | h3508
                                  · rcases h0bigk with h3509c | h3509c | h3509c | h3509c | h3509c | h3509c | h3509c | h3509c | h3509c | h3509c | h3509c | h3509c | h3509c | h3509c | h3509c | h3509c | h3509c | h3509c | h3509c | h3509c | h3509c | h3509c | h3509c | h3509c | h3509c
                                    · have p3509_0 := h3509c.1
                                      have p3509_1 := h3509c.2.1
                                      have p3509_2 := h3509c.2.2.1
                                      have p3509_3 := h3509c.2.2.2
                                      linarith only [hlam, p3509_0]
                                    · have p3509_0 := h3509c.1
                                      have p3509_1 := h3509c.2.1
                                      have p3509_2 := h3509c.2.2.1
                                      have p3509_3 := h3509c.2.2.2
                                      linarith only [h0, hlam, p3509_1]
                                    · have p3509_0 := h3509c.1
                                      have p3509_1 := h3509c.2.1
                                      have p3509_2 := h3509c.2.2.1
                                      have p3509_3 := h3509c.2.2.2
                                      linarith only [h3096, h3500, hc03, hc34, hlam, hphi, p3509_1]
                                    · have p3509_0 := h3509c.1
                                      have p3509_1 := h3509c.2.1
                                      have p3509_2 := h3509c.2.2.1
                                      have p3509_3 := h3509c.2.2.2
                                      linarith only [h3096, hlam, p3509_1]
                                    · have p3509_0 := h3509c.1
                                      have p3509_1 := h3509c.2.1
                                      have p3509_2 := h3509c.2.2.1
                                      have p3509_3 := h3509c.2.2.2
                                      linarith only [h3096, h3500, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3509_1]
                                    · have p3509_0 := h3509c.1
                                      have p3509_1 := h3509c.2.1
                                      have p3509_2 := h3509c.2.2.1
                                      have p3509_3 := h3509c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p3509_1]
                                    · have p3509_0 := h3509c.1
                                      have p3509_1 := h3509c.2.1
                                      have p3509_2 := h3509c.2.2.1
                                      have p3509_3 := h3509c.2.2.2
                                      linarith only [hlam, p3509_0]
                                    · have p3509_0 := h3509c.1
                                      have p3509_1 := h3509c.2.1
                                      have p3509_2 := h3509c.2.2.1
                                      have p3509_3 := h3509c.2.2.2
                                      rcases p3509_3 (m.d 0 1) (by simp) with h3517 | h3517
                                      · linarith only [h0, h3517, hlam]
                                      · linarith only [h3095, h3517, hlam]
                                    · have p3509_0 := h3509c.1
                                      have p3509_1 := h3509c.2.1
                                      have p3509_2 := h3509c.2.2.1
                                      have p3509_3 := h3509c.2.2.2
                                      linarith only [h0, h3096, h3439, h3499, h3505, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3509_1]
                                    · have p3509_0 := h3509c.1
                                      have p3509_1 := h3509c.2.1
                                      have p3509_2 := h3509c.2.2.1
                                      have p3509_3 := h3509c.2.2.2
                                      rcases p3509_3 (m.d 0 1) (by simp) with h3521 | h3521
                                      · linarith only [h0, h3521, hlam]
                                      · linarith only [h3439, h3521, hlam]
                                    · have p3509_0 := h3509c.1
                                      have p3509_1 := h3509c.2.1
                                      have p3509_2 := h3509c.2.2.1
                                      have p3509_3 := h3509c.2.2.2
                                      linarith only [h3095, hlam, p3509_1]
                                    · have p3509_0 := h3509c.1
                                      have p3509_1 := h3509c.2.1
                                      have p3509_2 := h3509c.2.2.1
                                      have p3509_3 := h3509c.2.2.2
                                      linarith only [h3440, hlam, p3509_1]
                                    · have p3509_0 := h3509c.1
                                      have p3509_1 := h3509c.2.1
                                      have p3509_2 := h3509c.2.2.1
                                      have p3509_3 := h3509c.2.2.2
                                      linarith only [hlam, p3509_0]
                                    · have p3509_0 := h3509c.1
                                      have p3509_1 := h3509c.2.1
                                      have p3509_2 := h3509c.2.2.1
                                      have p3509_3 := h3509c.2.2.2
                                      linarith only [h3443, hlam, p3509_1]
                                    · have p3509_0 := h3509c.1
                                      have p3509_1 := h3509c.2.1
                                      have p3509_2 := h3509c.2.2.1
                                      have p3509_3 := h3509c.2.2.2
                                      linarith only [h3445, hlam, p3509_1]
                                    · have p3509_0 := h3509c.1
                                      have p3509_1 := h3509c.2.1
                                      have p3509_2 := h3509c.2.2.1
                                      have p3509_3 := h3509c.2.2.2
                                      linarith only [h3439, h3499, h3505, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3509_1]
                                    · have p3509_0 := h3509c.1
                                      have p3509_1 := h3509c.2.1
                                      have p3509_2 := h3509c.2.2.1
                                      have p3509_3 := h3509c.2.2.2
                                      linarith only [h3441, hlam, p3509_0]
                                    · have p3509_0 := h3509c.1
                                      have p3509_1 := h3509c.2.1
                                      have p3509_2 := h3509c.2.2.1
                                      have p3509_3 := h3509c.2.2.2
                                      linarith only [h3095, h3096, h3497, h3500, hc23, hc34, hlam, hphi, p3509_1]
                                    · have p3509_0 := h3509c.1
                                      have p3509_1 := h3509c.2.1
                                      have p3509_2 := h3509c.2.2.1
                                      have p3509_3 := h3509c.2.2.2
                                      linarith only [hlam, p3509_0]
                                    · have p3509_0 := h3509c.1
                                      have p3509_1 := h3509c.2.1
                                      have p3509_2 := h3509c.2.2.1
                                      have p3509_3 := h3509c.2.2.2
                                      linarith only [h3096, h3439, h3499, h3500, h3505, hc23, hc34, hlam, hphi, p3509_1]
                                    · have p3509_0 := h3509c.1
                                      have p3509_1 := h3509c.2.1
                                      have p3509_2 := h3509c.2.2.1
                                      have p3509_3 := h3509c.2.2.2
                                      linarith only [h3439, hlam, p3509_0]
                                    · have p3509_0 := h3509c.1
                                      have p3509_1 := h3509c.2.1
                                      have p3509_2 := h3509c.2.2.1
                                      have p3509_3 := h3509c.2.2.2
                                      linarith only [h3442, hlam, p3509_1]
                                    · have p3509_0 := h3509c.1
                                      have p3509_1 := h3509c.2.1
                                      have p3509_2 := h3509c.2.2.1
                                      have p3509_3 := h3509c.2.2.2
                                      linarith only [h3095, h3497, hc23, hlam, hphi, ht34, ht45, p3509_1, u5elo0]
                                    · have p3509_0 := h3509c.1
                                      have p3509_1 := h3509c.2.1
                                      have p3509_2 := h3509c.2.2.1
                                      have p3509_3 := h3509c.2.2.2
                                      linarith only [h3496, hlam, p3509_1]
                                    · have p3509_0 := h3509c.1
                                      have p3509_1 := h3509c.2.1
                                      have p3509_2 := h3509c.2.2.1
                                      have p3509_3 := h3509c.2.2.2
                                      linarith only [hlam, p3509_0]
                                  · linarith only [h3096, h3499, h3500, h3507, h3508, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
                                · linarith only [h3096, h3439, h3500, h3502, h3503, h3507, hc23, hc34, hlam, hphi]
                          · linarith only [h3096, h3502, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                      · linarith only [h0, h3095, h3497, h3499, hc23, hlam, hphi, ht34, ht45, u5elo2]
                    · linarith only [h0, h3441, h3498, hlam]
                  · linarith only [h0, h3440, h3497, hlam]
                · linarith only [h3095, h3096, h3496, hc13, hlam, hphi, ht34, ht45, u5elo4]
          · linarith only [h3441, h3442, hc24, hlam, hphi, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3547 | h3547
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3548 | h3548
            · linarith only [h0, h3095, h3441, h3548, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3550 | h3550
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3551 | h3551
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3552 | h3552
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3553 | h3553
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3554 | h3554
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3555 | h3555
                        · linarith only [h0, h3095, h3441, h3548, h3553, h3555, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3557 | h3557
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3558 | h3558
                            · linarith only [h0, h3095, h3441, h3552, h3553, h3555, h3558, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3560 | h3560
                              · linarith only [h0, h3095, h3441, h3552, h3553, h3560, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h0, h3095, h3441, h3550, h3553, h3560, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h0, h3095, h3441, h3553, h3557, hc13, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h3441, h3553, h3554, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3565 | h3565
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3566 | h3566
                        · linarith only [h0, h3095, h3553, h3566, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3568 | h3568
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3569 | h3569
                            · linarith only [h0, h3095, h3552, h3553, h3566, h3569, hlam]
                            · linarith only [h0, h3095, h3553, h3569, hc13, hc34, hlam, hphi]
                          · linarith only [h0, h3095, h3552, h3553, h3568, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h3095, h3552, h3565, hc23, hlam, hphi, ht34, ht45, u5elo2]
                  · linarith only [h0, h3095, h3440, h3441, h3552, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h3095, h3096, h3551, hc13, hlam, hphi, ht34, ht45, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3576 | h3576
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3577 | h3577
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3578 | h3578
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3579 | h3579
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3580 | h3580
                        · linarith only [h0, h3095, h3441, h3578, h3580, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3582 | h3582
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3583 | h3583
                            · linarith only [h0, h3095, h3441, h3577, h3578, h3580, h3583, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3585 | h3585
                              · linarith only [h0, h3095, h3441, h3550, h3577, h3578, h3585, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3587 | h3587
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3588 | h3588
                                  · rcases h0bigk with h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c
                                    · have p3589_0 := h3589c.1
                                      have p3589_1 := h3589c.2.1
                                      have p3589_2 := h3589c.2.2.1
                                      have p3589_3 := h3589c.2.2.2
                                      linarith only [hlam, p3589_0]
                                    · have p3589_0 := h3589c.1
                                      have p3589_1 := h3589c.2.1
                                      have p3589_2 := h3589c.2.2.1
                                      have p3589_3 := h3589c.2.2.2
                                      linarith only [h0, hlam, p3589_1]
                                    · have p3589_0 := h3589c.1
                                      have p3589_1 := h3589c.2.1
                                      have p3589_2 := h3589c.2.2.1
                                      have p3589_3 := h3589c.2.2.2
                                      linarith only [h0, h3441, h3578, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3589_1]
                                    · have p3589_0 := h3589c.1
                                      have p3589_1 := h3589c.2.1
                                      have p3589_2 := h3589c.2.2.1
                                      have p3589_3 := h3589c.2.2.2
                                      linarith only [h3096, hlam, p3589_1]
                                    · have p3589_0 := h3589c.1
                                      have p3589_1 := h3589c.2.1
                                      have p3589_2 := h3589c.2.2.1
                                      have p3589_3 := h3589c.2.2.2
                                      linarith only [h0, h3441, h3578, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p3589_1]
                                    · have p3589_0 := h3589c.1
                                      have p3589_1 := h3589c.2.1
                                      have p3589_2 := h3589c.2.2.1
                                      have p3589_3 := h3589c.2.2.2
                                      linarith only [h3441, h3578, hc01, hc12, hlam, hphi, p3589_1]
                                    · have p3589_0 := h3589c.1
                                      have p3589_1 := h3589c.2.1
                                      have p3589_2 := h3589c.2.2.1
                                      have p3589_3 := h3589c.2.2.2
                                      linarith only [hlam, p3589_0]
                                    · have p3589_0 := h3589c.1
                                      have p3589_1 := h3589c.2.1
                                      have p3589_2 := h3589c.2.2.1
                                      have p3589_3 := h3589c.2.2.2
                                      linarith only [h3095, h3441, h3578, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3589_1]
                                    · have p3589_0 := h3589c.1
                                      have p3589_1 := h3589c.2.1
                                      have p3589_2 := h3589c.2.2.1
                                      have p3589_3 := h3589c.2.2.2
                                      linarith only [h3441, hlam, p3589_1]
                                    · have p3589_0 := h3589c.1
                                      have p3589_1 := h3589c.2.1
                                      have p3589_2 := h3589c.2.2.1
                                      have p3589_3 := h3589c.2.2.2
                                      linarith only [h3439, h3441, h3578, h3579, h3585, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3589_1]
                                    · have p3589_0 := h3589c.1
                                      have p3589_1 := h3589c.2.1
                                      have p3589_2 := h3589c.2.2.1
                                      have p3589_3 := h3589c.2.2.2
                                      linarith only [h3095, hlam, p3589_1]
                                    · have p3589_0 := h3589c.1
                                      have p3589_1 := h3589c.2.1
                                      have p3589_2 := h3589c.2.2.1
                                      have p3589_3 := h3589c.2.2.2
                                      linarith only [h3440, hlam, p3589_1]
                                    · have p3589_0 := h3589c.1
                                      have p3589_1 := h3589c.2.1
                                      have p3589_2 := h3589c.2.2.1
                                      have p3589_3 := h3589c.2.2.2
                                      linarith only [hlam, p3589_0]
                                    · have p3589_0 := h3589c.1
                                      have p3589_1 := h3589c.2.1
                                      have p3589_2 := h3589c.2.2.1
                                      have p3589_3 := h3589c.2.2.2
                                      linarith only [h3548, hlam, p3589_1]
                                    · have p3589_0 := h3589c.1
                                      have p3589_1 := h3589c.2.1
                                      have p3589_2 := h3589c.2.2.1
                                      have p3589_3 := h3589c.2.2.2
                                      linarith only [h3550, hlam, p3589_1]
                                    · have p3589_0 := h3589c.1
                                      have p3589_1 := h3589c.2.1
                                      have p3589_2 := h3589c.2.2.1
                                      have p3589_3 := h3589c.2.2.2
                                      linarith only [h3439, h3579, h3585, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3589_1]
                                    · have p3589_0 := h3589c.1
                                      have p3589_1 := h3589c.2.1
                                      have p3589_2 := h3589c.2.2.1
                                      have p3589_3 := h3589c.2.2.2
                                      linarith only [h3441, h3578, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3589_1]
                                    · have p3589_0 := h3589c.1
                                      have p3589_1 := h3589c.2.1
                                      have p3589_2 := h3589c.2.2.1
                                      have p3589_3 := h3589c.2.2.2
                                      linarith only [h3095, h3441, h3578, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3589_1]
                                    · have p3589_0 := h3589c.1
                                      have p3589_1 := h3589c.2.1
                                      have p3589_2 := h3589c.2.2.1
                                      have p3589_3 := h3589c.2.2.2
                                      linarith only [hlam, p3589_0]
                                    · have p3589_0 := h3589c.1
                                      have p3589_1 := h3589c.2.1
                                      have p3589_2 := h3589c.2.2.1
                                      have p3589_3 := h3589c.2.2.2
                                      linarith only [h3439, h3441, h3578, h3579, h3585, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3589_1]
                                    · have p3589_0 := h3589c.1
                                      have p3589_1 := h3589c.2.1
                                      have p3589_2 := h3589c.2.2.1
                                      have p3589_3 := h3589c.2.2.2
                                      linarith only [h3439, hlam, p3589_0]
                                    · have p3589_0 := h3589c.1
                                      have p3589_1 := h3589c.2.1
                                      have p3589_2 := h3589c.2.2.1
                                      have p3589_3 := h3589c.2.2.2
                                      linarith only [h3547, hlam, p3589_1]
                                    · have p3589_0 := h3589c.1
                                      have p3589_1 := h3589c.2.1
                                      have p3589_2 := h3589c.2.2.1
                                      have p3589_3 := h3589c.2.2.2
                                      linarith only [h3095, hc13, hlam, hphi, ht34, ht45, p3589_1, u5elo0]
                                    · have p3589_0 := h3589c.1
                                      have p3589_1 := h3589c.2.1
                                      have p3589_2 := h3589c.2.2.1
                                      have p3589_3 := h3589c.2.2.2
                                      linarith only [h3576, hlam, p3589_1]
                                    · have p3589_0 := h3589c.1
                                      have p3589_1 := h3589c.2.1
                                      have p3589_2 := h3589c.2.2.1
                                      have p3589_3 := h3589c.2.2.2
                                      linarith only [hlam, p3589_0]
                                  · linarith only [h3096, h3439, h3579, h3580, h3587, h3588, hlam]
                                · linarith only [h0, h3439, h3441, h3582, h3587, hlam]
                          · linarith only [h0, h3095, h3441, h3578, h3582, hc13, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h3095, h3441, h3577, h3578, h3579, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3619 | h3619
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3620 | h3620
                        · linarith only [h0, h3095, h3548, h3578, h3620, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3622 | h3622
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3623 | h3623
                            · linarith only [h0, h3095, h3577, h3578, h3620, h3623, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h3095, h3577, h3578, h3623, hc23, hc34, hlam, hphi]
                          · linarith only [h0, h3095, h3577, h3578, h3622, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h3095, h3577, h3619, hc23, hlam, hphi, ht34, ht45, u5elo2]
                  · linarith only [h0, h3439, h3440, h3441, h3577, hc04, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h3095, h3096, h3576, hc13, hlam, hphi, ht34, ht45, u5elo4]
          · linarith only [h0, h3095, h3547, hc13, hlam, hphi, ht34, ht45, u5elo2]
      · linarith only [h0, h3095, h3440, hlam]
    · linarith only [h3095, h3439, hc13, hlam, hphi, ht34, ht45, u5elo1]

end R2N4
