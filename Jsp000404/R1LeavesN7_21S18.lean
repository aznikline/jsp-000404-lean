import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_21S17

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6944000 in
set_option maxHeartbeats 6944000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s1 m hb1 hb2 hb4 hb5 h0 h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h3079 | h3079
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3080 | h3080
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3081 | h3081
        · linarith only [h0, h1, h3081, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h3083 | h3083
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3084 | h3084
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3085 | h3085
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3086 | h3086
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3087 | h3087
                  · linarith only [h3081, h3083, h3086, h3087, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3089 | h3089
                    · linarith only [h0, h1, h3089, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h1, h3083, h3087, h3089, hc12, hc23, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3092 | h3092
                  · linarith only [h0, h1, h3081, h3092, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3094 | h3094
                    · linarith only [h0, h1, h3092, h3094, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h1, h3083, h3092, h3094, hc12, hc23, hlam, hphi]
              · linarith only [h1, h3080, h3085, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3098 | h3098
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3099 | h3099
                · linarith only [h3083, h3084, h3099, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3101 | h3101
                  · linarith only [h3081, h3083, h3101, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3103 | h3103
                    · linarith only [h0, h1, h3101, h3103, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                    · linarith only [h3083, h3084, h3103, hc12, hc25, hlam, hphi]
              · linarith only [h1, h3080, h3098, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3107 | h3107
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3108 | h3108
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3109 | h3109
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3110 | h3110
                  · linarith only [h0, h1, h3081, h3107, h3110, hc03, hlam, hphi, ht0b, ht5b, u5ehi0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3112 | h3112
                    · linarith only [h0, h1, h3083, h3107, h3110, h3112, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3114 | h3114
                      · linarith only [h1, h3079, h3110, h3112, h3114, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h3083, h3107, h3114, hc12, hc24, hlam, hphi]
                · linarith only [h3083, h3107, h3109, hlam]
              · linarith only [h1, h3079, h3083, h3107, h3108, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3119 | h3119
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3120 | h3120
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3121 | h3121
                  · linarith only [h0, h1, h3081, h3121, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3123 | h3123
                    · linarith only [h0, h1, h3083, h3121, h3123, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3125 | h3125
                      · linarith only [h0, h3107, h3125, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3127 | h3127
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3128 | h3128
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3129 | h3129
                            · linarith only [h1, h3079, h3121, h3129, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                            · linarith only [h1, h3079, h3120, h3121, h3123, h3129, hc12, hc23, hlam, hphi]
                          · linarith only [h1, h3080, h3128, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                        · linarith only [h1, h3079, h3120, h3127, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3134 | h3134
                  · linarith only [h0, h3081, h3134, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3136 | h3136
                    · linarith only [h0, h3083, h3136, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3138 | h3138
                      · linarith only [h0, h3107, h3138, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3140 | h3140
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3141 | h3141
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3142 | h3142
                            · linarith only [h3079, h3120, h3142, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3144 | h3144
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3145 | h3145
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3146 | h3146
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3147 | h3147
                                    · linarith only [h3079, h3120, h3140, h3147, hlam]
                                    · rcases h1bigk with h3149c | h3149c | h3149c | h3149c | h3149c | h3149c | h3149c | h3149c | h3149c | h3149c | h3149c | h3149c | h3149c | h3149c | h3149c | h3149c | h3149c | h3149c | h3149c | h3149c | h3149c | h3149c | h3149c | h3149c | h3149c
                                      · have p3149_0 := h3149c.1
                                        have p3149_1 := h3149c.2.1
                                        have p3149_2 := h3149c.2.2.1
                                        have p3149_3 := h3149c.2.2.2
                                        linarith only [hlam, p3149_0]
                                      · have p3149_0 := h3149c.1
                                        have p3149_1 := h3149c.2.1
                                        have p3149_2 := h3149c.2.2.1
                                        have p3149_3 := h3149c.2.2.2
                                        linarith only [h1, h3134, hc12, hc23, hlam, hphi, p3149_1]
                                      · have p3149_0 := h3149c.1
                                        have p3149_1 := h3149c.2.1
                                        have p3149_2 := h3149c.2.2.1
                                        have p3149_3 := h3149c.2.2.2
                                        linarith only [h1, hlam, p3149_0]
                                      · have p3149_0 := h3149c.1
                                        have p3149_1 := h3149c.2.1
                                        have p3149_2 := h3149c.2.2.1
                                        have p3149_3 := h3149c.2.2.2
                                        linarith only [h1, h3134, h3140, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3149_1, u4ehi3]
                                      · have p3149_0 := h3149c.1
                                        have p3149_1 := h3149c.2.1
                                        have p3149_2 := h3149c.2.2.1
                                        have p3149_3 := h3149c.2.2.2
                                        linarith only [h1, h3134, h3140, h3142, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3149_1, u4ehi3]
                                      · have p3149_0 := h3149c.1
                                        have p3149_1 := h3149c.2.1
                                        have p3149_2 := h3149c.2.2.1
                                        have p3149_3 := h3149c.2.2.2
                                        linarith only [h0, hlam, p3149_0]
                                      · have p3149_0 := h3149c.1
                                        have p3149_1 := h3149c.2.1
                                        have p3149_2 := h3149c.2.2.1
                                        have p3149_3 := h3149c.2.2.2
                                        linarith only [hlam, p3149_0]
                                      · have p3149_0 := h3149c.1
                                        have p3149_1 := h3149c.2.1
                                        have p3149_2 := h3149c.2.2.1
                                        have p3149_3 := h3149c.2.2.2
                                        linarith only [h3134, hlam, p3149_1]
                                      · have p3149_0 := h3149c.1
                                        have p3149_1 := h3149c.2.1
                                        have p3149_2 := h3149c.2.2.1
                                        have p3149_3 := h3149c.2.2.2
                                        linarith only [h3136, hlam, p3149_1]
                                      · have p3149_0 := h3149c.1
                                        have p3149_1 := h3149c.2.1
                                        have p3149_2 := h3149c.2.2.1
                                        have p3149_3 := h3149c.2.2.2
                                        linarith only [h3138, hlam, p3149_1]
                                      · have p3149_0 := h3149c.1
                                        have p3149_1 := h3149c.2.1
                                        have p3149_2 := h3149c.2.2.1
                                        have p3149_3 := h3149c.2.2.2
                                        linarith only [h0, h3134, hc12, hc23, hlam, hphi, p3149_1]
                                      · have p3149_0 := h3149c.1
                                        have p3149_1 := h3149c.2.1
                                        have p3149_2 := h3149c.2.2.1
                                        have p3149_3 := h3149c.2.2.2
                                        rcases p3149_3 (m.d 0 1) (by simp) with h3161 | h3161
                                        · linarith only [h1, h3161, hlam]
                                        · linarith only [h0, h3161, hlam]
                                      · have p3149_0 := h3149c.1
                                        have p3149_1 := h3149c.2.1
                                        have p3149_2 := h3149c.2.2.1
                                        have p3149_3 := h3149c.2.2.2
                                        linarith only [hlam, p3149_0]
                                      · have p3149_0 := h3149c.1
                                        have p3149_1 := h3149c.2.1
                                        have p3149_2 := h3149c.2.2.1
                                        have p3149_3 := h3149c.2.2.2
                                        rcases p3149_3 (m.d 0 1) (by simp) with h3165 | h3165
                                        · linarith only [h1, h3165, hlam]
                                        · linarith only [h3079, h3165, hlam]
                                      · have p3149_0 := h3149c.1
                                        have p3149_1 := h3149c.2.1
                                        have p3149_2 := h3149c.2.2.1
                                        have p3149_3 := h3149c.2.2.2
                                        rcases p3149_3 (m.d 0 1) (by simp) with h3168 | h3168
                                        · linarith only [h1, h3168, hlam]
                                        · linarith only [h3080, h3168, hlam]
                                      · have p3149_0 := h3149c.1
                                        have p3149_1 := h3149c.2.1
                                        have p3149_2 := h3149c.2.2.1
                                        have p3149_3 := h3149c.2.2.2
                                        linarith only [h3079, hlam, p3149_0]
                                      · have p3149_0 := h3149c.1
                                        have p3149_1 := h3149c.2.1
                                        have p3149_2 := h3149c.2.2.1
                                        have p3149_3 := h3149c.2.2.2
                                        linarith only [h3079, h3120, h3146, hc12, hc24, hlam, hphi, p3149_1]
                                      · have p3149_0 := h3149c.1
                                        have p3149_1 := h3149c.2.1
                                        have p3149_2 := h3149c.2.2.1
                                        have p3149_3 := h3149c.2.2.2
                                        linarith only [h3140, hlam, p3149_1]
                                      · have p3149_0 := h3149c.1
                                        have p3149_1 := h3149c.2.1
                                        have p3149_2 := h3149c.2.2.1
                                        have p3149_3 := h3149c.2.2.2
                                        linarith only [hlam, p3149_0]
                                      · have p3149_0 := h3149c.1
                                        have p3149_1 := h3149c.2.1
                                        have p3149_2 := h3149c.2.2.1
                                        have p3149_3 := h3149c.2.2.2
                                        linarith only [h3142, hlam, p3149_1]
                                      · have p3149_0 := h3149c.1
                                        have p3149_1 := h3149c.2.1
                                        have p3149_2 := h3149c.2.2.1
                                        have p3149_3 := h3149c.2.2.2
                                        linarith only [h3080, hlam, p3149_0]
                                      · have p3149_0 := h3149c.1
                                        have p3149_1 := h3149c.2.1
                                        have p3149_2 := h3149c.2.2.1
                                        have p3149_3 := h3149c.2.2.2
                                        linarith only [h1, h3080, h3134, hc12, hc23, hlam, hphi, p3149_1]
                                      · have p3149_0 := h3149c.1
                                        have p3149_1 := h3149c.2.1
                                        have p3149_2 := h3149c.2.2.1
                                        have p3149_3 := h3149c.2.2.2
                                        linarith only [h3141, hlam, p3149_0]
                                      · have p3149_0 := h3149c.1
                                        have p3149_1 := h3149c.2.1
                                        have p3149_2 := h3149c.2.2.1
                                        have p3149_3 := h3149c.2.2.2
                                        linarith only [h1, h3080, h3134, h3140, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3149_1, u4ehi3]
                                      · have p3149_0 := h3149c.1
                                        have p3149_1 := h3149c.2.1
                                        have p3149_2 := h3149c.2.2.1
                                        have p3149_3 := h3149c.2.2.2
                                        linarith only [hlam, p3149_0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3181 | h3181
                                    · linarith only [h3083, h3146, h3181, hc02, hc34, hlam, hphi, ht23]
                                    · rcases h1bigk with h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c
                                      · have p3183_0 := h3183c.1
                                        have p3183_1 := h3183c.2.1
                                        have p3183_2 := h3183c.2.2.1
                                        have p3183_3 := h3183c.2.2.2
                                        linarith only [hlam, p3183_0]
                                      · have p3183_0 := h3183c.1
                                        have p3183_1 := h3183c.2.1
                                        have p3183_2 := h3183c.2.2.1
                                        have p3183_3 := h3183c.2.2.2
                                        linarith only [h1, h3134, hc12, hc23, hlam, hphi, p3183_1]
                                      · have p3183_0 := h3183c.1
                                        have p3183_1 := h3183c.2.1
                                        have p3183_2 := h3183c.2.2.1
                                        have p3183_3 := h3183c.2.2.2
                                        linarith only [h1, hlam, p3183_0]
                                      · have p3183_0 := h3183c.1
                                        have p3183_1 := h3183c.2.1
                                        have p3183_2 := h3183c.2.2.1
                                        have p3183_3 := h3183c.2.2.2
                                        linarith only [h1, h3134, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3183_1, u4ehi1]
                                      · have p3183_0 := h3183c.1
                                        have p3183_1 := h3183c.2.1
                                        have p3183_2 := h3183c.2.2.1
                                        have p3183_3 := h3183c.2.2.2
                                        linarith only [h1, h3134, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3183_1, u5ehi1]
                                      · have p3183_0 := h3183c.1
                                        have p3183_1 := h3183c.2.1
                                        have p3183_2 := h3183c.2.2.1
                                        have p3183_3 := h3183c.2.2.2
                                        linarith only [h0, hlam, p3183_0]
                                      · have p3183_0 := h3183c.1
                                        have p3183_1 := h3183c.2.1
                                        have p3183_2 := h3183c.2.2.1
                                        have p3183_3 := h3183c.2.2.2
                                        linarith only [hlam, p3183_0]
                                      · have p3183_0 := h3183c.1
                                        have p3183_1 := h3183c.2.1
                                        have p3183_2 := h3183c.2.2.1
                                        have p3183_3 := h3183c.2.2.2
                                        linarith only [h3134, hlam, p3183_1]
                                      · have p3183_0 := h3183c.1
                                        have p3183_1 := h3183c.2.1
                                        have p3183_2 := h3183c.2.2.1
                                        have p3183_3 := h3183c.2.2.2
                                        linarith only [h3136, hlam, p3183_1]
                                      · have p3183_0 := h3183c.1
                                        have p3183_1 := h3183c.2.1
                                        have p3183_2 := h3183c.2.2.1
                                        have p3183_3 := h3183c.2.2.2
                                        linarith only [h3138, hlam, p3183_1]
                                      · have p3183_0 := h3183c.1
                                        have p3183_1 := h3183c.2.1
                                        have p3183_2 := h3183c.2.2.1
                                        have p3183_3 := h3183c.2.2.2
                                        linarith only [h0, h3134, hc12, hc23, hlam, hphi, p3183_1]
                                      · have p3183_0 := h3183c.1
                                        have p3183_1 := h3183c.2.1
                                        have p3183_2 := h3183c.2.2.1
                                        have p3183_3 := h3183c.2.2.2
                                        rcases p3183_3 (m.d 0 1) (by simp) with h3195 | h3195
                                        · linarith only [h1, h3195, hlam]
                                        · linarith only [h0, h3195, hlam]
                                      · have p3183_0 := h3183c.1
                                        have p3183_1 := h3183c.2.1
                                        have p3183_2 := h3183c.2.2.1
                                        have p3183_3 := h3183c.2.2.2
                                        linarith only [hlam, p3183_0]
                                      · have p3183_0 := h3183c.1
                                        have p3183_1 := h3183c.2.1
                                        have p3183_2 := h3183c.2.2.1
                                        have p3183_3 := h3183c.2.2.2
                                        rcases p3183_3 (m.d 0 1) (by simp) with h3199 | h3199
                                        · linarith only [h1, h3199, hlam]
                                        · linarith only [h3079, h3199, hlam]
                                      · have p3183_0 := h3183c.1
                                        have p3183_1 := h3183c.2.1
                                        have p3183_2 := h3183c.2.2.1
                                        have p3183_3 := h3183c.2.2.2
                                        rcases p3183_3 (m.d 0 1) (by simp) with h3202 | h3202
                                        · linarith only [h1, h3202, hlam]
                                        · linarith only [h3080, h3202, hlam]
                                      · have p3183_0 := h3183c.1
                                        have p3183_1 := h3183c.2.1
                                        have p3183_2 := h3183c.2.2.1
                                        have p3183_3 := h3183c.2.2.2
                                        linarith only [h3079, hlam, p3183_0]
                                      · have p3183_0 := h3183c.1
                                        have p3183_1 := h3183c.2.1
                                        have p3183_2 := h3183c.2.2.1
                                        have p3183_3 := h3183c.2.2.2
                                        linarith only [h1, h3080, h3134, h3142, hc12, hc23, hlam, hphi, p3183_1]
                                      · have p3183_0 := h3183c.1
                                        have p3183_1 := h3183c.2.1
                                        have p3183_2 := h3183c.2.2.1
                                        have p3183_3 := h3183c.2.2.2
                                        linarith only [h3140, hlam, p3183_1]
                                      · have p3183_0 := h3183c.1
                                        have p3183_1 := h3183c.2.1
                                        have p3183_2 := h3183c.2.2.1
                                        have p3183_3 := h3183c.2.2.2
                                        linarith only [hlam, p3183_0]
                                      · have p3183_0 := h3183c.1
                                        have p3183_1 := h3183c.2.1
                                        have p3183_2 := h3183c.2.2.1
                                        have p3183_3 := h3183c.2.2.2
                                        linarith only [h3142, hlam, p3183_1]
                                      · have p3183_0 := h3183c.1
                                        have p3183_1 := h3183c.2.1
                                        have p3183_2 := h3183c.2.2.1
                                        have p3183_3 := h3183c.2.2.2
                                        linarith only [h3080, hlam, p3183_0]
                                      · have p3183_0 := h3183c.1
                                        have p3183_1 := h3183c.2.1
                                        have p3183_2 := h3183c.2.2.1
                                        have p3183_3 := h3183c.2.2.2
                                        linarith only [h1, h3080, h3134, hc12, hc23, hlam, hphi, p3183_1]
                                      · have p3183_0 := h3183c.1
                                        have p3183_1 := h3183c.2.1
                                        have p3183_2 := h3183c.2.2.1
                                        have p3183_3 := h3183c.2.2.2
                                        linarith only [h3141, hlam, p3183_0]
                                      · have p3183_0 := h3183c.1
                                        have p3183_1 := h3183c.2.1
                                        have p3183_2 := h3183c.2.2.1
                                        have p3183_3 := h3183c.2.2.2
                                        linarith only [h1, h3080, h3134, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3183_1, u4ehi1]
                                      · have p3183_0 := h3183c.1
                                        have p3183_1 := h3183c.2.1
                                        have p3183_2 := h3183c.2.2.1
                                        have p3183_3 := h3183c.2.2.2
                                        linarith only [hlam, p3183_0]
                                · linarith only [h1, h3080, h3134, h3145, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                              · linarith only [h1, h3080, h3134, h3140, h3142, h3144, hlam]
                          · linarith only [h1, h3080, h3141, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                        · linarith only [h0, h1, h3140, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h3080, h3119, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3220 | h3220
        · linarith only [h0, h1, h3220, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h3222 | h3222
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3223 | h3223
            · linarith only [h0, h3080, h3223, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3225 | h3225
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3226 | h3226
                · linarith only [h0, h3080, h3222, h3226, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3228 | h3228
                  · linarith only [h0, h1, h3220, h3228, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3230 | h3230
                    · linarith only [h0, h1, h3228, h3230, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                    · linarith only [h3222, h3223, h3230, hc12, hc25, hlam, hphi]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3233 | h3233
                · linarith only [h3079, h3080, h3233, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3235 | h3235
                  · linarith only [h0, h1, h3225, h3235, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3237 | h3237
                    · linarith only [h0, h1, h3225, h3237, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h1, h3222, h3225, h3237, hc12, hc35, hlam, hphi, ht23]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3240 | h3240
            · linarith only [h3079, h3080, h3222, h3240, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3242 | h3242
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3243 | h3243
                · linarith only [h3079, h3080, h3243, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3245 | h3245
                  · linarith only [h0, h3220, h3245, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3247 | h3247
                    · linarith only [h0, h3222, h3247, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3249 | h3249
                      · linarith only [h0, h1, h3245, h3249, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3251 | h3251
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3252 | h3252
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3253 | h3253
                            · linarith only [h3079, h3080, h3222, h3243, h3245, h3252, h3253, hc02, hc23, hlam, hphi]
                            · linarith only [h3079, h3080, h3251, h3253, hc45, hlam, hphi, u4ehi3]
                          · linarith only [h1, h3079, h3251, h3252, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                        · linarith only [h1, h3079, h3251, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3258 | h3258
                · linarith only [h1, h3079, h3242, h3258, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3260 | h3260
                  · linarith only [h0, h1, h3242, h3260, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3262 | h3262
                    · linarith only [h0, h3222, h3262, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3264 | h3264
                      · linarith only [h1, h3079, h3242, h3262, h3264, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3266 | h3266
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3267 | h3267
                          · linarith only [h1, h3079, h3242, h3266, h3267, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                          · linarith only [h1, h3079, h3266, h3267, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                        · linarith only [h1, h3079, h3266, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3271 | h3271
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3272 | h3272
        · linarith only [h0, h1, h3272, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h3274 | h3274
          · linarith only [h0, h3079, h3274, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3276 | h3276
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3277 | h3277
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3278 | h3278
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3279 | h3279
                  · linarith only [h0, h1, h3272, h3279, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3281 | h3281
                    · linarith only [h0, h3274, h3276, h3281, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3283 | h3283
                      · linarith only [h0, h1, h3279, h3283, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h0, h1, h3276, h3279, h3283, hc12, hc23, hlam, hphi]
                · linarith only [h3079, h3271, h3278, hlam]
              · linarith only [h0, h1, h3276, h3277, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3288 | h3288
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3289 | h3289
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3290 | h3290
                  · linarith only [h0, h1, h3272, h3290, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3292 | h3292
                    · linarith only [h0, h1, h3290, h3292, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3294 | h3294
                      · linarith only [h0, h1, h3276, h3290, h3294, hc02, hc23, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3296 | h3296
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3297 | h3297
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3298 | h3298
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3299 | h3299
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3300 | h3300
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3301 | h3301
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3302 | h3302
                                    · rcases h1bigk with h3303c | h3303c | h3303c | h3303c | h3303c | h3303c | h3303c | h3303c | h3303c | h3303c | h3303c | h3303c | h3303c | h3303c | h3303c | h3303c | h3303c | h3303c | h3303c | h3303c | h3303c | h3303c | h3303c | h3303c | h3303c
                                      · have p3303_0 := h3303c.1
                                        have p3303_1 := h3303c.2.1
                                        have p3303_2 := h3303c.2.2.1
                                        have p3303_3 := h3303c.2.2.2
                                        linarith only [hlam, p3303_0]
                                      · have p3303_0 := h3303c.1
                                        have p3303_1 := h3303c.2.1
                                        have p3303_2 := h3303c.2.2.1
                                        have p3303_3 := h3303c.2.2.2
                                        linarith only [h3079, h3290, h3296, hc12, hc23, hlam, hphi, p3303_1]
                                      · have p3303_0 := h3303c.1
                                        have p3303_1 := h3303c.2.1
                                        have p3303_2 := h3303c.2.2.1
                                        have p3303_3 := h3303c.2.2.2
                                        linarith only [h1, hlam, p3303_0]
                                      · have p3303_0 := h3303c.1
                                        have p3303_1 := h3303c.2.1
                                        have p3303_2 := h3303c.2.2.1
                                        have p3303_3 := h3303c.2.2.2
                                        linarith only [h3079, hlam, p3303_0]
                                      · have p3303_0 := h3303c.1
                                        have p3303_1 := h3303c.2.1
                                        have p3303_2 := h3303c.2.2.1
                                        have p3303_3 := h3303c.2.2.2
                                        linarith only [h3079, h3290, h3296, h3297, h3302, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3303_1, u4ehi4]
                                      · have p3303_0 := h3303c.1
                                        have p3303_1 := h3303c.2.1
                                        have p3303_2 := h3303c.2.2.1
                                        have p3303_3 := h3303c.2.2.2
                                        linarith only [h0, hlam, p3303_0]
                                      · have p3303_0 := h3303c.1
                                        have p3303_1 := h3303c.2.1
                                        have p3303_2 := h3303c.2.2.1
                                        have p3303_3 := h3303c.2.2.2
                                        linarith only [hlam, p3303_0]
                                      · have p3303_0 := h3303c.1
                                        have p3303_1 := h3303c.2.1
                                        have p3303_2 := h3303c.2.2.1
                                        have p3303_3 := h3303c.2.2.2
                                        linarith only [h3290, hlam, p3303_1]
                                      · have p3303_0 := h3303c.1
                                        have p3303_1 := h3303c.2.1
                                        have p3303_2 := h3303c.2.2.1
                                        have p3303_3 := h3303c.2.2.2
                                        linarith only [h3292, hlam, p3303_1]
                                      · have p3303_0 := h3303c.1
                                        have p3303_1 := h3303c.2.1
                                        have p3303_2 := h3303c.2.2.1
                                        have p3303_3 := h3303c.2.2.2
                                        linarith only [h3294, hlam, p3303_1]
                                      · have p3303_0 := h3303c.1
                                        have p3303_1 := h3303c.2.1
                                        have p3303_2 := h3303c.2.2.1
                                        have p3303_3 := h3303c.2.2.2
                                        linarith only [h0, h3290, hc12, hc23, hlam, hphi, p3303_1]
                                      · have p3303_0 := h3303c.1
                                        have p3303_1 := h3303c.2.1
                                        have p3303_2 := h3303c.2.2.1
                                        have p3303_3 := h3303c.2.2.2
                                        rcases p3303_3 (m.d 0 1) (by simp) with h3315 | h3315
                                        · linarith only [h1, h3315, hlam]
                                        · linarith only [h0, h3315, hlam]
                                      · have p3303_0 := h3303c.1
                                        have p3303_1 := h3303c.2.1
                                        have p3303_2 := h3303c.2.2.1
                                        have p3303_3 := h3303c.2.2.2
                                        linarith only [hlam, p3303_0]
                                      · have p3303_0 := h3303c.1
                                        have p3303_1 := h3303c.2.1
                                        have p3303_2 := h3303c.2.2.1
                                        have p3303_3 := h3303c.2.2.2
                                        linarith only [h3079, h3271, h3290, h3297, h3302, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3303_1, u4ehi4]
                                      · have p3303_0 := h3303c.1
                                        have p3303_1 := h3303c.2.1
                                        have p3303_2 := h3303c.2.2.1
                                        have p3303_3 := h3303c.2.2.2
                                        rcases p3303_3 (m.d 0 1) (by simp) with h3320 | h3320
                                        · linarith only [h1, h3320, hlam]
                                        · linarith only [h3271, h3320, hlam]
                                      · have p3303_0 := h3303c.1
                                        have p3303_1 := h3303c.2.1
                                        have p3303_2 := h3303c.2.2.1
                                        have p3303_3 := h3303c.2.2.2
                                        linarith only [h3271, h3297, h3302, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3303_1, u4ehi4]
                                      · have p3303_0 := h3303c.1
                                        have p3303_1 := h3303c.2.1
                                        have p3303_2 := h3303c.2.2.1
                                        have p3303_3 := h3303c.2.2.2
                                        rcases p3303_3 (m.d 0 1) (by simp) with h3324 | h3324
                                        · linarith only [h3079, h3324, hlam]
                                        · linarith only [h0, h3324, hlam]
                                      · have p3303_0 := h3303c.1
                                        have p3303_1 := h3303c.2.1
                                        have p3303_2 := h3303c.2.2.1
                                        have p3303_3 := h3303c.2.2.2
                                        linarith only [h3296, hlam, p3303_1]
                                      · have p3303_0 := h3303c.1
                                        have p3303_1 := h3303c.2.1
                                        have p3303_2 := h3303c.2.2.1
                                        have p3303_3 := h3303c.2.2.2
                                        linarith only [hlam, p3303_0]
                                      · have p3303_0 := h3303c.1
                                        have p3303_1 := h3303c.2.1
                                        have p3303_2 := h3303c.2.2.1
                                        have p3303_3 := h3303c.2.2.2
                                        rcases p3303_3 (m.d 0 1) (by simp) with h3329 | h3329
                                        · linarith only [h3079, h3329, hlam]
                                        · linarith only [h3271, h3329, hlam]
                                      · have p3303_0 := h3303c.1
                                        have p3303_1 := h3303c.2.1
                                        have p3303_2 := h3303c.2.2.1
                                        have p3303_3 := h3303c.2.2.2
                                        linarith only [h3271, hlam, p3303_0]
                                      · have p3303_0 := h3303c.1
                                        have p3303_1 := h3303c.2.1
                                        have p3303_2 := h3303c.2.2.1
                                        have p3303_3 := h3303c.2.2.2
                                        linarith only [h1, h3271, h3290, hc12, hc23, hlam, hphi, p3303_1]
                                      · have p3303_0 := h3303c.1
                                        have p3303_1 := h3303c.2.1
                                        have p3303_2 := h3303c.2.2.1
                                        have p3303_3 := h3303c.2.2.2
                                        linarith only [h3297, hlam, p3303_0]
                                      · have p3303_0 := h3303c.1
                                        have p3303_1 := h3303c.2.1
                                        have p3303_2 := h3303c.2.2.1
                                        have p3303_3 := h3303c.2.2.2
                                        linarith only [h3298, hlam, p3303_0]
                                      · have p3303_0 := h3303c.1
                                        have p3303_1 := h3303c.2.1
                                        have p3303_2 := h3303c.2.2.1
                                        have p3303_3 := h3303c.2.2.2
                                        linarith only [hlam, p3303_0]
                                    · linarith only [h3079, h3271, h3290, h3296, h3298, h3302, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                                  · linarith only [h3079, h3271, h3290, h3296, h3298, h3301, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                                · linarith only [h3079, h3271, h3290, h3296, h3297, h3300, hlam]
                              · linarith only [h3079, h3271, h3290, h3296, h3299, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                            · linarith only [h3079, h3271, h3297, h3298, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                          · linarith only [h3079, h3271, h3296, h3297, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                        · linarith only [h1, h3271, h3296, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                · linarith only [h3079, h3271, h3289, hlam]
              · linarith only [h1, h3271, h3288, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3346 | h3346
        · linarith only [h0, h1, h3346, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h3348 | h3348
          · linarith only [h0, h3079, h3348, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3350 | h3350
            · linarith only [h0, h3271, h3350, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3352 | h3352
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3353 | h3353
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3354 | h3354
                  · linarith only [h0, h1, h3346, h3354, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3356 | h3356
                    · linarith only [h0, h3271, h3348, h3353, h3356, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3358 | h3358
                      · linarith only [h0, h3271, h3350, h3358, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3360 | h3360
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3361 | h3361
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3362 | h3362
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3363 | h3363
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3364 | h3364
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3365 | h3365
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3366 | h3366
                                    · rcases h1bigk with h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c
                                      · have p3367_0 := h3367c.1
                                        have p3367_1 := h3367c.2.1
                                        have p3367_2 := h3367c.2.2.1
                                        have p3367_3 := h3367c.2.2.2
                                        linarith only [hlam, p3367_0]
                                      · have p3367_0 := h3367c.1
                                        have p3367_1 := h3367c.2.1
                                        have p3367_2 := h3367c.2.2.1
                                        have p3367_3 := h3367c.2.2.2
                                        linarith only [h3271, h3354, h3360, h3362, hc12, hc23, hlam, hphi, p3367_1]
                                      · have p3367_0 := h3367c.1
                                        have p3367_1 := h3367c.2.1
                                        have p3367_2 := h3367c.2.2.1
                                        have p3367_3 := h3367c.2.2.2
                                        linarith only [h1, hlam, p3367_0]
                                      · have p3367_0 := h3367c.1
                                        have p3367_1 := h3367c.2.1
                                        have p3367_2 := h3367c.2.2.1
                                        have p3367_3 := h3367c.2.2.2
                                        linarith only [h3079, hlam, p3367_0]
                                      · have p3367_0 := h3367c.1
                                        have p3367_1 := h3367c.2.1
                                        have p3367_2 := h3367c.2.2.1
                                        have p3367_3 := h3367c.2.2.2
                                        linarith only [h3271, hlam, p3367_0]
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
                                        linarith only [h3354, hlam, p3367_1]
                                      · have p3367_0 := h3367c.1
                                        have p3367_1 := h3367c.2.1
                                        have p3367_2 := h3367c.2.2.1
                                        have p3367_3 := h3367c.2.2.2
                                        linarith only [h3356, hlam, p3367_1]
                                      · have p3367_0 := h3367c.1
                                        have p3367_1 := h3367c.2.1
                                        have p3367_2 := h3367c.2.2.1
                                        have p3367_3 := h3367c.2.2.2
                                        linarith only [h3358, hlam, p3367_1]
                                      · have p3367_0 := h3367c.1
                                        have p3367_1 := h3367c.2.1
                                        have p3367_2 := h3367c.2.2.1
                                        have p3367_3 := h3367c.2.2.2
                                        linarith only [h0, h3354, hc12, hc23, hlam, hphi, p3367_1]
                                      · have p3367_0 := h3367c.1
                                        have p3367_1 := h3367c.2.1
                                        have p3367_2 := h3367c.2.2.1
                                        have p3367_3 := h3367c.2.2.2
                                        rcases p3367_3 (m.d 0 1) (by simp) with h3379 | h3379
                                        · linarith only [h1, h3379, hlam]
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
                                        linarith only [h0, h3079, h3354, hc12, hc23, hlam, hphi, p3367_1]
                                      · have p3367_0 := h3367c.1
                                        have p3367_1 := h3367c.2.1
                                        have p3367_2 := h3367c.2.2.1
                                        have p3367_3 := h3367c.2.2.2
                                        linarith only [h0, h3271, h3354, hc12, hc23, hlam, hphi, p3367_1]
                                      · have p3367_0 := h3367c.1
                                        have p3367_1 := h3367c.2.1
                                        have p3367_2 := h3367c.2.2.1
                                        have p3367_3 := h3367c.2.2.2
                                        linarith only [h0, h3356, hc12, hc24, hlam, hphi, p3367_1]
                                      · have p3367_0 := h3367c.1
                                        have p3367_1 := h3367c.2.1
                                        have p3367_2 := h3367c.2.2.1
                                        have p3367_3 := h3367c.2.2.2
                                        rcases p3367_3 (m.d 0 1) (by simp) with h3386 | h3386
                                        · linarith only [h3079, h3386, hlam]
                                        · linarith only [h0, h3386, hlam]
                                      · have p3367_0 := h3367c.1
                                        have p3367_1 := h3367c.2.1
                                        have p3367_2 := h3367c.2.2.1
                                        have p3367_3 := h3367c.2.2.2
                                        linarith only [h3360, hlam, p3367_1]
                                      · have p3367_0 := h3367c.1
                                        have p3367_1 := h3367c.2.1
                                        have p3367_2 := h3367c.2.2.1
                                        have p3367_3 := h3367c.2.2.2
                                        linarith only [hlam, p3367_0]
                                      · have p3367_0 := h3367c.1
                                        have p3367_1 := h3367c.2.1
                                        have p3367_2 := h3367c.2.2.1
                                        have p3367_3 := h3367c.2.2.2
                                        linarith only [h0, h3271, h3354, h3360, hc12, hc23, hlam, hphi, p3367_1]
                                      · have p3367_0 := h3367c.1
                                        have p3367_1 := h3367c.2.1
                                        have p3367_2 := h3367c.2.2.1
                                        have p3367_3 := h3367c.2.2.2
                                        linarith only [h0, h3358, hc12, hc25, hlam, hphi, p3367_1]
                                      · have p3367_0 := h3367c.1
                                        have p3367_1 := h3367c.2.1
                                        have p3367_2 := h3367c.2.2.1
                                        have p3367_3 := h3367c.2.2.2
                                        rcases p3367_3 (m.d 0 1) (by simp) with h3393 | h3393
                                        · linarith only [h3271, h3393, hlam]
                                        · linarith only [h0, h3393, hlam]
                                      · have p3367_0 := h3367c.1
                                        have p3367_1 := h3367c.2.1
                                        have p3367_2 := h3367c.2.2.1
                                        have p3367_3 := h3367c.2.2.2
                                        linarith only [h3361, hlam, p3367_0]
                                      · have p3367_0 := h3367c.1
                                        have p3367_1 := h3367c.2.1
                                        have p3367_2 := h3367c.2.2.1
                                        have p3367_3 := h3367c.2.2.2
                                        linarith only [h3362, hlam, p3367_0]
                                      · have p3367_0 := h3367c.1
                                        have p3367_1 := h3367c.2.1
                                        have p3367_2 := h3367c.2.2.1
                                        have p3367_3 := h3367c.2.2.2
                                        linarith only [hlam, p3367_0]
                                    · rcases h1bigk with h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c
                                      · have p3399_0 := h3399c.1
                                        have p3399_1 := h3399c.2.1
                                        have p3399_2 := h3399c.2.2.1
                                        have p3399_3 := h3399c.2.2.2
                                        linarith only [hlam, p3399_0]
                                      · have p3399_0 := h3399c.1
                                        have p3399_1 := h3399c.2.1
                                        have p3399_2 := h3399c.2.2.1
                                        have p3399_3 := h3399c.2.2.2
                                        linarith only [h1, h3354, hc12, hc23, hlam, hphi, p3399_1]
                                      · have p3399_0 := h3399c.1
                                        have p3399_1 := h3399c.2.1
                                        have p3399_2 := h3399c.2.2.1
                                        have p3399_3 := h3399c.2.2.2
                                        linarith only [h1, hlam, p3399_0]
                                      · have p3399_0 := h3399c.1
                                        have p3399_1 := h3399c.2.1
                                        have p3399_2 := h3399c.2.2.1
                                        have p3399_3 := h3399c.2.2.2
                                        linarith only [h3079, hlam, p3399_0]
                                      · have p3399_0 := h3399c.1
                                        have p3399_1 := h3399c.2.1
                                        have p3399_2 := h3399c.2.2.1
                                        have p3399_3 := h3399c.2.2.2
                                        linarith only [h3271, hlam, p3399_0]
                                      · have p3399_0 := h3399c.1
                                        have p3399_1 := h3399c.2.1
                                        have p3399_2 := h3399c.2.2.1
                                        have p3399_3 := h3399c.2.2.2
                                        linarith only [h0, hlam, p3399_0]
                                      · have p3399_0 := h3399c.1
                                        have p3399_1 := h3399c.2.1
                                        have p3399_2 := h3399c.2.2.1
                                        have p3399_3 := h3399c.2.2.2
                                        linarith only [hlam, p3399_0]
                                      · have p3399_0 := h3399c.1
                                        have p3399_1 := h3399c.2.1
                                        have p3399_2 := h3399c.2.2.1
                                        have p3399_3 := h3399c.2.2.2
                                        linarith only [h3354, hlam, p3399_1]
                                      · have p3399_0 := h3399c.1
                                        have p3399_1 := h3399c.2.1
                                        have p3399_2 := h3399c.2.2.1
                                        have p3399_3 := h3399c.2.2.2
                                        linarith only [h3356, hlam, p3399_1]
                                      · have p3399_0 := h3399c.1
                                        have p3399_1 := h3399c.2.1
                                        have p3399_2 := h3399c.2.2.1
                                        have p3399_3 := h3399c.2.2.2
                                        linarith only [h3358, hlam, p3399_1]
                                      · have p3399_0 := h3399c.1
                                        have p3399_1 := h3399c.2.1
                                        have p3399_2 := h3399c.2.2.1
                                        have p3399_3 := h3399c.2.2.2
                                        linarith only [h0, h3354, hc12, hc23, hlam, hphi, p3399_1]
                                      · have p3399_0 := h3399c.1
                                        have p3399_1 := h3399c.2.1
                                        have p3399_2 := h3399c.2.2.1
                                        have p3399_3 := h3399c.2.2.2
                                        rcases p3399_3 (m.d 0 1) (by simp) with h3411 | h3411
                                        · linarith only [h1, h3411, hlam]
                                        · linarith only [h0, h3411, hlam]
                                      · have p3399_0 := h3399c.1
                                        have p3399_1 := h3399c.2.1
                                        have p3399_2 := h3399c.2.2.1
                                        have p3399_3 := h3399c.2.2.2
                                        linarith only [hlam, p3399_0]
                                      · have p3399_0 := h3399c.1
                                        have p3399_1 := h3399c.2.1
                                        have p3399_2 := h3399c.2.2.1
                                        have p3399_3 := h3399c.2.2.2
                                        linarith only [h0, h3079, h3354, hc12, hc23, hlam, hphi, p3399_1]
                                      · have p3399_0 := h3399c.1
                                        have p3399_1 := h3399c.2.1
                                        have p3399_2 := h3399c.2.2.1
                                        have p3399_3 := h3399c.2.2.2
                                        linarith only [h0, h3271, h3354, hc12, hc23, hlam, hphi, p3399_1]
                                      · have p3399_0 := h3399c.1
                                        have p3399_1 := h3399c.2.1
                                        have p3399_2 := h3399c.2.2.1
                                        have p3399_3 := h3399c.2.2.2
                                        linarith only [h0, h3356, h3363, hc12, hc23, hlam, hphi, p3399_1]
                                      · have p3399_0 := h3399c.1
                                        have p3399_1 := h3399c.2.1
                                        have p3399_2 := h3399c.2.2.1
                                        have p3399_3 := h3399c.2.2.2
                                        rcases p3399_3 (m.d 0 1) (by simp) with h3418 | h3418
                                        · linarith only [h3079, h3418, hlam]
                                        · linarith only [h0, h3418, hlam]
                                      · have p3399_0 := h3399c.1
                                        have p3399_1 := h3399c.2.1
                                        have p3399_2 := h3399c.2.2.1
                                        have p3399_3 := h3399c.2.2.2
                                        linarith only [h3360, hlam, p3399_1]
                                      · have p3399_0 := h3399c.1
                                        have p3399_1 := h3399c.2.1
                                        have p3399_2 := h3399c.2.2.1
                                        have p3399_3 := h3399c.2.2.2
                                        linarith only [hlam, p3399_0]
                                      · have p3399_0 := h3399c.1
                                        have p3399_1 := h3399c.2.1
                                        have p3399_2 := h3399c.2.2.1
                                        have p3399_3 := h3399c.2.2.2
                                        linarith only [h0, h3271, h3356, h3363, hc12, hc23, hlam, hphi, p3399_1]
                                      · have p3399_0 := h3399c.1
                                        have p3399_1 := h3399c.2.1
                                        have p3399_2 := h3399c.2.2.1
                                        have p3399_3 := h3399c.2.2.2
                                        linarith only [h0, h3358, h3363, h3365, hc12, hc23, hlam, hphi, p3399_1]
                                      · have p3399_0 := h3399c.1
                                        have p3399_1 := h3399c.2.1
                                        have p3399_2 := h3399c.2.2.1
                                        have p3399_3 := h3399c.2.2.2
                                        rcases p3399_3 (m.d 0 1) (by simp) with h3425 | h3425
                                        · linarith only [h3271, h3425, hlam]
                                        · linarith only [h0, h3425, hlam]
                                      · have p3399_0 := h3399c.1
                                        have p3399_1 := h3399c.2.1
                                        have p3399_2 := h3399c.2.2.1
                                        have p3399_3 := h3399c.2.2.2
                                        linarith only [h3361, hlam, p3399_0]
                                      · have p3399_0 := h3399c.1
                                        have p3399_1 := h3399c.2.1
                                        have p3399_2 := h3399c.2.2.1
                                        have p3399_3 := h3399c.2.2.2
                                        linarith only [h3362, hlam, p3399_0]
                                      · have p3399_0 := h3399c.1
                                        have p3399_1 := h3399c.2.1
                                        have p3399_2 := h3399c.2.2.1
                                        have p3399_3 := h3399c.2.2.2
                                        linarith only [hlam, p3399_0]
                                  · linarith only [h0, h3079, h3353, h3356, h3365, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                · linarith only [h0, h1, h3354, h3364, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h0, h3271, h3354, h3360, h3362, h3363, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h0, h3079, h3353, h3362, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                          · linarith only [h0, h1, h3361, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h3360, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3437 | h3437
                  · linarith only [h0, h3346, h3437, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3439 | h3439
                    · linarith only [h0, h3079, h3353, h3439, hc45, hlam, hphi, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3441 | h3441
                      · linarith only [h0, h3079, h3353, h3441, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3443 | h3443
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3444 | h3444
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3445 | h3445
                            · linarith only [h0, h3079, h3353, h3437, h3443, h3445, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h3079, h3445, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h3352, h3443, h3444, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                        · linarith only [h0, h1, h3443, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3450 | h3450
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3451 | h3451
                  · linarith only [h0, h1, h3352, h3451, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3453 | h3453
                    · linarith only [h0, h1, h3352, h3453, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3455 | h3455
                      · linarith only [h0, h1, h3352, h3455, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3457 | h3457
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3458 | h3458
                          · linarith only [h0, h1, h3352, h3451, h3458, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h3458, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h3457, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3462 | h3462
                  · linarith only [h0, h3079, h3450, h3462, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3464 | h3464
                    · linarith only [h0, h3079, h3450, h3464, hc45, hlam, hphi, u4ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3466 | h3466
                      · linarith only [h0, h3079, h3450, h3466, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3468 | h3468
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3469 | h3469
                          · linarith only [h0, h1, h3352, h3462, h3469, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h3469, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h3468, hc12, hc34, hlam, hphi, ht23]

end R2N4
