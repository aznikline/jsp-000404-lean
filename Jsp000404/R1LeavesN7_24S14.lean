import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_24S13

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6740000 in
set_option maxHeartbeats 6740000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0bigk := hb0.2.2.2
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s2 m hb0 hb1 hb3 hb4 h0 h1 h2
  · rcases m.htr 0 1 5 (by decide) (by decide) with h3173 | h3173
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3174 | h3174
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3175 | h3175
        · linarith only [h0, h2, h3175, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3177 | h3177
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3178 | h3178
            · linarith only [h1, h2, h3178, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3180 | h3180
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3181 | h3181
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3182 | h3182
                  · linarith only [h0, h2, h3182, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                  · linarith only [h0, h2, h3174, h3182, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                · linarith only [h0, h2, h3174, h3180, h3181, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3186 | h3186
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3187 | h3187
                  · linarith only [h0, h2, h3187, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                  · linarith only [h0, h2, h3174, h3187, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                · linarith only [h0, h2, h3177, h3186, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3191 | h3191
            · linarith only [h1, h2, h3191, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3193 | h3193
              · linarith only [h3174, h3177, h3193, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3195 | h3195
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3196 | h3196
                  · linarith only [h0, h2, h3196, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                  · linarith only [h2, h3173, h3174, h3177, h3196, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                · linarith only [h2, h3173, h3195, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3200 | h3200
        · linarith only [h0, h2, h3200, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3202 | h3202
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3203 | h3203
            · linarith only [h1, h2, h3203, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3205 | h3205
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3206 | h3206
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3207 | h3207
                  · linarith only [h3174, h3202, h3207, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3209 | h3209
                    · linarith only [h3200, h3202, h3209, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3211 | h3211
                      · linarith only [h1, h2, h3203, h3211, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3213 | h3213
                        · linarith only [h1, h2, h3213, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                        · linarith only [h1, h2, h3205, h3207, h3213, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                · linarith only [h0, h2, h3202, h3206, hlam]
              · linarith only [h3174, h3202, h3205, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3218 | h3218
            · linarith only [h1, h2, h3218, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3220 | h3220
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3221 | h3221
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3222 | h3222
                  · linarith only [h0, h2, h3174, h3222, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3224 | h3224
                    · linarith only [h0, h2, h3224, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3226 | h3226
                      · linarith only [h1, h2, h3218, h3226, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3228 | h3228
                        · linarith only [h1, h2, h3228, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                        · linarith only [h1, h2, h3220, h3222, h3228, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                · linarith only [h1, h2, h3220, h3221, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3232 | h3232
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3233 | h3233
                  · linarith only [h0, h2, h3174, h3233, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3235 | h3235
                    · linarith only [h0, h2, h3200, h3235, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3237 | h3237
                      · linarith only [h1, h2, h3218, h3237, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3239 | h3239
                        · linarith only [h1, h3220, h3239, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3241 | h3241
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3242 | h3242
                            · linarith only [h2, h3173, h3233, h3237, h3239, h3242, hc12, hc23, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3244 | h3244
                              · linarith only [h1, h3220, h3233, h3242, h3244, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3246 | h3246
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3247 | h3247
                                  · rcases h0bigk with h3248c | h3248c | h3248c | h3248c | h3248c | h3248c | h3248c | h3248c | h3248c | h3248c | h3248c | h3248c | h3248c | h3248c | h3248c | h3248c | h3248c | h3248c | h3248c | h3248c | h3248c | h3248c | h3248c | h3248c | h3248c
                                    · have p3248_0 := h3248c.1
                                      have p3248_1 := h3248c.2.1
                                      have p3248_2 := h3248c.2.2.1
                                      have p3248_3 := h3248c.2.2.2
                                      linarith only [hlam, p3248_0]
                                    · have p3248_0 := h3248c.1
                                      have p3248_1 := h3248c.2.1
                                      have p3248_2 := h3248c.2.2.1
                                      have p3248_3 := h3248c.2.2.2
                                      linarith only [h0, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3248_1, u1elo3]
                                    · have p3248_0 := h3248c.1
                                      have p3248_1 := h3248c.2.1
                                      have p3248_2 := h3248c.2.2.1
                                      have p3248_3 := h3248c.2.2.2
                                      linarith only [h1, h2, h3233, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3248_1, u1elo3]
                                    · have p3248_0 := h3248c.1
                                      have p3248_1 := h3248c.2.1
                                      have p3248_2 := h3248c.2.2.1
                                      have p3248_3 := h3248c.2.2.2
                                      linarith only [h2, hlam, p3248_1]
                                    · have p3248_0 := h3248c.1
                                      have p3248_1 := h3248c.2.1
                                      have p3248_2 := h3248c.2.2.1
                                      have p3248_3 := h3248c.2.2.2
                                      linarith only [h2, hc05, hlam, hphi, ht01, ht0b, ht5b, p3248_1, u1elo3]
                                    · have p3248_0 := h3248c.1
                                      have p3248_1 := h3248c.2.1
                                      have p3248_2 := h3248c.2.2.1
                                      have p3248_3 := h3248c.2.2.2
                                      linarith only [h0, hlam, p3248_0]
                                    · have p3248_0 := h3248c.1
                                      have p3248_1 := h3248c.2.1
                                      have p3248_2 := h3248c.2.2.1
                                      have p3248_3 := h3248c.2.2.2
                                      linarith only [hlam, p3248_0]
                                    · have p3248_0 := h3248c.1
                                      have p3248_1 := h3248c.2.1
                                      have p3248_2 := h3248c.2.2.1
                                      have p3248_3 := h3248c.2.2.2
                                      linarith only [h3174, hlam, p3248_0]
                                    · have p3248_0 := h3248c.1
                                      have p3248_1 := h3248c.2.1
                                      have p3248_2 := h3248c.2.2.1
                                      have p3248_3 := h3248c.2.2.2
                                      linarith only [h3200, hlam, p3248_1]
                                    · have p3248_0 := h3248c.1
                                      have p3248_1 := h3248c.2.1
                                      have p3248_2 := h3248c.2.2.1
                                      have p3248_3 := h3248c.2.2.2
                                      linarith only [h3202, hlam, p3248_0]
                                    · have p3248_0 := h3248c.1
                                      have p3248_1 := h3248c.2.1
                                      have p3248_2 := h3248c.2.2.1
                                      have p3248_3 := h3248c.2.2.2
                                      linarith only [h1, hlam, p3248_1]
                                    · have p3248_0 := h3248c.1
                                      have p3248_1 := h3248c.2.1
                                      have p3248_2 := h3248c.2.2.1
                                      have p3248_3 := h3248c.2.2.2
                                      linarith only [h0, h1, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3248_1, u1elo3]
                                    · have p3248_0 := h3248c.1
                                      have p3248_1 := h3248c.2.1
                                      have p3248_2 := h3248c.2.2.1
                                      have p3248_3 := h3248c.2.2.2
                                      linarith only [hlam, p3248_0]
                                    · have p3248_0 := h3248c.1
                                      have p3248_1 := h3248c.2.1
                                      have p3248_2 := h3248c.2.2.1
                                      have p3248_3 := h3248c.2.2.2
                                      linarith only [h3218, hlam, p3248_1]
                                    · have p3248_0 := h3248c.1
                                      have p3248_1 := h3248c.2.1
                                      have p3248_2 := h3248c.2.2.1
                                      have p3248_3 := h3248c.2.2.2
                                      linarith only [h3220, hlam, p3248_1]
                                    · have p3248_0 := h3248c.1
                                      have p3248_1 := h3248c.2.1
                                      have p3248_2 := h3248c.2.2.1
                                      have p3248_3 := h3248c.2.2.2
                                      linarith only [h3173, hc15, hlam, hphi, ht0b, ht5b, p3248_1, u0elo3]
                                    · have p3248_0 := h3248c.1
                                      have p3248_1 := h3248c.2.1
                                      have p3248_2 := h3248c.2.2.1
                                      have p3248_3 := h3248c.2.2.2
                                      rcases p3248_3 (m.d 0 1) (by simp) with h3265 | h3265
                                      · linarith only [h2, h3265, hlam]
                                      · linarith only [h0, h3265, hlam]
                                    · have p3248_0 := h3248c.1
                                      have p3248_1 := h3248c.2.1
                                      have p3248_2 := h3248c.2.2.1
                                      have p3248_3 := h3248c.2.2.2
                                      rcases p3248_3 (m.d 0 1) (by simp) with h3268 | h3268
                                      · linarith only [h2, h3268, hlam]
                                      · linarith only [h1, h3268, hlam]
                                    · have p3248_0 := h3248c.1
                                      have p3248_1 := h3248c.2.1
                                      have p3248_2 := h3248c.2.2.1
                                      have p3248_3 := h3248c.2.2.2
                                      linarith only [hlam, p3248_0]
                                    · have p3248_0 := h3248c.1
                                      have p3248_1 := h3248c.2.1
                                      have p3248_2 := h3248c.2.2.1
                                      have p3248_3 := h3248c.2.2.2
                                      rcases p3248_3 (m.d 0 1) (by simp) with h3272 | h3272
                                      · linarith only [h2, h3272, hlam]
                                      · linarith only [h3173, h3272, hlam]
                                    · have p3248_0 := h3248c.1
                                      have p3248_1 := h3248c.2.1
                                      have p3248_2 := h3248c.2.2.1
                                      have p3248_3 := h3248c.2.2.2
                                      linarith only [h3173, hlam, p3248_0]
                                    · have p3248_0 := h3248c.1
                                      have p3248_1 := h3248c.2.1
                                      have p3248_2 := h3248c.2.2.1
                                      have p3248_3 := h3248c.2.2.2
                                      linarith only [h0, h2, h3173, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3248_1, u1elo3]
                                    · have p3248_0 := h3248c.1
                                      have p3248_1 := h3248c.2.1
                                      have p3248_2 := h3248c.2.2.1
                                      have p3248_3 := h3248c.2.2.2
                                      linarith only [h2, h3173, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3248_1, u1elo3]
                                    · have p3248_0 := h3248c.1
                                      have p3248_1 := h3248c.2.1
                                      have p3248_2 := h3248c.2.2.1
                                      have p3248_3 := h3248c.2.2.2
                                      linarith only [h3232, hlam, p3248_1]
                                    · have p3248_0 := h3248c.1
                                      have p3248_1 := h3248c.2.1
                                      have p3248_2 := h3248c.2.2.1
                                      have p3248_3 := h3248c.2.2.2
                                      linarith only [hlam, p3248_0]
                                  · linarith only [h3218, h3232, h3247, hlam]
                                · linarith only [h2, h3173, h3235, h3241, h3246, hlam]
                          · linarith only [h0, h2, h3241, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h2, h3173, h3232, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3284 | h3284
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3285 | h3285
        · linarith only [h0, h2, h3285, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3287 | h3287
          · linarith only [h0, h3173, h3287, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3289 | h3289
            · linarith only [h1, h2, h3289, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3291 | h3291
              · linarith only [h0, h3173, h3284, h3291, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3293 | h3293
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3294 | h3294
                  · linarith only [h0, h3173, h3294, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                  · linarith only [h0, h3173, h3284, h3294, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3297 | h3297
                  · linarith only [h0, h3173, h3297, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                  · linarith only [h0, h3173, h3284, h3297, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3300 | h3300
        · linarith only [h1, h2, h3284, h3300, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3302 | h3302
          · linarith only [h1, h3173, h3284, h3302, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3304 | h3304
            · linarith only [h1, h2, h3304, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3306 | h3306
              · linarith only [h1, h3173, h3306, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3308 | h3308
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3309 | h3309
                  · linarith only [h0, h3173, h3284, h3309, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3311 | h3311
                    · linarith only [h0, h3173, h3300, h3308, h3311, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3313 | h3313
                      · linarith only [h1, h3173, h3304, h3313, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3315 | h3315
                        · linarith only [h1, h3173, h3306, h3315, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3317 | h3317
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3318 | h3318
                            · linarith only [h1, h3173, h3309, h3313, h3317, h3318, hc12, hc23, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3320 | h3320
                              · linarith only [h1, h3173, h3309, h3315, h3318, h3320, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3322 | h3322
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3323 | h3323
                                  · rcases h0bigk with h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c
                                    · have p3324_0 := h3324c.1
                                      have p3324_1 := h3324c.2.1
                                      have p3324_2 := h3324c.2.2.1
                                      have p3324_3 := h3324c.2.2.2
                                      linarith only [hlam, p3324_0]
                                    · have p3324_0 := h3324c.1
                                      have p3324_1 := h3324c.2.1
                                      have p3324_2 := h3324c.2.2.1
                                      have p3324_3 := h3324c.2.2.2
                                      linarith only [h3173, h3317, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3324_1, u1elo3]
                                    · have p3324_0 := h3324c.1
                                      have p3324_1 := h3324c.2.1
                                      have p3324_2 := h3324c.2.2.1
                                      have p3324_3 := h3324c.2.2.2
                                      linarith only [h0, h3173, h3284, h3317, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3324_1, u1elo3]
                                    · have p3324_0 := h3324c.1
                                      have p3324_1 := h3324c.2.1
                                      have p3324_2 := h3324c.2.2.1
                                      have p3324_3 := h3324c.2.2.2
                                      linarith only [h2, hlam, p3324_1]
                                    · have p3324_0 := h3324c.1
                                      have p3324_1 := h3324c.2.1
                                      have p3324_2 := h3324c.2.2.1
                                      have p3324_3 := h3324c.2.2.2
                                      linarith only [h3173, hlam, p3324_1]
                                    · have p3324_0 := h3324c.1
                                      have p3324_1 := h3324c.2.1
                                      have p3324_2 := h3324c.2.2.1
                                      have p3324_3 := h3324c.2.2.2
                                      linarith only [h0, hlam, p3324_0]
                                    · have p3324_0 := h3324c.1
                                      have p3324_1 := h3324c.2.1
                                      have p3324_2 := h3324c.2.2.1
                                      have p3324_3 := h3324c.2.2.2
                                      linarith only [hlam, p3324_0]
                                    · have p3324_0 := h3324c.1
                                      have p3324_1 := h3324c.2.1
                                      have p3324_2 := h3324c.2.2.1
                                      have p3324_3 := h3324c.2.2.2
                                      linarith only [h3284, hlam, p3324_0]
                                    · have p3324_0 := h3324c.1
                                      have p3324_1 := h3324c.2.1
                                      have p3324_2 := h3324c.2.2.1
                                      have p3324_3 := h3324c.2.2.2
                                      linarith only [h3300, hlam, p3324_1]
                                    · have p3324_0 := h3324c.1
                                      have p3324_1 := h3324c.2.1
                                      have p3324_2 := h3324c.2.2.1
                                      have p3324_3 := h3324c.2.2.2
                                      linarith only [h3302, hlam, p3324_0]
                                    · have p3324_0 := h3324c.1
                                      have p3324_1 := h3324c.2.1
                                      have p3324_2 := h3324c.2.2.1
                                      have p3324_3 := h3324c.2.2.2
                                      linarith only [h1, hlam, p3324_1]
                                    · have p3324_0 := h3324c.1
                                      have p3324_1 := h3324c.2.1
                                      have p3324_2 := h3324c.2.2.1
                                      have p3324_3 := h3324c.2.2.2
                                      linarith only [h0, h1, h3173, h3317, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3324_1, u1elo3]
                                    · have p3324_0 := h3324c.1
                                      have p3324_1 := h3324c.2.1
                                      have p3324_2 := h3324c.2.2.1
                                      have p3324_3 := h3324c.2.2.2
                                      linarith only [hlam, p3324_0]
                                    · have p3324_0 := h3324c.1
                                      have p3324_1 := h3324c.2.1
                                      have p3324_2 := h3324c.2.2.1
                                      have p3324_3 := h3324c.2.2.2
                                      linarith only [h3304, hlam, p3324_1]
                                    · have p3324_0 := h3324c.1
                                      have p3324_1 := h3324c.2.1
                                      have p3324_2 := h3324c.2.2.1
                                      have p3324_3 := h3324c.2.2.2
                                      linarith only [h3306, hlam, p3324_1]
                                    · have p3324_0 := h3324c.1
                                      have p3324_1 := h3324c.2.1
                                      have p3324_2 := h3324c.2.2.1
                                      have p3324_3 := h3324c.2.2.2
                                      linarith only [h1, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3324_1, u0elo3]
                                    · have p3324_0 := h3324c.1
                                      have p3324_1 := h3324c.2.1
                                      have p3324_2 := h3324c.2.2.1
                                      have p3324_3 := h3324c.2.2.2
                                      rcases p3324_3 (m.d 0 1) (by simp) with h3341 | h3341
                                      · linarith only [h2, h3341, hlam]
                                      · linarith only [h0, h3341, hlam]
                                    · have p3324_0 := h3324c.1
                                      have p3324_1 := h3324c.2.1
                                      have p3324_2 := h3324c.2.2.1
                                      have p3324_3 := h3324c.2.2.2
                                      rcases p3324_3 (m.d 0 1) (by simp) with h3344 | h3344
                                      · linarith only [h2, h3344, hlam]
                                      · linarith only [h1, h3344, hlam]
                                    · have p3324_0 := h3324c.1
                                      have p3324_1 := h3324c.2.1
                                      have p3324_2 := h3324c.2.2.1
                                      have p3324_3 := h3324c.2.2.2
                                      linarith only [hlam, p3324_0]
                                    · have p3324_0 := h3324c.1
                                      have p3324_1 := h3324c.2.1
                                      have p3324_2 := h3324c.2.2.1
                                      have p3324_3 := h3324c.2.2.2
                                      linarith only [h1, h2, h3173, h3309, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3324_1, u1elo3]
                                    · have p3324_0 := h3324c.1
                                      have p3324_1 := h3324c.2.1
                                      have p3324_2 := h3324c.2.2.1
                                      have p3324_3 := h3324c.2.2.2
                                      linarith only [h1, h3309, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3324_1, u0elo4]
                                    · have p3324_0 := h3324c.1
                                      have p3324_1 := h3324c.2.1
                                      have p3324_2 := h3324c.2.2.1
                                      have p3324_3 := h3324c.2.2.2
                                      rcases p3324_3 (m.d 0 1) (by simp) with h3350 | h3350
                                      · linarith only [h3173, h3350, hlam]
                                      · linarith only [h0, h3350, hlam]
                                    · have p3324_0 := h3324c.1
                                      have p3324_1 := h3324c.2.1
                                      have p3324_2 := h3324c.2.2.1
                                      have p3324_3 := h3324c.2.2.2
                                      rcases p3324_3 (m.d 0 1) (by simp) with h3353 | h3353
                                      · linarith only [h3173, h3353, hlam]
                                      · linarith only [h1, h3353, hlam]
                                    · have p3324_0 := h3324c.1
                                      have p3324_1 := h3324c.2.1
                                      have p3324_2 := h3324c.2.2.1
                                      have p3324_3 := h3324c.2.2.2
                                      linarith only [h3308, hlam, p3324_1]
                                    · have p3324_0 := h3324c.1
                                      have p3324_1 := h3324c.2.1
                                      have p3324_2 := h3324c.2.2.1
                                      have p3324_3 := h3324c.2.2.2
                                      linarith only [hlam, p3324_0]
                                  · linarith only [h2, h3304, h3308, h3323, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                                · linarith only [h2, h3308, h3311, h3322, hlam]
                          · linarith only [h2, h3308, h3317, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3361 | h3361
                  · linarith only [h0, h3284, h3361, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3363 | h3363
                    · linarith only [h1, h2, h3361, h3363, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3365 | h3365
                      · linarith only [h1, h2, h3365, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3367 | h3367
                        · linarith only [h1, h2, h3367, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3369 | h3369
                          · linarith only [h1, h2, h3308, h3361, h3369, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                          · linarith only [h1, h2, h3361, h3369, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 7774000 in
set_option maxHeartbeats 7774000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0bigk := hb0.2.2.2
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s1 m hb0 hb1 hb3 hb4 h0 h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h3372 | h3372
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3373 | h3373
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3374 | h3374
        · linarith only [h0, h1, h3374, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h3376 | h3376
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3377 | h3377
            · rcases m.htr 0 3 4 (by decide) (by decide) with h3378 | h3378
              · rcases m.htr 0 3 5 (by decide) (by decide) with h3379 | h3379
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3380 | h3380
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3381 | h3381
                    · linarith only [h3374, h3376, h3381, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3383 | h3383
                      · linarith only [h0, h1, h3383, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · linarith only [h0, h1, h3376, h3383, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3386 | h3386
                    · linarith only [h3374, h3376, h3386, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3388 | h3388
                      · linarith only [h0, h1, h3388, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · linarith only [h0, h1, h3376, h3388, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                · linarith only [h0, h1, h3377, h3379, hlam]
              · linarith only [h1, h3372, h3378, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h3393 | h3393
              · rcases m.htr 0 3 5 (by decide) (by decide) with h3394 | h3394
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3395 | h3395
                  · linarith only [h3376, h3377, h3395, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3397 | h3397
                    · linarith only [h3374, h3376, h3397, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3399 | h3399
                      · linarith only [h0, h1, h3399, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · linarith only [h3376, h3377, h3399, hc12, hc25, hlam, hphi]
                · linarith only [h1, h3373, h3394, hlam]
              · linarith only [h1, h3373, h3376, h3377, h3393, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3404 | h3404
            · rcases m.htr 0 3 4 (by decide) (by decide) with h3405 | h3405
              · rcases m.htr 0 3 5 (by decide) (by decide) with h3406 | h3406
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3407 | h3407
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3408 | h3408
                    · linarith only [h0, h1, h3408, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3410 | h3410
                      · linarith only [h0, h1, h3376, h3404, h3410, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3412 | h3412
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3413 | h3413
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3414 | h3414
                            · linarith only [h1, h3372, h3414, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                            · linarith only [h1, h3372, h3407, h3410, h3414, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                          · linarith only [h0, h1, h3413, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h3372, h3405, h3412, hlam]
                  · linarith only [h3376, h3404, h3407, hlam]
                · linarith only [h0, h1, h3404, h3406, hlam]
              · linarith only [h1, h3372, h3405, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h3422 | h3422
              · rcases m.htr 0 3 5 (by decide) (by decide) with h3423 | h3423
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3424 | h3424
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3425 | h3425
                    · linarith only [h0, h1, h3425, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3427 | h3427
                      · linarith only [h0, h1, h3376, h3427, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3429 | h3429
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3430 | h3430
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3431 | h3431
                            · linarith only [h1, h3372, h3431, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                            · linarith only [h1, h3372, h3424, h3431, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                          · linarith only [h0, h1, h3430, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h3372, h3427, h3429, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3436 | h3436
                    · linarith only [h0, h1, h3436, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3438 | h3438
                      · linarith only [h0, h1, h3376, h3438, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3440 | h3440
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3441 | h3441
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3442 | h3442
                            · linarith only [h0, h1, h3372, h3376, h3424, h3442, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3444 | h3444
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3445 | h3445
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3446 | h3446
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3447 | h3447
                                    · linarith only [h3372, h3424, h3440, h3447, hlam]
                                    · rcases h0bigk with h3449c | h3449c | h3449c | h3449c | h3449c | h3449c | h3449c | h3449c | h3449c | h3449c | h3449c | h3449c | h3449c | h3449c | h3449c | h3449c | h3449c | h3449c | h3449c | h3449c | h3449c | h3449c | h3449c | h3449c | h3449c
                                      · have p3449_0 := h3449c.1
                                        have p3449_1 := h3449c.2.1
                                        have p3449_2 := h3449c.2.2.1
                                        have p3449_3 := h3449c.2.2.2
                                        linarith only [hlam, p3449_0]
                                      · have p3449_0 := h3449c.1
                                        have p3449_1 := h3449c.2.1
                                        have p3449_2 := h3449c.2.2.1
                                        have p3449_3 := h3449c.2.2.2
                                        linarith only [h0, h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3449_1, u1elo2]
                                      · have p3449_0 := h3449c.1
                                        have p3449_1 := h3449c.2.1
                                        have p3449_2 := h3449c.2.2.1
                                        have p3449_3 := h3449c.2.2.2
                                        linarith only [h1, hlam, p3449_0]
                                      · have p3449_0 := h3449c.1
                                        have p3449_1 := h3449c.2.1
                                        have p3449_2 := h3449c.2.2.1
                                        have p3449_3 := h3449c.2.2.2
                                        linarith only [h0, h1, h3376, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3449_1, u1elo2]
                                      · have p3449_0 := h3449c.1
                                        have p3449_1 := h3449c.2.1
                                        have p3449_2 := h3449c.2.2.1
                                        have p3449_3 := h3449c.2.2.2
                                        linarith only [h0, h1, h3376, h3424, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3449_1, u1elo2]
                                      · have p3449_0 := h3449c.1
                                        have p3449_1 := h3449c.2.1
                                        have p3449_2 := h3449c.2.2.1
                                        have p3449_3 := h3449c.2.2.2
                                        linarith only [h0, hlam, p3449_0]
                                      · have p3449_0 := h3449c.1
                                        have p3449_1 := h3449c.2.1
                                        have p3449_2 := h3449c.2.2.1
                                        have p3449_3 := h3449c.2.2.2
                                        linarith only [hlam, p3449_0]
                                      · have p3449_0 := h3449c.1
                                        have p3449_1 := h3449c.2.1
                                        have p3449_2 := h3449c.2.2.1
                                        have p3449_3 := h3449c.2.2.2
                                        linarith only [h3374, hlam, p3449_0]
                                      · have p3449_0 := h3449c.1
                                        have p3449_1 := h3449c.2.1
                                        have p3449_2 := h3449c.2.2.1
                                        have p3449_3 := h3449c.2.2.2
                                        linarith only [h3376, hlam, p3449_1]
                                      · have p3449_0 := h3449c.1
                                        have p3449_1 := h3449c.2.1
                                        have p3449_2 := h3449c.2.2.1
                                        have p3449_3 := h3449c.2.2.2
                                        linarith only [h3404, hlam, p3449_0]
                                      · have p3449_0 := h3449c.1
                                        have p3449_1 := h3449c.2.1
                                        have p3449_2 := h3449c.2.2.1
                                        have p3449_3 := h3449c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3449_1, u0elo2]
                                      · have p3449_0 := h3449c.1
                                        have p3449_1 := h3449c.2.1
                                        have p3449_2 := h3449c.2.2.1
                                        have p3449_3 := h3449c.2.2.2
                                        rcases p3449_3 (m.d 0 1) (by simp) with h3461 | h3461
                                        · linarith only [h1, h3461, hlam]
                                        · linarith only [h0, h3461, hlam]
                                      · have p3449_0 := h3449c.1
                                        have p3449_1 := h3449c.2.1
                                        have p3449_2 := h3449c.2.2.1
                                        have p3449_3 := h3449c.2.2.2
                                        linarith only [hlam, p3449_0]
                                      · have p3449_0 := h3449c.1
                                        have p3449_1 := h3449c.2.1
                                        have p3449_2 := h3449c.2.2.1
                                        have p3449_3 := h3449c.2.2.2
                                        rcases p3449_3 (m.d 0 1) (by simp) with h3465 | h3465
                                        · linarith only [h1, h3465, hlam]
                                        · linarith only [h3372, h3465, hlam]
                                      · have p3449_0 := h3449c.1
                                        have p3449_1 := h3449c.2.1
                                        have p3449_2 := h3449c.2.2.1
                                        have p3449_3 := h3449c.2.2.2
                                        rcases p3449_3 (m.d 0 1) (by simp) with h3468 | h3468
                                        · linarith only [h1, h3468, hlam]
                                        · linarith only [h3373, h3468, hlam]
                                      · have p3449_0 := h3449c.1
                                        have p3449_1 := h3449c.2.1
                                        have p3449_2 := h3449c.2.2.1
                                        have p3449_3 := h3449c.2.2.2
                                        linarith only [h3372, hlam, p3449_0]
                                      · have p3449_0 := h3449c.1
                                        have p3449_1 := h3449c.2.1
                                        have p3449_2 := h3449c.2.2.1
                                        have p3449_3 := h3449c.2.2.2
                                        linarith only [h0, h3424, h3446, hc12, hc24, hlam, hphi, p3449_1]
                                      · have p3449_0 := h3449c.1
                                        have p3449_1 := h3449c.2.1
                                        have p3449_2 := h3449c.2.2.1
                                        have p3449_3 := h3449c.2.2.2
                                        linarith only [h3422, hlam, p3449_0]
                                      · have p3449_0 := h3449c.1
                                        have p3449_1 := h3449c.2.1
                                        have p3449_2 := h3449c.2.2.1
                                        have p3449_3 := h3449c.2.2.2
                                        linarith only [hlam, p3449_0]
                                      · have p3449_0 := h3449c.1
                                        have p3449_1 := h3449c.2.1
                                        have p3449_2 := h3449c.2.2.1
                                        have p3449_3 := h3449c.2.2.2
                                        linarith only [h3424, hlam, p3449_0]
                                      · have p3449_0 := h3449c.1
                                        have p3449_1 := h3449c.2.1
                                        have p3449_2 := h3449c.2.2.1
                                        have p3449_3 := h3449c.2.2.2
                                        linarith only [h3373, hlam, p3449_0]
                                      · have p3449_0 := h3449c.1
                                        have p3449_1 := h3449c.2.1
                                        have p3449_2 := h3449c.2.2.1
                                        have p3449_3 := h3449c.2.2.2
                                        linarith only [h0, h1, h3373, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3449_1, u1elo2]
                                      · have p3449_0 := h3449c.1
                                        have p3449_1 := h3449c.2.1
                                        have p3449_2 := h3449c.2.2.1
                                        have p3449_3 := h3449c.2.2.2
                                        linarith only [h3423, hlam, p3449_0]
                                      · have p3449_0 := h3449c.1
                                        have p3449_1 := h3449c.2.1
                                        have p3449_2 := h3449c.2.2.1
                                        have p3449_3 := h3449c.2.2.2
                                        linarith only [h1, h3373, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p3449_1, u1elo2]
                                      · have p3449_0 := h3449c.1
                                        have p3449_1 := h3449c.2.1
                                        have p3449_2 := h3449c.2.2.1
                                        have p3449_3 := h3449c.2.2.2
                                        linarith only [hlam, p3449_0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3481 | h3481
                                    · linarith only [h1, h3373, h3440, h3442, h3446, h3481, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                                    · rcases h0bigk with h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c | h3483c
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [hlam, p3483_0]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [h0, h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3483_1, u1elo2]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [h1, hlam, p3483_0]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [h1, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p3483_1, u1elo2]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [h1, hc05, hlam, hphi, ht01, ht0b, ht5b, p3483_1, u1elo2]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [h0, hlam, p3483_0]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [hlam, p3483_0]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [h3374, hlam, p3483_0]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [h3376, hlam, p3483_1]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [h3404, hlam, p3483_0]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [h1, hc01, hlam, hphi, p3483_1, u1elo2]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        rcases p3483_3 (m.d 0 1) (by simp) with h3495 | h3495
                                        · linarith only [h1, h3495, hlam]
                                        · linarith only [h0, h3495, hlam]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [hlam, p3483_0]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        rcases p3483_3 (m.d 0 1) (by simp) with h3499 | h3499
                                        · linarith only [h1, h3499, hlam]
                                        · linarith only [h3372, h3499, hlam]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        rcases p3483_3 (m.d 0 1) (by simp) with h3502 | h3502
                                        · linarith only [h1, h3502, hlam]
                                        · linarith only [h3373, h3502, hlam]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [h3372, hlam, p3483_0]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [h0, h1, h3372, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3483_1, u1elo2]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [h3422, hlam, p3483_0]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [hlam, p3483_0]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [h3424, hlam, p3483_0]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [h3373, hlam, p3483_0]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [h0, h1, h3373, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3483_1, u1elo2]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [h3423, hlam, p3483_0]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [h1, h3373, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p3483_1, u1elo2]
                                      · have p3483_0 := h3483c.1
                                        have p3483_1 := h3483c.2.1
                                        have p3483_2 := h3483c.2.2.1
                                        have p3483_3 := h3483c.2.2.2
                                        linarith only [hlam, p3483_0]
                                · linarith only [h1, h3373, h3441, h3445, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                              · linarith only [h0, h1, h3436, h3444, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h1, h3372, h3438, h3441, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h3372, h3438, h3440, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h1, h3373, h3423, hlam]
              · linarith only [h1, h3372, h3422, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3521 | h3521
        · linarith only [h0, h1, h3521, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h3523 | h3523
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3524 | h3524
            · linarith only [h0, h3373, h3524, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h3526 | h3526
              · rcases m.htr 0 3 5 (by decide) (by decide) with h3527 | h3527
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3528 | h3528
                  · linarith only [h0, h3373, h3523, h3528, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3530 | h3530
                    · linarith only [h3521, h3523, h3530, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3532 | h3532
                      · linarith only [h0, h1, h3532, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · linarith only [h3523, h3524, h3532, hc12, hc25, hlam, hphi]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3535 | h3535
                  · linarith only [h0, h1, h3523, h3527, h3535, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3537 | h3537
                    · linarith only [h3521, h3523, h3537, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3539 | h3539
                      · linarith only [h0, h1, h3539, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · linarith only [h3523, h3524, h3539, hc12, hc25, hlam, hphi]
              · linarith only [h0, h1, h3523, h3526, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3543 | h3543
            · linarith only [h3372, h3373, h3523, h3543, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h3545 | h3545
              · rcases m.htr 0 3 5 (by decide) (by decide) with h3546 | h3546
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3547 | h3547
                  · linarith only [h3372, h3373, h3547, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3549 | h3549
                    · linarith only [h0, h1, h3549, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3551 | h3551
                      · linarith only [h0, h1, h3523, h3551, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3553 | h3553
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3554 | h3554
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3555 | h3555
                            · linarith only [h3372, h3373, h3547, h3554, h3555, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3557 | h3557
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3558 | h3558
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3559 | h3559
                                  · linarith only [h0, h3373, h3555, h3559, hc12, hc24, hlam, hphi]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3561 | h3561
                                    · linarith only [h0, h3523, h3559, h3561, hc12, hc34, hlam, hphi, ht23]
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
                                        linarith only [h0, h3373, h3554, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3563_1, u1elo2]
                                      · have p3563_0 := h3563c.1
                                        have p3563_1 := h3563c.2.1
                                        have p3563_2 := h3563c.2.2.1
                                        have p3563_3 := h3563c.2.2.2
                                        linarith only [h1, hlam, p3563_0]
                                      · have p3563_0 := h3563c.1
                                        have p3563_1 := h3563c.2.1
                                        have p3563_2 := h3563c.2.2.1
                                        have p3563_3 := h3563c.2.2.2
                                        linarith only [h0, h3373, h3523, h3554, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3563_1, u1elo2]
                                      · have p3563_0 := h3563c.1
                                        have p3563_1 := h3563c.2.1
                                        have p3563_2 := h3563c.2.2.1
                                        have p3563_3 := h3563c.2.2.2
                                        linarith only [h3373, hlam, p3563_1]
                                      · have p3563_0 := h3563c.1
                                        have p3563_1 := h3563c.2.1
                                        have p3563_2 := h3563c.2.2.1
                                        have p3563_3 := h3563c.2.2.2
                                        linarith only [h0, hlam, p3563_0]
                                      · have p3563_0 := h3563c.1
                                        have p3563_1 := h3563c.2.1
                                        have p3563_2 := h3563c.2.2.1
                                        have p3563_3 := h3563c.2.2.2
                                        linarith only [hlam, p3563_0]
                                      · have p3563_0 := h3563c.1
                                        have p3563_1 := h3563c.2.1
                                        have p3563_2 := h3563c.2.2.1
                                        have p3563_3 := h3563c.2.2.2
                                        linarith only [h3521, hlam, p3563_0]
                                      · have p3563_0 := h3563c.1
                                        have p3563_1 := h3563c.2.1
                                        have p3563_2 := h3563c.2.2.1
                                        have p3563_3 := h3563c.2.2.2
                                        linarith only [h3523, hlam, p3563_1]
                                      · have p3563_0 := h3563c.1
                                        have p3563_1 := h3563c.2.1
                                        have p3563_2 := h3563c.2.2.1
                                        have p3563_3 := h3563c.2.2.2
                                        linarith only [h3543, hlam, p3563_0]
                                      · have p3563_0 := h3563c.1
                                        have p3563_1 := h3563c.2.1
                                        have p3563_2 := h3563c.2.2.1
                                        have p3563_3 := h3563c.2.2.2
                                        linarith only [h3372, hc14, hlam, hphi, ht0b, ht45, ht5b, p3563_1, u0elo2]
                                      · have p3563_0 := h3563c.1
                                        have p3563_1 := h3563c.2.1
                                        have p3563_2 := h3563c.2.2.1
                                        have p3563_3 := h3563c.2.2.2
                                        rcases p3563_3 (m.d 0 1) (by simp) with h3575 | h3575
                                        · linarith only [h1, h3575, hlam]
                                        · linarith only [h0, h3575, hlam]
                                      · have p3563_0 := h3563c.1
                                        have p3563_1 := h3563c.2.1
                                        have p3563_2 := h3563c.2.2.1
                                        have p3563_3 := h3563c.2.2.2
                                        linarith only [hlam, p3563_0]
                                      · have p3563_0 := h3563c.1
                                        have p3563_1 := h3563c.2.1
                                        have p3563_2 := h3563c.2.2.1
                                        have p3563_3 := h3563c.2.2.2
                                        rcases p3563_3 (m.d 0 1) (by simp) with h3579 | h3579
                                        · linarith only [h1, h3579, hlam]
                                        · linarith only [h3372, h3579, hlam]
                                      · have p3563_0 := h3563c.1
                                        have p3563_1 := h3563c.2.1
                                        have p3563_2 := h3563c.2.2.1
                                        have p3563_3 := h3563c.2.2.2
                                        linarith only [h1, h3372, h3373, h3551, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3563_1, u1elo2]
                                      · have p3563_0 := h3563c.1
                                        have p3563_1 := h3563c.2.1
                                        have p3563_2 := h3563c.2.2.1
                                        have p3563_3 := h3563c.2.2.2
                                        linarith only [h3372, hlam, p3563_0]
                                      · have p3563_0 := h3563c.1
                                        have p3563_1 := h3563c.2.1
                                        have p3563_2 := h3563c.2.2.1
                                        have p3563_3 := h3563c.2.2.2
                                        linarith only [h0, h3372, h3373, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3563_1, u1elo4]
                                      · have p3563_0 := h3563c.1
                                        have p3563_1 := h3563c.2.1
                                        have p3563_2 := h3563c.2.2.1
                                        have p3563_3 := h3563c.2.2.2
                                        linarith only [h3545, hlam, p3563_0]
                                      · have p3563_0 := h3563c.1
                                        have p3563_1 := h3563c.2.1
                                        have p3563_2 := h3563c.2.2.1
                                        have p3563_3 := h3563c.2.2.2
                                        linarith only [hlam, p3563_0]
                                      · have p3563_0 := h3563c.1
                                        have p3563_1 := h3563c.2.1
                                        have p3563_2 := h3563c.2.2.1
                                        have p3563_3 := h3563c.2.2.2
                                        linarith only [h3547, hlam, p3563_0]
                                      · have p3563_0 := h3563c.1
                                        have p3563_1 := h3563c.2.1
                                        have p3563_2 := h3563c.2.2.1
                                        have p3563_3 := h3563c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3563_1, u0elo4]
                                      · have p3563_0 := h3563c.1
                                        have p3563_1 := h3563c.2.1
                                        have p3563_2 := h3563c.2.2.1
                                        have p3563_3 := h3563c.2.2.2
                                        rcases p3563_3 (m.d 0 1) (by simp) with h3589 | h3589
                                        · linarith only [h3373, h3589, hlam]
                                        · linarith only [h0, h3589, hlam]
                                      · have p3563_0 := h3563c.1
                                        have p3563_1 := h3563c.2.1
                                        have p3563_2 := h3563c.2.2.1
                                        have p3563_3 := h3563c.2.2.2
                                        linarith only [h3546, hlam, p3563_0]
                                      · have p3563_0 := h3563c.1
                                        have p3563_1 := h3563c.2.1
                                        have p3563_2 := h3563c.2.2.1
                                        have p3563_3 := h3563c.2.2.2
                                        rcases p3563_3 (m.d 0 1) (by simp) with h3593 | h3593
                                        · linarith only [h3373, h3593, hlam]
                                        · linarith only [h3372, h3593, hlam]
                                      · have p3563_0 := h3563c.1
                                        have p3563_1 := h3563c.2.1
                                        have p3563_2 := h3563c.2.2.1
                                        have p3563_3 := h3563c.2.2.2
                                        linarith only [hlam, p3563_0]
                                · linarith only [h0, h1, h3521, h3546, h3558, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                              · linarith only [h1, h3372, h3549, h3551, h3557, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h1, h3546, h3554, hlam]
                        · linarith only [h1, h3372, h3551, h3553, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3601 | h3601
                  · linarith only [h3372, h3373, h3601, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3603 | h3603
                    · linarith only [h0, h3373, h3521, h3603, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3605 | h3605
                      · linarith only [h0, h3373, h3523, h3605, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3607 | h3607
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3608 | h3608
                          · linarith only [h1, h3546, h3608, hc01, hlam, hphi, u1elo2]
                          · linarith only [h1, h3372, h3605, h3608, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h3372, h3605, h3607, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h3372, h3545, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3613 | h3613
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3614 | h3614
        · linarith only [h0, h1, h3614, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h3616 | h3616
          · linarith only [h0, h3372, h3616, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3618 | h3618
            · rcases m.htr 0 3 4 (by decide) (by decide) with h3619 | h3619
              · rcases m.htr 0 3 5 (by decide) (by decide) with h3620 | h3620
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3621 | h3621
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3622 | h3622
                    · linarith only [h3614, h3618, h3622, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3624 | h3624
                      · linarith only [h0, h1, h3616, h3624, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3626 | h3626
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3627 | h3627
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3628 | h3628
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3629 | h3629
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3630 | h3630
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3631 | h3631
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3632 | h3632
                                    · rcases h0bigk with h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c
                                      · have p3633_0 := h3633c.1
                                        have p3633_1 := h3633c.2.1
                                        have p3633_2 := h3633c.2.2.1
                                        have p3633_3 := h3633c.2.2.2
                                        linarith only [hlam, p3633_0]
                                      · have p3633_0 := h3633c.1
                                        have p3633_1 := h3633c.2.1
                                        have p3633_2 := h3633c.2.2.1
                                        have p3633_3 := h3633c.2.2.2
                                        linarith only [h3372, h3618, h3626, h3630, h3632, hc45, hlam, hphi, ht01, ht0b, ht5b, p3633_1, u1elo2]
                                      · have p3633_0 := h3633c.1
                                        have p3633_1 := h3633c.2.1
                                        have p3633_2 := h3633c.2.2.1
                                        have p3633_3 := h3633c.2.2.2
                                        linarith only [h1, hlam, p3633_0]
                                      · have p3633_0 := h3633c.1
                                        have p3633_1 := h3633c.2.1
                                        have p3633_2 := h3633c.2.2.1
                                        have p3633_3 := h3633c.2.2.2
                                        linarith only [h3372, hlam, p3633_1]
                                      · have p3633_0 := h3633c.1
                                        have p3633_1 := h3633c.2.1
                                        have p3633_2 := h3633c.2.2.1
                                        have p3633_3 := h3633c.2.2.2
                                        linarith only [h3372, h3626, hc05, hlam, hphi, ht01, ht0b, ht5b, p3633_1, u1elo2]
                                      · have p3633_0 := h3633c.1
                                        have p3633_1 := h3633c.2.1
                                        have p3633_2 := h3633c.2.2.1
                                        have p3633_3 := h3633c.2.2.2
                                        linarith only [h0, hlam, p3633_0]
                                      · have p3633_0 := h3633c.1
                                        have p3633_1 := h3633c.2.1
                                        have p3633_2 := h3633c.2.2.1
                                        have p3633_3 := h3633c.2.2.2
                                        linarith only [hlam, p3633_0]
                                      · have p3633_0 := h3633c.1
                                        have p3633_1 := h3633c.2.1
                                        have p3633_2 := h3633c.2.2.1
                                        have p3633_3 := h3633c.2.2.2
                                        linarith only [h3614, hlam, p3633_0]
                                      · have p3633_0 := h3633c.1
                                        have p3633_1 := h3633c.2.1
                                        have p3633_2 := h3633c.2.2.1
                                        have p3633_3 := h3633c.2.2.2
                                        linarith only [h3616, hlam, p3633_1]
                                      · have p3633_0 := h3633c.1
                                        have p3633_1 := h3633c.2.1
                                        have p3633_2 := h3633c.2.2.1
                                        have p3633_3 := h3633c.2.2.2
                                        linarith only [h0, h3372, h3613, h3626, hc15, hlam, hphi, ht01, ht0b, ht5b, p3633_1, u1elo2]
                                      · have p3633_0 := h3633c.1
                                        have p3633_1 := h3633c.2.1
                                        have p3633_2 := h3633c.2.2.1
                                        have p3633_3 := h3633c.2.2.2
                                        linarith only [h0, h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3633_1, u1elo2]
                                      · have p3633_0 := h3633c.1
                                        have p3633_1 := h3633c.2.1
                                        have p3633_2 := h3633c.2.2.1
                                        have p3633_3 := h3633c.2.2.2
                                        linarith only [h1, h3618, h3630, h3632, hc45, hlam, hphi, ht01, ht0b, ht5b, p3633_1, u1elo2]
                                      · have p3633_0 := h3633c.1
                                        have p3633_1 := h3633c.2.1
                                        have p3633_2 := h3633c.2.2.1
                                        have p3633_3 := h3633c.2.2.2
                                        linarith only [hlam, p3633_0]
                                      · have p3633_0 := h3633c.1
                                        have p3633_1 := h3633c.2.1
                                        have p3633_2 := h3633c.2.2.1
                                        have p3633_3 := h3633c.2.2.2
                                        linarith only [h0, h1, h3372, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3633_1, u1elo2]
                                      · have p3633_0 := h3633c.1
                                        have p3633_1 := h3633c.2.1
                                        have p3633_2 := h3633c.2.2.1
                                        have p3633_3 := h3633c.2.2.2
                                        rcases p3633_3 (m.d 0 1) (by simp) with h3648 | h3648
                                        · linarith only [h1, h3648, hlam]
                                        · linarith only [h3613, h3648, hlam]
                                      · have p3633_0 := h3633c.1
                                        have p3633_1 := h3633c.2.1
                                        have p3633_2 := h3633c.2.2.1
                                        have p3633_3 := h3633c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3633_1, u0elo3]
                                      · have p3633_0 := h3633c.1
                                        have p3633_1 := h3633c.2.1
                                        have p3633_2 := h3633c.2.2.1
                                        have p3633_3 := h3633c.2.2.2
                                        linarith only [h3372, h3618, h3626, h3630, h3632, hc45, hlam, hphi, ht01, ht0b, ht5b, p3633_1, u1elo2]
                                      · have p3633_0 := h3633c.1
                                        have p3633_1 := h3633c.2.1
                                        have p3633_2 := h3633c.2.2.1
                                        have p3633_3 := h3633c.2.2.2
                                        linarith only [h3619, hlam, p3633_0]
                                      · have p3633_0 := h3633c.1
                                        have p3633_1 := h3633c.2.1
                                        have p3633_2 := h3633c.2.2.1
                                        have p3633_3 := h3633c.2.2.2
                                        linarith only [hlam, p3633_0]
                                      · have p3633_0 := h3633c.1
                                        have p3633_1 := h3633c.2.1
                                        have p3633_2 := h3633c.2.2.1
                                        have p3633_3 := h3633c.2.2.2
                                        rcases p3633_3 (m.d 0 1) (by simp) with h3655 | h3655
                                        · linarith only [h3372, h3655, hlam]
                                        · linarith only [h3613, h3655, hlam]
                                      · have p3633_0 := h3633c.1
                                        have p3633_1 := h3633c.2.1
                                        have p3633_2 := h3633c.2.2.1
                                        have p3633_3 := h3633c.2.2.2
                                        linarith only [h3613, hlam, p3633_0]
                                      · have p3633_0 := h3633c.1
                                        have p3633_1 := h3633c.2.1
                                        have p3633_2 := h3633c.2.2.1
                                        have p3633_3 := h3633c.2.2.2
                                        linarith only [h3618, hlam, p3633_1]
                                      · have p3633_0 := h3633c.1
                                        have p3633_1 := h3633c.2.1
                                        have p3633_2 := h3633c.2.2.1
                                        have p3633_3 := h3633c.2.2.2
                                        linarith only [h3620, hlam, p3633_0]
                                      · have p3633_0 := h3633c.1
                                        have p3633_1 := h3633c.2.1
                                        have p3633_2 := h3633c.2.2.1
                                        have p3633_3 := h3633c.2.2.2
                                        linarith only [h3621, hlam, p3633_1]
                                      · have p3633_0 := h3633c.1
                                        have p3633_1 := h3633c.2.1
                                        have p3633_2 := h3633c.2.2.1
                                        have p3633_3 := h3633c.2.2.2
                                        linarith only [hlam, p3633_0]
                                    · linarith only [h3372, h3613, h3626, h3628, h3632, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                                  · linarith only [h3372, h3613, h3624, h3628, h3631, hlam]
                                · linarith only [h0, h3372, h3622, h3626, h3630, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h0, h3372, h3622, h3626, h3629, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h0, h3372, h3628, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h0, h3372, h3626, h3627, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h3619, h3626, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h3372, h3613, h3621, hlam]
                · linarith only [h0, h1, h3618, h3620, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h3672 | h3672
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3673 | h3673
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3674 | h3674
                    · linarith only [h0, h3614, h3674, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3676 | h3676
                      · linarith only [h0, h3372, h3616, h3676, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3678 | h3678
                        · linarith only [h1, h3619, h3678, hc01, hlam, hphi, u1elo2]
                        · linarith only [h0, h1, h3678, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h0, h1, h3618, h3619, h3673, hlam]
                · linarith only [h0, h1, h3618, h3672, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h3683 | h3683
              · rcases m.htr 0 3 5 (by decide) (by decide) with h3684 | h3684
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3685 | h3685
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3686 | h3686
                    · linarith only [h0, h1, h3686, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3688 | h3688
                      · linarith only [h0, h1, h3688, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3690 | h3690
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3691 | h3691
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3692 | h3692
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3693 | h3693
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3694 | h3694
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3695 | h3695
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3696 | h3696
                                    · rcases h0bigk with h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c
                                      · have p3697_0 := h3697c.1
                                        have p3697_1 := h3697c.2.1
                                        have p3697_2 := h3697c.2.2.1
                                        have p3697_3 := h3697c.2.2.2
                                        linarith only [hlam, p3697_0]
                                      · have p3697_0 := h3697c.1
                                        have p3697_1 := h3697c.2.1
                                        have p3697_2 := h3697c.2.2.1
                                        have p3697_3 := h3697c.2.2.2
                                        linarith only [h3372, h3690, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3697_1, u1elo2]
                                      · have p3697_0 := h3697c.1
                                        have p3697_1 := h3697c.2.1
                                        have p3697_2 := h3697c.2.2.1
                                        have p3697_3 := h3697c.2.2.2
                                        linarith only [h1, hlam, p3697_0]
                                      · have p3697_0 := h3697c.1
                                        have p3697_1 := h3697c.2.1
                                        have p3697_2 := h3697c.2.2.1
                                        have p3697_3 := h3697c.2.2.2
                                        linarith only [h3372, hlam, p3697_1]
                                      · have p3697_0 := h3697c.1
                                        have p3697_1 := h3697c.2.1
                                        have p3697_2 := h3697c.2.2.1
                                        have p3697_3 := h3697c.2.2.2
                                        linarith only [h3372, h3690, hc05, hlam, hphi, ht01, ht0b, ht5b, p3697_1, u1elo2]
                                      · have p3697_0 := h3697c.1
                                        have p3697_1 := h3697c.2.1
                                        have p3697_2 := h3697c.2.2.1
                                        have p3697_3 := h3697c.2.2.2
                                        linarith only [h0, hlam, p3697_0]
                                      · have p3697_0 := h3697c.1
                                        have p3697_1 := h3697c.2.1
                                        have p3697_2 := h3697c.2.2.1
                                        have p3697_3 := h3697c.2.2.2
                                        linarith only [hlam, p3697_0]
                                      · have p3697_0 := h3697c.1
                                        have p3697_1 := h3697c.2.1
                                        have p3697_2 := h3697c.2.2.1
                                        have p3697_3 := h3697c.2.2.2
                                        linarith only [h3614, hlam, p3697_0]
                                      · have p3697_0 := h3697c.1
                                        have p3697_1 := h3697c.2.1
                                        have p3697_2 := h3697c.2.2.1
                                        have p3697_3 := h3697c.2.2.2
                                        linarith only [h3616, hlam, p3697_1]
                                      · have p3697_0 := h3697c.1
                                        have p3697_1 := h3697c.2.1
                                        have p3697_2 := h3697c.2.2.1
                                        have p3697_3 := h3697c.2.2.2
                                        linarith only [h3618, hlam, p3697_0]
                                      · have p3697_0 := h3697c.1
                                        have p3697_1 := h3697c.2.1
                                        have p3697_2 := h3697c.2.2.1
                                        have p3697_3 := h3697c.2.2.2
                                        linarith only [h3613, hc15, hlam, hphi, ht0b, ht5b, p3697_1, u0elo2]
                                      · have p3697_0 := h3697c.1
                                        have p3697_1 := h3697c.2.1
                                        have p3697_2 := h3697c.2.2.1
                                        have p3697_3 := h3697c.2.2.2
                                        rcases p3697_3 (m.d 0 1) (by simp) with h3709 | h3709
                                        · linarith only [h1, h3709, hlam]
                                        · linarith only [h0, h3709, hlam]
                                      · have p3697_0 := h3697c.1
                                        have p3697_1 := h3697c.2.1
                                        have p3697_2 := h3697c.2.2.1
                                        have p3697_3 := h3697c.2.2.2
                                        linarith only [hlam, p3697_0]
                                      · have p3697_0 := h3697c.1
                                        have p3697_1 := h3697c.2.1
                                        have p3697_2 := h3697c.2.2.1
                                        have p3697_3 := h3697c.2.2.2
                                        linarith only [h0, h1, h3372, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3697_1, u1elo2]
                                      · have p3697_0 := h3697c.1
                                        have p3697_1 := h3697c.2.1
                                        have p3697_2 := h3697c.2.2.1
                                        have p3697_3 := h3697c.2.2.2
                                        rcases p3697_3 (m.d 0 1) (by simp) with h3714 | h3714
                                        · linarith only [h1, h3714, hlam]
                                        · linarith only [h3613, h3714, hlam]
                                      · have p3697_0 := h3697c.1
                                        have p3697_1 := h3697c.2.1
                                        have p3697_2 := h3697c.2.2.1
                                        have p3697_3 := h3697c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3697_1, u0elo3]
                                      · have p3697_0 := h3697c.1
                                        have p3697_1 := h3697c.2.1
                                        have p3697_2 := h3697c.2.2.1
                                        have p3697_3 := h3697c.2.2.2
                                        rcases p3697_3 (m.d 0 1) (by simp) with h3718 | h3718
                                        · linarith only [h3372, h3718, hlam]
                                        · linarith only [h0, h3718, hlam]
                                      · have p3697_0 := h3697c.1
                                        have p3697_1 := h3697c.2.1
                                        have p3697_2 := h3697c.2.2.1
                                        have p3697_3 := h3697c.2.2.2
                                        linarith only [h3683, hlam, p3697_0]
                                      · have p3697_0 := h3697c.1
                                        have p3697_1 := h3697c.2.1
                                        have p3697_2 := h3697c.2.2.1
                                        have p3697_3 := h3697c.2.2.2
                                        linarith only [hlam, p3697_0]
                                      · have p3697_0 := h3697c.1
                                        have p3697_1 := h3697c.2.1
                                        have p3697_2 := h3697c.2.2.1
                                        have p3697_3 := h3697c.2.2.2
                                        rcases p3697_3 (m.d 0 1) (by simp) with h3723 | h3723
                                        · linarith only [h3372, h3723, hlam]
                                        · linarith only [h3613, h3723, hlam]
                                      · have p3697_0 := h3697c.1
                                        have p3697_1 := h3697c.2.1
                                        have p3697_2 := h3697c.2.2.1
                                        have p3697_3 := h3697c.2.2.2
                                        linarith only [h3613, hlam, p3697_0]
                                      · have p3697_0 := h3697c.1
                                        have p3697_1 := h3697c.2.1
                                        have p3697_2 := h3697c.2.2.1
                                        have p3697_3 := h3697c.2.2.2
                                        linarith only [h0, h1, h3613, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3697_1, u1elo2]
                                      · have p3697_0 := h3697c.1
                                        have p3697_1 := h3697c.2.1
                                        have p3697_2 := h3697c.2.2.1
                                        have p3697_3 := h3697c.2.2.2
                                        linarith only [h3684, hlam, p3697_0]
                                      · have p3697_0 := h3697c.1
                                        have p3697_1 := h3697c.2.1
                                        have p3697_2 := h3697c.2.2.1
                                        have p3697_3 := h3697c.2.2.2
                                        linarith only [h3685, hlam, p3697_1]
                                      · have p3697_0 := h3697c.1
                                        have p3697_1 := h3697c.2.1
                                        have p3697_2 := h3697c.2.2.1
                                        have p3697_3 := h3697c.2.2.2
                                        linarith only [hlam, p3697_0]
                                    · linarith only [h3372, h3613, h3690, h3692, h3696, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                                  · linarith only [h3372, h3613, h3688, h3692, h3695, hlam]
                                · linarith only [h0, h3372, h3686, h3690, h3694, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h0, h3372, h3686, h3690, h3693, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h0, h3372, h3692, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h0, h3372, h3690, h3691, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h3683, h3690, hlam]
                  · linarith only [h3372, h3613, h3685, hlam]
                · linarith only [h1, h3613, h3684, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h3740 | h3740
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3741 | h3741
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3742 | h3742
                    · linarith only [h0, h1, h3742, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3744 | h3744
                      · linarith only [h0, h1, h3744, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3746 | h3746
                        · linarith only [h0, h1, h3683, h3746, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                        · linarith only [h0, h1, h3746, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h1, h3613, h3683, h3741, hlam]
                · linarith only [h1, h3613, h3740, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3751 | h3751
        · linarith only [h0, h1, h3751, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h3753 | h3753
          · linarith only [h0, h3372, h3753, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3755 | h3755
            · linarith only [h0, h3613, h3755, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h3757 | h3757
              · rcases m.htr 0 3 5 (by decide) (by decide) with h3758 | h3758
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3759 | h3759
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3760 | h3760
                    · linarith only [h0, h3751, h3760, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3762 | h3762
                      · linarith only [h0, h1, h3753, h3762, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3764 | h3764
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3765 | h3765
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3766 | h3766
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3767 | h3767
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3768 | h3768
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3769 | h3769
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3770 | h3770
                                    · rcases h0bigk with h3771c | h3771c | h3771c | h3771c | h3771c | h3771c | h3771c | h3771c | h3771c | h3771c | h3771c | h3771c | h3771c | h3771c | h3771c | h3771c | h3771c | h3771c | h3771c | h3771c | h3771c | h3771c | h3771c | h3771c | h3771c
                                      · have p3771_0 := h3771c.1
                                        have p3771_1 := h3771c.2.1
                                        have p3771_2 := h3771c.2.2.1
                                        have p3771_3 := h3771c.2.2.2
                                        linarith only [hlam, p3771_0]
                                      · have p3771_0 := h3771c.1
                                        have p3771_1 := h3771c.2.1
                                        have p3771_2 := h3771c.2.2.1
                                        have p3771_3 := h3771c.2.2.2
                                        linarith only [h3613, h3764, h3766, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3771_1, u1elo2]
                                      · have p3771_0 := h3771c.1
                                        have p3771_1 := h3771c.2.1
                                        have p3771_2 := h3771c.2.2.1
                                        have p3771_3 := h3771c.2.2.2
                                        linarith only [h1, hlam, p3771_0]
                                      · have p3771_0 := h3771c.1
                                        have p3771_1 := h3771c.2.1
                                        have p3771_2 := h3771c.2.2.1
                                        have p3771_3 := h3771c.2.2.2
                                        linarith only [h3372, hlam, p3771_1]
                                      · have p3771_0 := h3771c.1
                                        have p3771_1 := h3771c.2.1
                                        have p3771_2 := h3771c.2.2.1
                                        have p3771_3 := h3771c.2.2.2
                                        linarith only [h3613, hlam, p3771_1]
                                      · have p3771_0 := h3771c.1
                                        have p3771_1 := h3771c.2.1
                                        have p3771_2 := h3771c.2.2.1
                                        have p3771_3 := h3771c.2.2.2
                                        linarith only [h0, hlam, p3771_0]
                                      · have p3771_0 := h3771c.1
                                        have p3771_1 := h3771c.2.1
                                        have p3771_2 := h3771c.2.2.1
                                        have p3771_3 := h3771c.2.2.2
                                        linarith only [hlam, p3771_0]
                                      · have p3771_0 := h3771c.1
                                        have p3771_1 := h3771c.2.1
                                        have p3771_2 := h3771c.2.2.1
                                        have p3771_3 := h3771c.2.2.2
                                        linarith only [h3751, hlam, p3771_0]
                                      · have p3771_0 := h3771c.1
                                        have p3771_1 := h3771c.2.1
                                        have p3771_2 := h3771c.2.2.1
                                        have p3771_3 := h3771c.2.2.2
                                        linarith only [h3753, hlam, p3771_1]
                                      · have p3771_0 := h3771c.1
                                        have p3771_1 := h3771c.2.1
                                        have p3771_2 := h3771c.2.2.1
                                        have p3771_3 := h3771c.2.2.2
                                        linarith only [h3755, hlam, p3771_0]
                                      · have p3771_0 := h3771c.1
                                        have p3771_1 := h3771c.2.1
                                        have p3771_2 := h3771c.2.2.1
                                        have p3771_3 := h3771c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3771_1, u0elo2]
                                      · have p3771_0 := h3771c.1
                                        have p3771_1 := h3771c.2.1
                                        have p3771_2 := h3771c.2.2.1
                                        have p3771_3 := h3771c.2.2.2
                                        rcases p3771_3 (m.d 0 1) (by simp) with h3783 | h3783
                                        · linarith only [h1, h3783, hlam]
                                        · linarith only [h0, h3783, hlam]
                                      · have p3771_0 := h3771c.1
                                        have p3771_1 := h3771c.2.1
                                        have p3771_2 := h3771c.2.2.1
                                        have p3771_3 := h3771c.2.2.2
                                        linarith only [hlam, p3771_0]
                                      · have p3771_0 := h3771c.1
                                        have p3771_1 := h3771c.2.1
                                        have p3771_2 := h3771c.2.2.1
                                        have p3771_3 := h3771c.2.2.2
                                        linarith only [h0, h1, h3613, h3759, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3771_1, u1elo2]
                                      · have p3771_0 := h3771c.1
                                        have p3771_1 := h3771c.2.1
                                        have p3771_2 := h3771c.2.2.1
                                        have p3771_3 := h3771c.2.2.2
                                        linarith only [h0, h1, h3613, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3771_1, u1elo2]
                                      · have p3771_0 := h3771c.1
                                        have p3771_1 := h3771c.2.1
                                        have p3771_2 := h3771c.2.2.1
                                        have p3771_3 := h3771c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3771_1, u0elo3]
                                      · have p3771_0 := h3771c.1
                                        have p3771_1 := h3771c.2.1
                                        have p3771_2 := h3771c.2.2.1
                                        have p3771_3 := h3771c.2.2.2
                                        rcases p3771_3 (m.d 0 1) (by simp) with h3790 | h3790
                                        · linarith only [h3372, h3790, hlam]
                                        · linarith only [h0, h3790, hlam]
                                      · have p3771_0 := h3771c.1
                                        have p3771_1 := h3771c.2.1
                                        have p3771_2 := h3771c.2.2.1
                                        have p3771_3 := h3771c.2.2.2
                                        linarith only [h3757, hlam, p3771_0]
                                      · have p3771_0 := h3771c.1
                                        have p3771_1 := h3771c.2.1
                                        have p3771_2 := h3771c.2.2.1
                                        have p3771_3 := h3771c.2.2.2
                                        linarith only [hlam, p3771_0]
                                      · have p3771_0 := h3771c.1
                                        have p3771_1 := h3771c.2.1
                                        have p3771_2 := h3771c.2.2.1
                                        have p3771_3 := h3771c.2.2.2
                                        linarith only [h0, h3372, h3613, h3764, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3771_1, u1elo2]
                                      · have p3771_0 := h3771c.1
                                        have p3771_1 := h3771c.2.1
                                        have p3771_2 := h3771c.2.2.1
                                        have p3771_3 := h3771c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3771_1, u0elo4]
                                      · have p3771_0 := h3771c.1
                                        have p3771_1 := h3771c.2.1
                                        have p3771_2 := h3771c.2.2.1
                                        have p3771_3 := h3771c.2.2.2
                                        rcases p3771_3 (m.d 0 1) (by simp) with h3797 | h3797
                                        · linarith only [h3613, h3797, hlam]
                                        · linarith only [h0, h3797, hlam]
                                      · have p3771_0 := h3771c.1
                                        have p3771_1 := h3771c.2.1
                                        have p3771_2 := h3771c.2.2.1
                                        have p3771_3 := h3771c.2.2.2
                                        linarith only [h3758, hlam, p3771_0]
                                      · have p3771_0 := h3771c.1
                                        have p3771_1 := h3771c.2.1
                                        have p3771_2 := h3771c.2.2.1
                                        have p3771_3 := h3771c.2.2.2
                                        linarith only [h3759, hlam, p3771_1]
                                      · have p3771_0 := h3771c.1
                                        have p3771_1 := h3771c.2.1
                                        have p3771_2 := h3771c.2.2.1
                                        have p3771_3 := h3771c.2.2.2
                                        linarith only [hlam, p3771_0]
                                    · rcases h0bigk with h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c
                                      · have p3803_0 := h3803c.1
                                        have p3803_1 := h3803c.2.1
                                        have p3803_2 := h3803c.2.2.1
                                        have p3803_3 := h3803c.2.2.2
                                        linarith only [hlam, p3803_0]
                                      · have p3803_0 := h3803c.1
                                        have p3803_1 := h3803c.2.1
                                        have p3803_2 := h3803c.2.2.1
                                        have p3803_3 := h3803c.2.2.2
                                        linarith only [h0, h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3803_1, u1elo2]
                                      · have p3803_0 := h3803c.1
                                        have p3803_1 := h3803c.2.1
                                        have p3803_2 := h3803c.2.2.1
                                        have p3803_3 := h3803c.2.2.2
                                        linarith only [h1, hlam, p3803_0]
                                      · have p3803_0 := h3803c.1
                                        have p3803_1 := h3803c.2.1
                                        have p3803_2 := h3803c.2.2.1
                                        have p3803_3 := h3803c.2.2.2
                                        linarith only [h3372, hlam, p3803_1]
                                      · have p3803_0 := h3803c.1
                                        have p3803_1 := h3803c.2.1
                                        have p3803_2 := h3803c.2.2.1
                                        have p3803_3 := h3803c.2.2.2
                                        linarith only [h3613, hlam, p3803_1]
                                      · have p3803_0 := h3803c.1
                                        have p3803_1 := h3803c.2.1
                                        have p3803_2 := h3803c.2.2.1
                                        have p3803_3 := h3803c.2.2.2
                                        linarith only [h0, hlam, p3803_0]
                                      · have p3803_0 := h3803c.1
                                        have p3803_1 := h3803c.2.1
                                        have p3803_2 := h3803c.2.2.1
                                        have p3803_3 := h3803c.2.2.2
                                        linarith only [hlam, p3803_0]
                                      · have p3803_0 := h3803c.1
                                        have p3803_1 := h3803c.2.1
                                        have p3803_2 := h3803c.2.2.1
                                        have p3803_3 := h3803c.2.2.2
                                        linarith only [h3751, hlam, p3803_0]
                                      · have p3803_0 := h3803c.1
                                        have p3803_1 := h3803c.2.1
                                        have p3803_2 := h3803c.2.2.1
                                        have p3803_3 := h3803c.2.2.2
                                        linarith only [h3753, hlam, p3803_1]
                                      · have p3803_0 := h3803c.1
                                        have p3803_1 := h3803c.2.1
                                        have p3803_2 := h3803c.2.2.1
                                        have p3803_3 := h3803c.2.2.2
                                        linarith only [h3755, hlam, p3803_0]
                                      · have p3803_0 := h3803c.1
                                        have p3803_1 := h3803c.2.1
                                        have p3803_2 := h3803c.2.2.1
                                        have p3803_3 := h3803c.2.2.2
                                        linarith only [h1, hc01, hlam, hphi, p3803_1, u1elo2]
                                      · have p3803_0 := h3803c.1
                                        have p3803_1 := h3803c.2.1
                                        have p3803_2 := h3803c.2.2.1
                                        have p3803_3 := h3803c.2.2.2
                                        rcases p3803_3 (m.d 0 1) (by simp) with h3815 | h3815
                                        · linarith only [h1, h3815, hlam]
                                        · linarith only [h0, h3815, hlam]
                                      · have p3803_0 := h3803c.1
                                        have p3803_1 := h3803c.2.1
                                        have p3803_2 := h3803c.2.2.1
                                        have p3803_3 := h3803c.2.2.2
                                        linarith only [hlam, p3803_0]
                                      · have p3803_0 := h3803c.1
                                        have p3803_1 := h3803c.2.1
                                        have p3803_2 := h3803c.2.2.1
                                        have p3803_3 := h3803c.2.2.2
                                        linarith only [h1, h3759, h3770, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3803_1, u1elo2]
                                      · have p3803_0 := h3803c.1
                                        have p3803_1 := h3803c.2.1
                                        have p3803_2 := h3803c.2.2.1
                                        have p3803_3 := h3803c.2.2.2
                                        linarith only [h0, h1, h3613, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3803_1, u1elo2]
                                      · have p3803_0 := h3803c.1
                                        have p3803_1 := h3803c.2.1
                                        have p3803_2 := h3803c.2.2.1
                                        have p3803_3 := h3803c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3803_1, u0elo3]
                                      · have p3803_0 := h3803c.1
                                        have p3803_1 := h3803c.2.1
                                        have p3803_2 := h3803c.2.2.1
                                        have p3803_3 := h3803c.2.2.2
                                        rcases p3803_3 (m.d 0 1) (by simp) with h3822 | h3822
                                        · linarith only [h3372, h3822, hlam]
                                        · linarith only [h0, h3822, hlam]
                                      · have p3803_0 := h3803c.1
                                        have p3803_1 := h3803c.2.1
                                        have p3803_2 := h3803c.2.2.1
                                        have p3803_3 := h3803c.2.2.2
                                        linarith only [h3757, hlam, p3803_0]
                                      · have p3803_0 := h3803c.1
                                        have p3803_1 := h3803c.2.1
                                        have p3803_2 := h3803c.2.2.1
                                        have p3803_3 := h3803c.2.2.2
                                        linarith only [hlam, p3803_0]
                                      · have p3803_0 := h3803c.1
                                        have p3803_1 := h3803c.2.1
                                        have p3803_2 := h3803c.2.2.1
                                        have p3803_3 := h3803c.2.2.2
                                        linarith only [h0, h3372, h3613, h3764, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3803_1, u1elo2]
                                      · have p3803_0 := h3803c.1
                                        have p3803_1 := h3803c.2.1
                                        have p3803_2 := h3803c.2.2.1
                                        have p3803_3 := h3803c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3803_1, u0elo4]
                                      · have p3803_0 := h3803c.1
                                        have p3803_1 := h3803c.2.1
                                        have p3803_2 := h3803c.2.2.1
                                        have p3803_3 := h3803c.2.2.2
                                        rcases p3803_3 (m.d 0 1) (by simp) with h3829 | h3829
                                        · linarith only [h3613, h3829, hlam]
                                        · linarith only [h0, h3829, hlam]
                                      · have p3803_0 := h3803c.1
                                        have p3803_1 := h3803c.2.1
                                        have p3803_2 := h3803c.2.2.1
                                        have p3803_3 := h3803c.2.2.2
                                        linarith only [h3758, hlam, p3803_0]
                                      · have p3803_0 := h3803c.1
                                        have p3803_1 := h3803c.2.1
                                        have p3803_2 := h3803c.2.2.1
                                        have p3803_3 := h3803c.2.2.2
                                        linarith only [h3759, hlam, p3803_1]
                                      · have p3803_0 := h3803c.1
                                        have p3803_1 := h3803c.2.1
                                        have p3803_2 := h3803c.2.2.1
                                        have p3803_3 := h3803c.2.2.2
                                        linarith only [hlam, p3803_0]
                                  · linarith only [h0, h3372, h3762, h3769, hc12, hc45, hlam, hphi, ht23, ht34]
                                · linarith only [h0, h1, h3760, h3768, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h0, h1, h3760, h3767, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h0, h3372, h3759, h3766, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                          · linarith only [h1, h3758, h3765, hlam]
                        · linarith only [h1, h3757, h3764, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3841 | h3841
                    · linarith only [h0, h3372, h3841, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3843 | h3843
                      · linarith only [h0, h3372, h3843, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3845 | h3845
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3846 | h3846
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3847 | h3847
                            · linarith only [h0, h3372, h3759, h3845, h3847, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                            · linarith only [h0, h3372, h3847, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h0, h1, h3758, h3846, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h1, h3757, h3845, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3852 | h3852
                  · linarith only [h3757, h3758, h3852, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3854 | h3854
                    · linarith only [h0, h1, h3854, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3856 | h3856
                      · linarith only [h0, h1, h3753, h3856, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3858 | h3858
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3859 | h3859
                          · linarith only [h3757, h3758, h3859, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                          · linarith only [h0, h3372, h3858, h3859, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h3858, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h3863 | h3863
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3864 | h3864
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3865 | h3865
                    · linarith only [h0, h1, h3865, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3867 | h3867
                      · linarith only [h0, h1, h3867, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3869 | h3869
                        · linarith only [h0, h3613, h3757, h3863, h3869, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                        · linarith only [h0, h1, h3869, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h3757, h3863, h3864, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3873 | h3873
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3874 | h3874
                    · linarith only [h0, h1, h3874, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3876 | h3876
                      · linarith only [h0, h1, h3876, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3878 | h3878
                        · linarith only [h0, h1, h3757, h3878, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                        · linarith only [h0, h1, h3878, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3881 | h3881
                    · linarith only [h0, h1, h3881, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3883 | h3883
                      · linarith only [h0, h1, h3883, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3885 | h3885
                        · linarith only [h0, h1, h3757, h3885, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                        · linarith only [h0, h1, h3885, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 12148000 in
set_option maxHeartbeats 12148000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h0bigk := hb0.2.2.2
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  exact r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s0 m hb0 hb1 hb3 hb4 h0

end R2N4
