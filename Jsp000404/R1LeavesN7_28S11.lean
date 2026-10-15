import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5198000 in
set_option maxHeartbeats 5198000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_s1_x1_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1833 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2722 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3122 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3210 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3211 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h5ehi := hb5.1
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
  have h0 := hg0
  have h1833 := hg1833
  rcases m.htr 0 2 5 (by decide) (by decide) with h3212 | h3212
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3213 | h3213
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3214 | h3214
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3215 | h3215
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3216 | h3216
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3217 | h3217
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3218 | h3218
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3219 | h3219
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3220 | h3220
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3221 | h3221
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3222 | h3222
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3223 | h3223
                        · linarith only [h3210, h3223, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                        · linarith only [h3210, h3214, h3222, h3223, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3226 | h3226
                        · linarith only [h3210, h3226, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3228 | h3228
                          · linarith only [h3211, h3228, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3230 | h3230
                            · linarith only [h3210, h3213, h3222, h3228, h3230, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · linarith only [h3210, h3213, h3215, h3222, h3230, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h2722, h3210, h3213, h3215, h3221, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h1833, h3214, h3220, hlam]
                · linarith only [h1833, h3213, h3219, hlam]
              · linarith only [h0, h3212, h3218, hlam]
            · linarith only [h0, h3211, h3217, hlam]
          · linarith only [h0, h3210, h3216, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3239 | h3239
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3240 | h3240
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3241 | h3241
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3242 | h3242
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3243 | h3243
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3244 | h3244
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3245 | h3245
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3246 | h3246
                        · linarith only [h3210, h3246, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                        · linarith only [h3214, h3245, h3246, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3249 | h3249
                        · linarith only [h3210, h3249, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3251 | h3251
                          · linarith only [h3213, h3215, h3245, h3251, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3253 | h3253
                            · linarith only [h3213, h3215, h3253, hlam]
                            · rcases h0bigk with h3255c | h3255c | h3255c | h3255c | h3255c | h3255c | h3255c | h3255c | h3255c | h3255c | h3255c | h3255c | h3255c | h3255c | h3255c | h3255c | h3255c | h3255c | h3255c | h3255c | h3255c | h3255c | h3255c | h3255c | h3255c
                              · have p3255_0 := h3255c.1
                                have p3255_1 := h3255c.2.1
                                have p3255_2 := h3255c.2.2.1
                                have p3255_3 := h3255c.2.2.2
                                linarith only [hlam, p3255_0]
                              · have p3255_0 := h3255c.1
                                have p3255_1 := h3255c.2.1
                                have p3255_2 := h3255c.2.2.1
                                have p3255_3 := h3255c.2.2.2
                                linarith only [h0, hlam, p3255_1]
                              · have p3255_0 := h3255c.1
                                have p3255_1 := h3255c.2.1
                                have p3255_2 := h3255c.2.2.1
                                have p3255_3 := h3255c.2.2.2
                                linarith only [h1833, hlam, p3255_0]
                              · have p3255_0 := h3255c.1
                                have p3255_1 := h3255c.2.1
                                have p3255_2 := h3255c.2.2.1
                                have p3255_3 := h3255c.2.2.2
                                linarith only [h2722, hlam, p3255_1]
                              · have p3255_0 := h3255c.1
                                have p3255_1 := h3255c.2.1
                                have p3255_2 := h3255c.2.2.1
                                have p3255_3 := h3255c.2.2.2
                                linarith only [h3122, hlam, p3255_1]
                              · have p3255_0 := h3255c.1
                                have p3255_1 := h3255c.2.1
                                have p3255_2 := h3255c.2.2.1
                                have p3255_3 := h3255c.2.2.2
                                rcases p3255_3 (m.d 0 1) (by simp) with h3261 | h3261
                                · linarith only [h0, h3261, hlam]
                                · rcases p3255_3 (m.d 0 2) (by simp) with h3263 | h3263
                                  · rcases p3255_3 (m.d 0 3) (by simp) with h3264 | h3264
                                    · linarith only [h3210, h3264, hlam]
                                    · linarith only [h1833, h3264, hlam]
                                  · linarith only [h0, h3263, hlam]
                              · have p3255_0 := h3255c.1
                                have p3255_1 := h3255c.2.1
                                have p3255_2 := h3255c.2.2.1
                                have p3255_3 := h3255c.2.2.2
                                linarith only [hlam, p3255_0]
                              · have p3255_0 := h3255c.1
                                have p3255_1 := h3255c.2.1
                                have p3255_2 := h3255c.2.2.1
                                have p3255_3 := h3255c.2.2.2
                                linarith only [h3213, h3245, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3255_1, u0elo1]
                              · have p3255_0 := h3255c.1
                                have p3255_1 := h3255c.2.1
                                have p3255_2 := h3255c.2.2.1
                                have p3255_3 := h3255c.2.2.2
                                linarith only [h3213, h3245, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3255_1, u0elo1]
                              · have p3255_0 := h3255c.1
                                have p3255_1 := h3255c.2.1
                                have p3255_2 := h3255c.2.2.1
                                have p3255_3 := h3255c.2.2.2
                                linarith only [h3212, hlam, hphi, ht0b, ht5b, p3255_1, u0elo1, u5ehi2]
                              · have p3255_0 := h3255c.1
                                have p3255_1 := h3255c.2.1
                                have p3255_2 := h3255c.2.2.1
                                have p3255_3 := h3255c.2.2.2
                                rcases p3255_3 (m.d 0 1) (by simp) with h3272 | h3272
                                · linarith only [h1833, h3272, hlam]
                                · rcases p3255_3 (m.d 0 2) (by simp) with h3274 | h3274
                                  · rcases p3255_3 (m.d 0 3) (by simp) with h3275 | h3275
                                    · rcases p3255_3 (m.d 0 4) (by simp) with h3276 | h3276
                                      · linarith only [h3213, h3276, hlam]
                                      · linarith only [h2722, h3276, hlam]
                                    · linarith only [h1833, h3275, hlam]
                                  · linarith only [h0, h3274, hlam]
                              · have p3255_0 := h3255c.1
                                have p3255_1 := h3255c.2.1
                                have p3255_2 := h3255c.2.2.1
                                have p3255_3 := h3255c.2.2.2
                                linarith only [h3210, hlam, p3255_1]
                              · have p3255_0 := h3255c.1
                                have p3255_1 := h3255c.2.1
                                have p3255_2 := h3255c.2.2.1
                                have p3255_3 := h3255c.2.2.2
                                linarith only [hlam, p3255_0]
                              · have p3255_0 := h3255c.1
                                have p3255_1 := h3255c.2.1
                                have p3255_2 := h3255c.2.2.1
                                have p3255_3 := h3255c.2.2.2
                                linarith only [h3210, h3213, h3245, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3255_1, u0elo1]
                              · have p3255_0 := h3255c.1
                                have p3255_1 := h3255c.2.1
                                have p3255_2 := h3255c.2.2.1
                                have p3255_3 := h3255c.2.2.2
                                linarith only [h3210, h3214, h3245, h3253, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3255_1, u0elo1]
                              · have p3255_0 := h3255c.1
                                have p3255_1 := h3255c.2.1
                                have p3255_2 := h3255c.2.2.1
                                have p3255_3 := h3255c.2.2.2
                                linarith only [h3215, h3239, h3242, h3244, hc01, hc12, hlam, hphi, p3255_1]
                              · have p3255_0 := h3255c.1
                                have p3255_1 := h3255c.2.1
                                have p3255_2 := h3255c.2.2.1
                                have p3255_3 := h3255c.2.2.2
                                linarith only [h3211, hlam, p3255_0]
                              · have p3255_0 := h3255c.1
                                have p3255_1 := h3255c.2.1
                                have p3255_2 := h3255c.2.2.1
                                have p3255_3 := h3255c.2.2.2
                                linarith only [h3213, hlam, p3255_0]
                              · have p3255_0 := h3255c.1
                                have p3255_1 := h3255c.2.1
                                have p3255_2 := h3255c.2.2.1
                                have p3255_3 := h3255c.2.2.2
                                linarith only [hlam, p3255_0]
                              · have p3255_0 := h3255c.1
                                have p3255_1 := h3255c.2.1
                                have p3255_2 := h3255c.2.2.1
                                have p3255_3 := h3255c.2.2.2
                                linarith only [h3215, hlam, p3255_0]
                              · have p3255_0 := h3255c.1
                                have p3255_1 := h3255c.2.1
                                have p3255_2 := h3255c.2.2.1
                                have p3255_3 := h3255c.2.2.2
                                linarith only [h3215, h3239, h3242, h3244, hc01, hc12, hlam, hphi, p3255_1]
                              · have p3255_0 := h3255c.1
                                have p3255_1 := h3255c.2.1
                                have p3255_2 := h3255c.2.2.1
                                have p3255_3 := h3255c.2.2.2
                                linarith only [h3212, hlam, p3255_1]
                              · have p3255_0 := h3255c.1
                                have p3255_1 := h3255c.2.1
                                have p3255_2 := h3255c.2.2.1
                                have p3255_3 := h3255c.2.2.2
                                linarith only [h3214, hlam, p3255_0]
                              · have p3255_0 := h3255c.1
                                have p3255_1 := h3255c.2.1
                                have p3255_2 := h3255c.2.2.1
                                have p3255_3 := h3255c.2.2.2
                                linarith only [h2722, h3215, h3239, h3242, h3244, hc01, hc12, hlam, hphi, p3255_1]
                              · have p3255_0 := h3255c.1
                                have p3255_1 := h3255c.2.1
                                have p3255_2 := h3255c.2.2.1
                                have p3255_3 := h3255c.2.2.2
                                linarith only [hlam, p3255_0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3295 | h3295
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3296 | h3296
                        · linarith only [h3210, h3296, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                        · linarith only [h3210, h3214, h3295, h3296, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3299 | h3299
                        · linarith only [h3213, h3295, h3299, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3301 | h3301
                          · linarith only [h2722, h3210, h3213, h3244, h3295, h3301, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3303 | h3303
                            · linarith only [h2722, h3213, h3244, h3303, hlam]
                            · rcases h0bigk with h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [hlam, p3305_0]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [h0, hlam, p3305_1]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [h1833, hlam, p3305_0]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [h2722, hlam, p3305_1]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [h3122, hlam, p3305_1]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                rcases p3305_3 (m.d 0 1) (by simp) with h3311 | h3311
                                · linarith only [h0, h3311, hlam]
                                · rcases p3305_3 (m.d 0 2) (by simp) with h3313 | h3313
                                  · rcases p3305_3 (m.d 0 3) (by simp) with h3314 | h3314
                                    · linarith only [h3210, h3314, hlam]
                                    · linarith only [h1833, h3314, hlam]
                                  · linarith only [h0, h3313, hlam]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [hlam, p3305_0]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [h3214, hlam, hphi, ht0b, ht5b, p3305_1, u0elo1, u5ehi0]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [h3213, h3295, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3305_1, u0elo1]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht5b, p3305_1, u0elo1, u5ehi0]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                rcases p3305_3 (m.d 0 1) (by simp) with h3322 | h3322
                                · linarith only [h1833, h3322, hlam]
                                · rcases p3305_3 (m.d 0 2) (by simp) with h3324 | h3324
                                  · rcases p3305_3 (m.d 0 3) (by simp) with h3325 | h3325
                                    · rcases p3305_3 (m.d 0 4) (by simp) with h3326 | h3326
                                      · linarith only [h3213, h3326, hlam]
                                      · linarith only [h2722, h3326, hlam]
                                    · linarith only [h1833, h3325, hlam]
                                  · linarith only [h0, h3324, hlam]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [h3210, hlam, p3305_1]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [hlam, p3305_0]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [h3210, h3213, h3295, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3305_1, u0elo1]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [h3210, h3214, h3295, h3303, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3305_1, u0elo1]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [h2722, h3244, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3305_1]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [h3211, hlam, p3305_0]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [h3213, hlam, p3305_0]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [hlam, p3305_0]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [h3215, hlam, p3305_0]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                rcases p3305_3 (m.d 0 1) (by simp) with h3340 | h3340
                                · linarith only [h3122, h3340, hlam]
                                · rcases p3305_3 (m.d 0 2) (by simp) with h3342 | h3342
                                  · rcases p3305_3 (m.d 0 3) (by simp) with h3343 | h3343
                                    · rcases p3305_3 (m.d 0 4) (by simp) with h3344 | h3344
                                      · linarith only [h3215, h3344, hlam]
                                      · linarith only [h2722, h3344, hlam]
                                    · linarith only [h1833, h3343, hlam]
                                  · linarith only [h0, h3342, hlam]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [h3212, hlam, p3305_1]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [h3214, hlam, p3305_0]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [h3210, h3213, h3214, h3295, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3305_1, u0elo1]
                              · have p3305_0 := h3305c.1
                                have p3305_1 := h3305c.2.1
                                have p3305_2 := h3305c.2.2.1
                                have p3305_3 := h3305c.2.2.2
                                linarith only [hlam, p3305_0]
                  · linarith only [h1833, h3214, h3243, hlam]
                · linarith only [h1833, h3213, h3214, h3242, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi3]
              · linarith only [h0, h3212, h3241, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h3210, h3211, h3214, h3240, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi3]
          · linarith only [h0, h3210, h3239, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3358 | h3358
        · linarith only [h3213, h3214, h3358, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3360 | h3360
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3361 | h3361
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3362 | h3362
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3363 | h3363
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3364 | h3364
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3365 | h3365
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3366 | h3366
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3367 | h3367
                        · linarith only [h2722, h3210, h3213, h3214, h3367, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3369 | h3369
                          · linarith only [h3211, h3358, h3369, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3371 | h3371
                            · linarith only [h2722, h3210, h3358, h3366, h3371, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                            · rcases h0bigk with h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c
                              · have p3373_0 := h3373c.1
                                have p3373_1 := h3373c.2.1
                                have p3373_2 := h3373c.2.2.1
                                have p3373_3 := h3373c.2.2.2
                                linarith only [hlam, p3373_0]
                              · have p3373_0 := h3373c.1
                                have p3373_1 := h3373c.2.1
                                have p3373_2 := h3373c.2.2.1
                                have p3373_3 := h3373c.2.2.2
                                linarith only [h0, hlam, p3373_1]
                              · have p3373_0 := h3373c.1
                                have p3373_1 := h3373c.2.1
                                have p3373_2 := h3373c.2.2.1
                                have p3373_3 := h3373c.2.2.2
                                linarith only [h1833, hlam, p3373_0]
                              · have p3373_0 := h3373c.1
                                have p3373_1 := h3373c.2.1
                                have p3373_2 := h3373c.2.2.1
                                have p3373_3 := h3373c.2.2.2
                                linarith only [h2722, hlam, p3373_1]
                              · have p3373_0 := h3373c.1
                                have p3373_1 := h3373c.2.1
                                have p3373_2 := h3373c.2.2.1
                                have p3373_3 := h3373c.2.2.2
                                linarith only [h3122, hlam, p3373_1]
                              · have p3373_0 := h3373c.1
                                have p3373_1 := h3373c.2.1
                                have p3373_2 := h3373c.2.2.1
                                have p3373_3 := h3373c.2.2.2
                                rcases p3373_3 (m.d 0 1) (by simp) with h3379 | h3379
                                · linarith only [h0, h3379, hlam]
                                · rcases p3373_3 (m.d 0 2) (by simp) with h3381 | h3381
                                  · rcases p3373_3 (m.d 0 3) (by simp) with h3382 | h3382
                                    · linarith only [h3210, h3382, hlam]
                                    · linarith only [h1833, h3382, hlam]
                                  · linarith only [h0, h3381, hlam]
                              · have p3373_0 := h3373c.1
                                have p3373_1 := h3373c.2.1
                                have p3373_2 := h3373c.2.2.1
                                have p3373_3 := h3373c.2.2.2
                                linarith only [hlam, p3373_0]
                              · have p3373_0 := h3373c.1
                                have p3373_1 := h3373c.2.1
                                have p3373_2 := h3373c.2.2.1
                                have p3373_3 := h3373c.2.2.2
                                linarith only [h3210, h3366, hc34, hlam, hphi, ht0b, ht45, ht5b, p3373_1, u0elo1]
                              · have p3373_0 := h3373c.1
                                have p3373_1 := h3373c.2.1
                                have p3373_2 := h3373c.2.2.1
                                have p3373_3 := h3373c.2.2.2
                                rcases p3373_3 (m.d 0 1) (by simp) with h3388 | h3388
                                · linarith only [h0, h3388, hlam]
                                · rcases p3373_3 (m.d 0 2) (by simp) with h3390 | h3390
                                  · rcases p3373_3 (m.d 0 3) (by simp) with h3391 | h3391
                                    · linarith only [h3210, h3391, hlam]
                                    · linarith only [h3213, h3391, hlam]
                                  · linarith only [h3211, h3390, hlam]
                              · have p3373_0 := h3373c.1
                                have p3373_1 := h3373c.2.1
                                have p3373_2 := h3373c.2.2.1
                                have p3373_3 := h3373c.2.2.2
                                linarith only [h3210, h3214, h3366, hc34, hlam, hphi, ht0b, ht45, ht5b, p3373_1, u0elo1]
                              · have p3373_0 := h3373c.1
                                have p3373_1 := h3373c.2.1
                                have p3373_2 := h3373c.2.2.1
                                have p3373_3 := h3373c.2.2.2
                                linarith only [h3214, h3360, h3363, h3365, h3371, hc01, hc12, hlam, hphi, p3373_1]
                              · have p3373_0 := h3373c.1
                                have p3373_1 := h3373c.2.1
                                have p3373_2 := h3373c.2.2.1
                                have p3373_3 := h3373c.2.2.2
                                linarith only [h3210, hlam, p3373_1]
                              · have p3373_0 := h3373c.1
                                have p3373_1 := h3373c.2.1
                                have p3373_2 := h3373c.2.2.1
                                have p3373_3 := h3373c.2.2.2
                                linarith only [hlam, p3373_0]
                              · have p3373_0 := h3373c.1
                                have p3373_1 := h3373c.2.1
                                have p3373_2 := h3373c.2.2.1
                                have p3373_3 := h3373c.2.2.2
                                linarith only [h2722, h3214, h3360, h3363, h3365, h3371, hc01, hc12, hlam, hphi, p3373_1]
                              · have p3373_0 := h3373c.1
                                have p3373_1 := h3373c.2.1
                                have p3373_2 := h3373c.2.2.1
                                have p3373_3 := h3373c.2.2.2
                                linarith only [h3214, hlam, p3373_1]
                              · have p3373_0 := h3373c.1
                                have p3373_1 := h3373c.2.1
                                have p3373_2 := h3373c.2.2.1
                                have p3373_3 := h3373c.2.2.2
                                linarith only [h3213, h3214, h3360, h3363, h3365, h3371, hc01, hc12, hlam, hphi, p3373_1]
                              · have p3373_0 := h3373c.1
                                have p3373_1 := h3373c.2.1
                                have p3373_2 := h3373c.2.2.1
                                have p3373_3 := h3373c.2.2.2
                                linarith only [h3211, hlam, p3373_0]
                              · have p3373_0 := h3373c.1
                                have p3373_1 := h3373c.2.1
                                have p3373_2 := h3373c.2.2.1
                                have p3373_3 := h3373c.2.2.2
                                linarith only [h3213, hlam, p3373_0]
                              · have p3373_0 := h3373c.1
                                have p3373_1 := h3373c.2.1
                                have p3373_2 := h3373c.2.2.1
                                have p3373_3 := h3373c.2.2.2
                                linarith only [hlam, p3373_0]
                              · have p3373_0 := h3373c.1
                                have p3373_1 := h3373c.2.1
                                have p3373_2 := h3373c.2.2.1
                                have p3373_3 := h3373c.2.2.2
                                linarith only [h3358, hlam, p3373_0]
                              · have p3373_0 := h3373c.1
                                have p3373_1 := h3373c.2.1
                                have p3373_2 := h3373c.2.2.1
                                have p3373_3 := h3373c.2.2.2
                                linarith only [h3214, h3360, h3363, h3365, h3371, hc01, hc12, hlam, hphi, p3373_1]
                              · have p3373_0 := h3373c.1
                                have p3373_1 := h3373c.2.1
                                have p3373_2 := h3373c.2.2.1
                                have p3373_3 := h3373c.2.2.2
                                linarith only [h3212, hlam, p3373_1]
                              · have p3373_0 := h3373c.1
                                have p3373_1 := h3373c.2.1
                                have p3373_2 := h3373c.2.2.1
                                have p3373_3 := h3373c.2.2.2
                                linarith only [h3210, h3214, h3360, h3363, h3365, h3366, h3371, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3373_1]
                              · have p3373_0 := h3373c.1
                                have p3373_1 := h3373c.2.1
                                have p3373_2 := h3373c.2.2.1
                                have p3373_3 := h3373c.2.2.2
                                linarith only [h2722, h3214, h3360, h3363, h3365, h3371, hc01, hc12, hlam, hphi, p3373_1]
                              · have p3373_0 := h3373c.1
                                have p3373_1 := h3373c.2.1
                                have p3373_2 := h3373c.2.2.1
                                have p3373_3 := h3373c.2.2.2
                                linarith only [hlam, p3373_0]
                      · linarith only [h3213, h3214, h3366, hc23, hc35, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3412 | h3412
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3413 | h3413
                        · linarith only [h3210, h3214, h3413, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3415 | h3415
                          · linarith only [h2722, h3211, h3365, h3415, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3417 | h3417
                            · linarith only [h3210, h3214, h3360, h3364, h3365, h3412, h3417, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases h0bigk with h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c
                              · have p3419_0 := h3419c.1
                                have p3419_1 := h3419c.2.1
                                have p3419_2 := h3419c.2.2.1
                                have p3419_3 := h3419c.2.2.2
                                linarith only [hlam, p3419_0]
                              · have p3419_0 := h3419c.1
                                have p3419_1 := h3419c.2.1
                                have p3419_2 := h3419c.2.2.1
                                have p3419_3 := h3419c.2.2.2
                                linarith only [h0, hlam, p3419_1]
                              · have p3419_0 := h3419c.1
                                have p3419_1 := h3419c.2.1
                                have p3419_2 := h3419c.2.2.1
                                have p3419_3 := h3419c.2.2.2
                                linarith only [h1833, hlam, p3419_0]
                              · have p3419_0 := h3419c.1
                                have p3419_1 := h3419c.2.1
                                have p3419_2 := h3419c.2.2.1
                                have p3419_3 := h3419c.2.2.2
                                linarith only [h2722, hlam, p3419_1]
                              · have p3419_0 := h3419c.1
                                have p3419_1 := h3419c.2.1
                                have p3419_2 := h3419c.2.2.1
                                have p3419_3 := h3419c.2.2.2
                                linarith only [h3122, hlam, p3419_1]
                              · have p3419_0 := h3419c.1
                                have p3419_1 := h3419c.2.1
                                have p3419_2 := h3419c.2.2.1
                                have p3419_3 := h3419c.2.2.2
                                rcases p3419_3 (m.d 0 1) (by simp) with h3425 | h3425
                                · linarith only [h0, h3425, hlam]
                                · rcases p3419_3 (m.d 0 2) (by simp) with h3427 | h3427
                                  · rcases p3419_3 (m.d 0 3) (by simp) with h3428 | h3428
                                    · linarith only [h3210, h3428, hlam]
                                    · linarith only [h1833, h3428, hlam]
                                  · linarith only [h0, h3427, hlam]
                              · have p3419_0 := h3419c.1
                                have p3419_1 := h3419c.2.1
                                have p3419_2 := h3419c.2.2.1
                                have p3419_3 := h3419c.2.2.2
                                linarith only [hlam, p3419_0]
                              · have p3419_0 := h3419c.1
                                have p3419_1 := h3419c.2.1
                                have p3419_2 := h3419c.2.2.1
                                have p3419_3 := h3419c.2.2.2
                                linarith only [h3210, h3412, hc34, hlam, hphi, ht0b, ht45, ht5b, p3419_1, u0elo1]
                              · have p3419_0 := h3419c.1
                                have p3419_1 := h3419c.2.1
                                have p3419_2 := h3419c.2.2.1
                                have p3419_3 := h3419c.2.2.2
                                rcases p3419_3 (m.d 0 1) (by simp) with h3434 | h3434
                                · linarith only [h0, h3434, hlam]
                                · rcases p3419_3 (m.d 0 2) (by simp) with h3436 | h3436
                                  · rcases p3419_3 (m.d 0 3) (by simp) with h3437 | h3437
                                    · linarith only [h3210, h3437, hlam]
                                    · linarith only [h3213, h3437, hlam]
                                  · linarith only [h3211, h3436, hlam]
                              · have p3419_0 := h3419c.1
                                have p3419_1 := h3419c.2.1
                                have p3419_2 := h3419c.2.2.1
                                have p3419_3 := h3419c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht5b, p3419_1, u0elo1, u5ehi0]
                              · have p3419_0 := h3419c.1
                                have p3419_1 := h3419c.2.1
                                have p3419_2 := h3419c.2.2.1
                                have p3419_3 := h3419c.2.2.2
                                linarith only [h3214, h3360, h3364, hc01, hc12, hlam, hphi, p3419_1]
                              · have p3419_0 := h3419c.1
                                have p3419_1 := h3419c.2.1
                                have p3419_2 := h3419c.2.2.1
                                have p3419_3 := h3419c.2.2.2
                                linarith only [h3210, hlam, p3419_1]
                              · have p3419_0 := h3419c.1
                                have p3419_1 := h3419c.2.1
                                have p3419_2 := h3419c.2.2.1
                                have p3419_3 := h3419c.2.2.2
                                linarith only [hlam, p3419_0]
                              · have p3419_0 := h3419c.1
                                have p3419_1 := h3419c.2.1
                                have p3419_2 := h3419c.2.2.1
                                have p3419_3 := h3419c.2.2.2
                                linarith only [h3214, h3360, h3364, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3419_1]
                              · have p3419_0 := h3419c.1
                                have p3419_1 := h3419c.2.1
                                have p3419_2 := h3419c.2.2.1
                                have p3419_3 := h3419c.2.2.2
                                linarith only [h3214, hlam, p3419_1]
                              · have p3419_0 := h3419c.1
                                have p3419_1 := h3419c.2.1
                                have p3419_2 := h3419c.2.2.1
                                have p3419_3 := h3419c.2.2.2
                                linarith only [h2722, h3365, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3419_1]
                              · have p3419_0 := h3419c.1
                                have p3419_1 := h3419c.2.1
                                have p3419_2 := h3419c.2.2.1
                                have p3419_3 := h3419c.2.2.2
                                linarith only [h3211, hlam, p3419_0]
                              · have p3419_0 := h3419c.1
                                have p3419_1 := h3419c.2.1
                                have p3419_2 := h3419c.2.2.1
                                have p3419_3 := h3419c.2.2.2
                                linarith only [h3213, hlam, p3419_0]
                              · have p3419_0 := h3419c.1
                                have p3419_1 := h3419c.2.1
                                have p3419_2 := h3419c.2.2.1
                                have p3419_3 := h3419c.2.2.2
                                linarith only [hlam, p3419_0]
                              · have p3419_0 := h3419c.1
                                have p3419_1 := h3419c.2.1
                                have p3419_2 := h3419c.2.2.1
                                have p3419_3 := h3419c.2.2.2
                                linarith only [h3358, hlam, p3419_0]
                              · have p3419_0 := h3419c.1
                                have p3419_1 := h3419c.2.1
                                have p3419_2 := h3419c.2.2.1
                                have p3419_3 := h3419c.2.2.2
                                linarith only [h3214, h3360, h3364, hc01, hc12, hlam, hphi, p3419_1]
                              · have p3419_0 := h3419c.1
                                have p3419_1 := h3419c.2.1
                                have p3419_2 := h3419c.2.2.1
                                have p3419_3 := h3419c.2.2.2
                                linarith only [h3212, hlam, p3419_1]
                              · have p3419_0 := h3419c.1
                                have p3419_1 := h3419c.2.1
                                have p3419_2 := h3419c.2.2.1
                                have p3419_3 := h3419c.2.2.2
                                linarith only [h1833, h3214, h3360, h3364, hc01, hc12, hlam, hphi, p3419_1]
                              · have p3419_0 := h3419c.1
                                have p3419_1 := h3419c.2.1
                                have p3419_2 := h3419c.2.2.1
                                have p3419_3 := h3419c.2.2.2
                                linarith only [h2722, h3214, h3360, h3364, hc01, hc12, hlam, hphi, p3419_1]
                              · have p3419_0 := h3419c.1
                                have p3419_1 := h3419c.2.1
                                have p3419_2 := h3419c.2.2.1
                                have p3419_3 := h3419c.2.2.2
                                linarith only [hlam, p3419_0]
                      · linarith only [h3213, h3214, h3360, h3364, h3412, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3458 | h3458
                    · linarith only [h2722, h3358, h3363, h3364, h3458, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3460 | h3460
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3461 | h3461
                        · linarith only [h1833, h3364, h3461, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3463 | h3463
                          · linarith only [h2722, h3458, h3463, hc01, hc24, hlam, hphi, ht12]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3465 | h3465
                            · linarith only [h2722, h3458, h3465, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases h0bigk with h3467c | h3467c | h3467c | h3467c | h3467c | h3467c | h3467c | h3467c | h3467c | h3467c | h3467c | h3467c | h3467c | h3467c | h3467c | h3467c | h3467c | h3467c | h3467c | h3467c | h3467c | h3467c | h3467c | h3467c | h3467c
                              · have p3467_0 := h3467c.1
                                have p3467_1 := h3467c.2.1
                                have p3467_2 := h3467c.2.2.1
                                have p3467_3 := h3467c.2.2.2
                                linarith only [hlam, p3467_0]
                              · have p3467_0 := h3467c.1
                                have p3467_1 := h3467c.2.1
                                have p3467_2 := h3467c.2.2.1
                                have p3467_3 := h3467c.2.2.2
                                linarith only [h0, hlam, p3467_1]
                              · have p3467_0 := h3467c.1
                                have p3467_1 := h3467c.2.1
                                have p3467_2 := h3467c.2.2.1
                                have p3467_3 := h3467c.2.2.2
                                linarith only [h1833, hlam, p3467_0]
                              · have p3467_0 := h3467c.1
                                have p3467_1 := h3467c.2.1
                                have p3467_2 := h3467c.2.2.1
                                have p3467_3 := h3467c.2.2.2
                                linarith only [h2722, hlam, p3467_1]
                              · have p3467_0 := h3467c.1
                                have p3467_1 := h3467c.2.1
                                have p3467_2 := h3467c.2.2.1
                                have p3467_3 := h3467c.2.2.2
                                linarith only [h3122, hlam, p3467_1]
                              · have p3467_0 := h3467c.1
                                have p3467_1 := h3467c.2.1
                                have p3467_2 := h3467c.2.2.1
                                have p3467_3 := h3467c.2.2.2
                                rcases p3467_3 (m.d 0 1) (by simp) with h3473 | h3473
                                · linarith only [h0, h3473, hlam]
                                · rcases p3467_3 (m.d 0 2) (by simp) with h3475 | h3475
                                  · rcases p3467_3 (m.d 0 3) (by simp) with h3476 | h3476
                                    · linarith only [h3210, h3476, hlam]
                                    · linarith only [h1833, h3476, hlam]
                                  · linarith only [h0, h3475, hlam]
                              · have p3467_0 := h3467c.1
                                have p3467_1 := h3467c.2.1
                                have p3467_2 := h3467c.2.2.1
                                have p3467_3 := h3467c.2.2.2
                                linarith only [hlam, p3467_0]
                              · have p3467_0 := h3467c.1
                                have p3467_1 := h3467c.2.1
                                have p3467_2 := h3467c.2.2.1
                                have p3467_3 := h3467c.2.2.2
                                linarith only [h3210, h3460, hc34, hlam, hphi, ht0b, ht45, ht5b, p3467_1, u0elo1]
                              · have p3467_0 := h3467c.1
                                have p3467_1 := h3467c.2.1
                                have p3467_2 := h3467c.2.2.1
                                have p3467_3 := h3467c.2.2.2
                                rcases p3467_3 (m.d 0 1) (by simp) with h3482 | h3482
                                · linarith only [h0, h3482, hlam]
                                · rcases p3467_3 (m.d 0 2) (by simp) with h3484 | h3484
                                  · rcases p3467_3 (m.d 0 3) (by simp) with h3485 | h3485
                                    · linarith only [h3210, h3485, hlam]
                                    · linarith only [h3213, h3485, hlam]
                                  · linarith only [h3211, h3484, hlam]
                              · have p3467_0 := h3467c.1
                                have p3467_1 := h3467c.2.1
                                have p3467_2 := h3467c.2.2.1
                                have p3467_3 := h3467c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht5b, p3467_1, u0elo1, u5ehi0]
                              · have p3467_0 := h3467c.1
                                have p3467_1 := h3467c.2.1
                                have p3467_2 := h3467c.2.2.1
                                have p3467_3 := h3467c.2.2.2
                                linarith only [h1833, h3364, hc01, hc35, hlam, hphi, ht12, ht23, p3467_1]
                              · have p3467_0 := h3467c.1
                                have p3467_1 := h3467c.2.1
                                have p3467_2 := h3467c.2.2.1
                                have p3467_3 := h3467c.2.2.2
                                linarith only [h3210, hlam, p3467_1]
                              · have p3467_0 := h3467c.1
                                have p3467_1 := h3467c.2.1
                                have p3467_2 := h3467c.2.2.1
                                have p3467_3 := h3467c.2.2.2
                                linarith only [hlam, p3467_0]
                              · have p3467_0 := h3467c.1
                                have p3467_1 := h3467c.2.1
                                have p3467_2 := h3467c.2.2.1
                                have p3467_3 := h3467c.2.2.2
                                linarith only [h1833, h2722, h3364, h3465, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3467_1]
                              · have p3467_0 := h3467c.1
                                have p3467_1 := h3467c.2.1
                                have p3467_2 := h3467c.2.2.1
                                have p3467_3 := h3467c.2.2.2
                                linarith only [h3214, hlam, p3467_1]
                              · have p3467_0 := h3467c.1
                                have p3467_1 := h3467c.2.1
                                have p3467_2 := h3467c.2.2.1
                                have p3467_3 := h3467c.2.2.2
                                linarith only [h1833, h3213, h3364, h3465, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3467_1]
                              · have p3467_0 := h3467c.1
                                have p3467_1 := h3467c.2.1
                                have p3467_2 := h3467c.2.2.1
                                have p3467_3 := h3467c.2.2.2
                                linarith only [h3211, hlam, p3467_0]
                              · have p3467_0 := h3467c.1
                                have p3467_1 := h3467c.2.1
                                have p3467_2 := h3467c.2.2.1
                                have p3467_3 := h3467c.2.2.2
                                linarith only [h3213, hlam, p3467_0]
                              · have p3467_0 := h3467c.1
                                have p3467_1 := h3467c.2.1
                                have p3467_2 := h3467c.2.2.1
                                have p3467_3 := h3467c.2.2.2
                                linarith only [hlam, p3467_0]
                              · have p3467_0 := h3467c.1
                                have p3467_1 := h3467c.2.1
                                have p3467_2 := h3467c.2.2.1
                                have p3467_3 := h3467c.2.2.2
                                linarith only [h3358, hlam, p3467_0]
                              · have p3467_0 := h3467c.1
                                have p3467_1 := h3467c.2.1
                                have p3467_2 := h3467c.2.2.1
                                have p3467_3 := h3467c.2.2.2
                                rcases p3467_3 (m.d 0 1) (by simp) with h3500 | h3500
                                · linarith only [h3122, h3500, hlam]
                                · rcases p3467_3 (m.d 0 2) (by simp) with h3502 | h3502
                                  · rcases p3467_3 (m.d 0 3) (by simp) with h3503 | h3503
                                    · linarith only [h3214, h3503, hlam]
                                    · linarith only [h1833, h3503, hlam]
                                  · linarith only [h0, h3502, hlam]
                              · have p3467_0 := h3467c.1
                                have p3467_1 := h3467c.2.1
                                have p3467_2 := h3467c.2.2.1
                                have p3467_3 := h3467c.2.2.2
                                linarith only [h3212, hlam, p3467_1]
                              · have p3467_0 := h3467c.1
                                have p3467_1 := h3467c.2.1
                                have p3467_2 := h3467c.2.2.1
                                have p3467_3 := h3467c.2.2.2
                                linarith only [h3122, h3210, h3364, h3460, h3465, hc34, hc45, hlam, hphi, p3467_1]
                              · have p3467_0 := h3467c.1
                                have p3467_1 := h3467c.2.1
                                have p3467_2 := h3467c.2.2.1
                                have p3467_3 := h3467c.2.2.2
                                rcases p3467_3 (m.d 0 1) (by simp) with h3509 | h3509
                                · linarith only [h3122, h3509, hlam]
                                · rcases p3467_3 (m.d 0 2) (by simp) with h3511 | h3511
                                  · rcases p3467_3 (m.d 0 3) (by simp) with h3512 | h3512
                                    · linarith only [h3214, h3512, hlam]
                                    · linarith only [h3213, h3512, hlam]
                                  · linarith only [h3211, h3511, hlam]
                              · have p3467_0 := h3467c.1
                                have p3467_1 := h3467c.2.1
                                have p3467_2 := h3467c.2.2.1
                                have p3467_3 := h3467c.2.2.2
                                linarith only [hlam, p3467_0]
                      · linarith only [h1833, h3213, h3364, h3460, hc23, hc35, hlam, hphi]
                · linarith only [h1833, h3213, h3363, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
              · linarith only [h0, h3212, h3362, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h3211, h3212, h3361, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi2]
          · linarith only [h0, h3210, h3360, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3522 | h3522
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3523 | h3523
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3524 | h3524
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3525 | h3525
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3526 | h3526
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3527 | h3527
                · linarith only [h3213, h3522, h3527, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3529 | h3529
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3530 | h3530
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3531 | h3531
                      · linarith only [h3210, h3527, h3531, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3533 | h3533
                        · linarith only [h3211, h3531, h3533, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                        · linarith only [h1833, h3522, h3527, h3533, hc23, hc34, hlam, hphi]
                    · linarith only [h1833, h3522, h3523, h3527, h3530, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi0]
                  · linarith only [h1833, h3522, h3529, hlam]
              · linarith only [h0, h3210, h3212, h3522, h3526, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
            · linarith only [h0, h3211, h3525, hlam]
          · linarith only [h0, h3210, h3524, hlam]
        · linarith only [h3213, h3522, h3523, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3542 | h3542
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3543 | h3543
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3544 | h3544
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3545 | h3545
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3546 | h3546
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3547 | h3547
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3548 | h3548
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3549 | h3549
                      · linarith only [h3210, h3213, h3549, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3551 | h3551
                        · linarith only [h3210, h3551, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3553 | h3553
                          · linarith only [h3211, h3553, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3555 | h3555
                            · rcases h0bigk with h3556c | h3556c | h3556c | h3556c | h3556c | h3556c | h3556c | h3556c | h3556c | h3556c | h3556c | h3556c | h3556c | h3556c | h3556c | h3556c | h3556c | h3556c | h3556c | h3556c | h3556c | h3556c | h3556c | h3556c | h3556c
                              · have p3556_0 := h3556c.1
                                have p3556_1 := h3556c.2.1
                                have p3556_2 := h3556c.2.2.1
                                have p3556_3 := h3556c.2.2.2
                                linarith only [hlam, p3556_0]
                              · have p3556_0 := h3556c.1
                                have p3556_1 := h3556c.2.1
                                have p3556_2 := h3556c.2.2.1
                                have p3556_3 := h3556c.2.2.2
                                linarith only [h0, hlam, p3556_1]
                              · have p3556_0 := h3556c.1
                                have p3556_1 := h3556c.2.1
                                have p3556_2 := h3556c.2.2.1
                                have p3556_3 := h3556c.2.2.2
                                linarith only [h1833, hlam, p3556_0]
                              · have p3556_0 := h3556c.1
                                have p3556_1 := h3556c.2.1
                                have p3556_2 := h3556c.2.2.1
                                have p3556_3 := h3556c.2.2.2
                                linarith only [h2722, hlam, p3556_1]
                              · have p3556_0 := h3556c.1
                                have p3556_1 := h3556c.2.1
                                have p3556_2 := h3556c.2.2.1
                                have p3556_3 := h3556c.2.2.2
                                linarith only [h3122, hlam, p3556_1]
                              · have p3556_0 := h3556c.1
                                have p3556_1 := h3556c.2.1
                                have p3556_2 := h3556c.2.2.1
                                have p3556_3 := h3556c.2.2.2
                                rcases p3556_3 (m.d 0 1) (by simp) with h3562 | h3562
                                · linarith only [h0, h3562, hlam]
                                · rcases p3556_3 (m.d 0 2) (by simp) with h3564 | h3564
                                  · rcases p3556_3 (m.d 0 3) (by simp) with h3565 | h3565
                                    · linarith only [h3210, h3565, hlam]
                                    · linarith only [h1833, h3565, hlam]
                                  · linarith only [h0, h3564, hlam]
                              · have p3556_0 := h3556c.1
                                have p3556_1 := h3556c.2.1
                                have p3556_2 := h3556c.2.2.1
                                have p3556_3 := h3556c.2.2.2
                                linarith only [hlam, p3556_0]
                              · have p3556_0 := h3556c.1
                                have p3556_1 := h3556c.2.1
                                have p3556_2 := h3556c.2.2.1
                                have p3556_3 := h3556c.2.2.2
                                rcases p3556_3 (m.d 0 1) (by simp) with h3570 | h3570
                                · linarith only [h0, h3570, hlam]
                                · rcases p3556_3 (m.d 0 2) (by simp) with h3572 | h3572
                                  · rcases p3556_3 (m.d 0 3) (by simp) with h3573 | h3573
                                    · linarith only [h3210, h3573, hlam]
                                    · rcases p3556_3 (m.d 0 4) (by simp) with h3575 | h3575
                                      · linarith only [h3211, h3575, hlam]
                                      · linarith only [h3213, h3575, hlam]
                                  · linarith only [h3210, h3572, hlam]
                              · have p3556_0 := h3556c.1
                                have p3556_1 := h3556c.2.1
                                have p3556_2 := h3556c.2.2.1
                                have p3556_3 := h3556c.2.2.2
                                linarith only [h3542, h3549, h3553, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3556_1, u0elo1]
                              · have p3556_0 := h3556c.1
                                have p3556_1 := h3556c.2.1
                                have p3556_2 := h3556c.2.2.1
                                have p3556_3 := h3556c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht5b, p3556_1, u0elo1, u5ehi0]
                              · have p3556_0 := h3556c.1
                                have p3556_1 := h3556c.2.1
                                have p3556_2 := h3556c.2.2.1
                                have p3556_3 := h3556c.2.2.2
                                linarith only [h3213, h3543, h3546, hc01, hc12, hlam, hphi, p3556_1]
                              · have p3556_0 := h3556c.1
                                have p3556_1 := h3556c.2.1
                                have p3556_2 := h3556c.2.2.1
                                have p3556_3 := h3556c.2.2.2
                                linarith only [h3210, hlam, p3556_1]
                              · have p3556_0 := h3556c.1
                                have p3556_1 := h3556c.2.1
                                have p3556_2 := h3556c.2.2.1
                                have p3556_3 := h3556c.2.2.2
                                linarith only [hlam, p3556_0]
                              · have p3556_0 := h3556c.1
                                have p3556_1 := h3556c.2.1
                                have p3556_2 := h3556c.2.2.1
                                have p3556_3 := h3556c.2.2.2
                                linarith only [h3213, hlam, p3556_1]
                              · have p3556_0 := h3556c.1
                                have p3556_1 := h3556c.2.1
                                have p3556_2 := h3556c.2.2.1
                                have p3556_3 := h3556c.2.2.2
                                linarith only [h3522, hlam, p3556_1]
                              · have p3556_0 := h3556c.1
                                have p3556_1 := h3556c.2.1
                                have p3556_2 := h3556c.2.2.1
                                have p3556_3 := h3556c.2.2.2
                                linarith only [h3213, h3543, h3546, hc01, hc12, hlam, hphi, p3556_1]
                              · have p3556_0 := h3556c.1
                                have p3556_1 := h3556c.2.1
                                have p3556_2 := h3556c.2.2.1
                                have p3556_3 := h3556c.2.2.2
                                linarith only [h3211, hlam, p3556_0]
                              · have p3556_0 := h3556c.1
                                have p3556_1 := h3556c.2.1
                                have p3556_2 := h3556c.2.2.1
                                have p3556_3 := h3556c.2.2.2
                                linarith only [h1833, h3213, h3543, h3546, hc01, hc12, hlam, hphi, p3556_1]
                              · have p3556_0 := h3556c.1
                                have p3556_1 := h3556c.2.1
                                have p3556_2 := h3556c.2.2.1
                                have p3556_3 := h3556c.2.2.2
                                linarith only [hlam, p3556_0]
                              · have p3556_0 := h3556c.1
                                have p3556_1 := h3556c.2.1
                                have p3556_2 := h3556c.2.2.1
                                have p3556_3 := h3556c.2.2.2
                                linarith only [h3213, h3543, h3546, hc12, hlam, hphi, ht01, ht0b, ht5b, p3556_1, u5ehi0]
                              · have p3556_0 := h3556c.1
                                have p3556_1 := h3556c.2.1
                                have p3556_2 := h3556c.2.2.1
                                have p3556_3 := h3556c.2.2.2
                                linarith only [h3522, h3543, h3546, h3555, hc01, hc12, hlam, hphi, p3556_1]
                              · have p3556_0 := h3556c.1
                                have p3556_1 := h3556c.2.1
                                have p3556_2 := h3556c.2.2.1
                                have p3556_3 := h3556c.2.2.2
                                linarith only [h3212, hlam, p3556_1]
                              · have p3556_0 := h3556c.1
                                have p3556_1 := h3556c.2.1
                                have p3556_2 := h3556c.2.2.1
                                have p3556_3 := h3556c.2.2.2
                                linarith only [h1833, h3522, h3543, h3546, h3555, hc01, hc12, hlam, hphi, p3556_1]
                              · have p3556_0 := h3556c.1
                                have p3556_1 := h3556c.2.1
                                have p3556_2 := h3556c.2.2.1
                                have p3556_3 := h3556c.2.2.2
                                linarith only [h3542, hlam, p3556_1]
                              · have p3556_0 := h3556c.1
                                have p3556_1 := h3556c.2.1
                                have p3556_2 := h3556c.2.2.1
                                have p3556_3 := h3556c.2.2.2
                                linarith only [hlam, p3556_0]
                            · linarith only [h3213, h3542, h3555, hlam]
                    · linarith only [h2722, h3213, h3542, h3543, h3546, h3548, hc01, hc12, hlam, hphi]
                  · linarith only [h3213, h3542, h3546, h3547, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3599 | h3599
                  · linarith only [h1833, h3522, h3546, h3599, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3601 | h3601
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3602 | h3602
                      · linarith only [h1833, h3546, h3602, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3604 | h3604
                        · linarith only [h1833, h3599, h3604, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3606 | h3606
                          · linarith only [h3211, h3606, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3608 | h3608
                            · rcases h0bigk with h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c | h3609c
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [hlam, p3609_0]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [h0, hlam, p3609_1]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [h1833, hlam, p3609_0]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [h2722, hlam, p3609_1]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [h3122, hlam, p3609_1]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                rcases p3609_3 (m.d 0 1) (by simp) with h3615 | h3615
                                · linarith only [h0, h3615, hlam]
                                · rcases p3609_3 (m.d 0 2) (by simp) with h3617 | h3617
                                  · rcases p3609_3 (m.d 0 3) (by simp) with h3618 | h3618
                                    · linarith only [h3210, h3618, hlam]
                                    · linarith only [h1833, h3618, hlam]
                                  · linarith only [h0, h3617, hlam]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [hlam, p3609_0]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                rcases p3609_3 (m.d 0 1) (by simp) with h3623 | h3623
                                · linarith only [h0, h3623, hlam]
                                · rcases p3609_3 (m.d 0 2) (by simp) with h3625 | h3625
                                  · rcases p3609_3 (m.d 0 3) (by simp) with h3626 | h3626
                                    · linarith only [h3210, h3626, hlam]
                                    · rcases p3609_3 (m.d 0 4) (by simp) with h3628 | h3628
                                      · linarith only [h3211, h3628, hlam]
                                      · linarith only [h3213, h3628, hlam]
                                  · linarith only [h3210, h3625, hlam]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [h3542, h3602, h3606, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3609_1, u0elo1]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht5b, p3609_1, u0elo1, u5ehi0]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [h1833, h3599, hc01, hc35, hlam, hphi, ht12, ht23, p3609_1]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [h3210, hlam, p3609_1]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [hlam, p3609_0]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [h3213, hlam, p3609_1]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [h3522, hlam, p3609_1]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                rcases p3609_3 (m.d 0 1) (by simp) with h3639 | h3639
                                · linarith only [h2722, h3639, hlam]
                                · rcases p3609_3 (m.d 0 2) (by simp) with h3641 | h3641
                                  · rcases p3609_3 (m.d 0 3) (by simp) with h3642 | h3642
                                    · linarith only [h3213, h3642, hlam]
                                    · linarith only [h1833, h3642, hlam]
                                  · linarith only [h0, h3641, hlam]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [h3211, hlam, p3609_0]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                rcases p3609_3 (m.d 0 1) (by simp) with h3647 | h3647
                                · linarith only [h2722, h3647, hlam]
                                · rcases p3609_3 (m.d 0 2) (by simp) with h3649 | h3649
                                  · rcases p3609_3 (m.d 0 3) (by simp) with h3650 | h3650
                                    · linarith only [h3213, h3650, hlam]
                                    · rcases p3609_3 (m.d 0 4) (by simp) with h3652 | h3652
                                      · rcases p3609_3 (m.d 0 5) (by simp) with h3653 | h3653
                                        · linarith only [h3542, h3653, hlam]
                                        · linarith only [h3522, h3653, hlam]
                                      · linarith only [h3213, h3652, hlam]
                                  · linarith only [h3210, h3649, hlam]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [hlam, p3609_0]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [h3542, h3602, h3606, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3609_1, u0elo3]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                rcases p3609_3 (m.d 0 1) (by simp) with h3660 | h3660
                                · linarith only [h3122, h3660, hlam]
                                · rcases p3609_3 (m.d 0 2) (by simp) with h3662 | h3662
                                  · rcases p3609_3 (m.d 0 3) (by simp) with h3663 | h3663
                                    · linarith only [h3522, h3663, hlam]
                                    · linarith only [h1833, h3663, hlam]
                                  · linarith only [h0, h3662, hlam]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [h3212, hlam, p3609_1]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                rcases p3609_3 (m.d 0 1) (by simp) with h3668 | h3668
                                · linarith only [h3122, h3668, hlam]
                                · rcases p3609_3 (m.d 0 2) (by simp) with h3670 | h3670
                                  · rcases p3609_3 (m.d 0 3) (by simp) with h3671 | h3671
                                    · linarith only [h3522, h3671, hlam]
                                    · rcases p3609_3 (m.d 0 4) (by simp) with h3673 | h3673
                                      · rcases p3609_3 (m.d 0 5) (by simp) with h3674 | h3674
                                        · rcases h2bigk with h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c | h3675c
                                          · have p3675_0 := h3675c.1
                                            have p3675_1 := h3675c.2.1
                                            have p3675_2 := h3675c.2.2.1
                                            have p3675_3 := h3675c.2.2.2
                                            linarith only [hlam, p3675_0]
                                          · have p3675_0 := h3675c.1
                                            have p3675_1 := h3675c.2.1
                                            have p3675_2 := h3675c.2.2.1
                                            have p3675_3 := h3675c.2.2.2
                                            linarith only [h0, hlam, p3675_1]
                                          · have p3675_0 := h3675c.1
                                            have p3675_1 := h3675c.2.1
                                            have p3675_2 := h3675c.2.2.1
                                            have p3675_3 := h3675c.2.2.2
                                            rcases p3675_3 (m.d 0 2) (by simp) with h3678 | h3678
                                            · rcases p3675_3 (m.d 1 2) (by simp) with h3679 | h3679
                                              · rcases p3675_3 (m.d 2 3) (by simp) with h3680 | h3680
                                                · linarith only [h3680, hlam, p3675_0]
                                                · rcases p3675_3 (m.d 2 4) (by simp) with h3682 | h3682
                                                  · linarith only [h3211, h3682, hlam]
                                                  · linarith only [h3602, h3682, hlam]
                                              · linarith only [h3543, h3679, hlam]
                                            · linarith only [h3678, hlam, p3675_0]
                                          · have p3675_0 := h3675c.1
                                            have p3675_1 := h3675c.2.1
                                            have p3675_2 := h3675c.2.2.1
                                            have p3675_3 := h3675c.2.2.2
                                            rcases p3675_3 (m.d 0 2) (by simp) with h3687 | h3687
                                            · rcases p3675_3 (m.d 1 2) (by simp) with h3688 | h3688
                                              · rcases p3675_3 (m.d 2 3) (by simp) with h3689 | h3689
                                                · linarith only [h3210, h3689, hlam]
                                                · rcases p3675_3 (m.d 2 4) (by simp) with h3691 | h3691
                                                  · linarith only [h3691, hlam, p3675_0]
                                                  · rcases p3675_3 (m.d 2 5) (by simp) with h3693 | h3693
                                                    · linarith only [h3212, h3693, hlam]
                                                    · linarith only [h3606, h3693, hlam]
                                              · linarith only [h3544, h3688, hlam]
                                            · linarith only [h3687, hlam, p3675_0]
                                          · have p3675_0 := h3675c.1
                                            have p3675_1 := h3675c.2.1
                                            have p3675_2 := h3675c.2.2.1
                                            have p3675_3 := h3675c.2.2.2
                                            linarith only [hlam, hphi, ht0b, ht5b, p3675_1, u0elo1, u5ehi2]
                                          · have p3675_0 := h3675c.1
                                            have p3675_1 := h3675c.2.1
                                            have p3675_2 := h3675c.2.2.1
                                            have p3675_3 := h3675c.2.2.2
                                            linarith only [h1833, h3212, hc01, hc12, hlam, hphi, ht0b, ht5b, p3609_1, p3675_1, u0elo4, u5ehi2]
                                          · have p3675_0 := h3675c.1
                                            have p3675_1 := h3675c.2.1
                                            have p3675_2 := h3675c.2.2.1
                                            have p3675_3 := h3675c.2.2.2
                                            linarith only [hlam, p3675_0]
                                          · have p3675_0 := h3675c.1
                                            have p3675_1 := h3675c.2.1
                                            have p3675_2 := h3675c.2.2.1
                                            have p3675_3 := h3675c.2.2.2
                                            rcases p3675_3 (m.d 0 2) (by simp) with h3701 | h3701
                                            · linarith only [h0, h3701, hlam]
                                            · linarith only [h3210, h3701, hlam]
                                          · have p3675_0 := h3675c.1
                                            have p3675_1 := h3675c.2.1
                                            have p3675_2 := h3675c.2.2.1
                                            have p3675_3 := h3675c.2.2.2
                                            rcases p3675_3 (m.d 0 2) (by simp) with h3704 | h3704
                                            · linarith only [h0, h3704, hlam]
                                            · linarith only [h3211, h3704, hlam]
                                          · have p3675_0 := h3675c.1
                                            have p3675_1 := h3675c.2.1
                                            have p3675_2 := h3675c.2.2.1
                                            have p3675_3 := h3675c.2.2.2
                                            rcases p3675_3 (m.d 0 2) (by simp) with h3707 | h3707
                                            · linarith only [h0, h3707, hlam]
                                            · linarith only [h3212, h3707, hlam]
                                          · have p3675_0 := h3675c.1
                                            have p3675_1 := h3675c.2.1
                                            have p3675_2 := h3675c.2.2.1
                                            have p3675_3 := h3675c.2.2.2
                                            linarith only [h3210, hlam, p3675_0]
                                          · have p3675_0 := h3675c.1
                                            have p3675_1 := h3675c.2.1
                                            have p3675_2 := h3675c.2.2.1
                                            have p3675_3 := h3675c.2.2.2
                                            linarith only [h3543, hlam, p3675_0]
                                          · have p3675_0 := h3675c.1
                                            have p3675_1 := h3675c.2.1
                                            have p3675_2 := h3675c.2.2.1
                                            have p3675_3 := h3675c.2.2.2
                                            linarith only [hlam, p3675_0]
                                          · have p3675_0 := h3675c.1
                                            have p3675_1 := h3675c.2.1
                                            have p3675_2 := h3675c.2.2.1
                                            have p3675_3 := h3675c.2.2.2
                                            linarith only [h3602, hlam, p3675_0]
                                          · have p3675_0 := h3675c.1
                                            have p3675_1 := h3675c.2.1
                                            have p3675_2 := h3675c.2.2.1
                                            have p3675_3 := h3675c.2.2.2
                                            linarith only [h3604, hlam, p3675_0]
                                          · have p3675_0 := h3675c.1
                                            have p3675_1 := h3675c.2.1
                                            have p3675_2 := h3675c.2.2.1
                                            have p3675_3 := h3675c.2.2.2
                                            linarith only [h3211, hlam, p3675_0]
                                          · have p3675_0 := h3675c.1
                                            have p3675_1 := h3675c.2.1
                                            have p3675_2 := h3675c.2.2.1
                                            have p3675_3 := h3675c.2.2.2
                                            linarith only [h3544, hlam, p3675_0]
                                          · have p3675_0 := h3675c.1
                                            have p3675_1 := h3675c.2.1
                                            have p3675_2 := h3675c.2.2.1
                                            have p3675_3 := h3675c.2.2.2
                                            linarith only [h3606, hc23, hc45, hlam, hphi, ht34, p3675_1]
                                          · have p3675_0 := h3675c.1
                                            have p3675_1 := h3675c.2.1
                                            have p3675_2 := h3675c.2.2.1
                                            have p3675_3 := h3675c.2.2.2
                                            linarith only [hlam, p3675_0]
                                          · have p3675_0 := h3675c.1
                                            have p3675_1 := h3675c.2.1
                                            have p3675_2 := h3675c.2.2.1
                                            have p3675_3 := h3675c.2.2.2
                                            linarith only [h3606, hlam, p3675_1]
                                          · have p3675_0 := h3675c.1
                                            have p3675_1 := h3675c.2.1
                                            have p3675_2 := h3675c.2.2.1
                                            have p3675_3 := h3675c.2.2.2
                                            linarith only [h3212, hlam, p3675_0]
                                          · have p3675_0 := h3675c.1
                                            have p3675_1 := h3675c.2.1
                                            have p3675_2 := h3675c.2.2.1
                                            have p3675_3 := h3675c.2.2.2
                                            linarith only [h3545, hlam, p3675_0]
                                          · have p3675_0 := h3675c.1
                                            have p3675_1 := h3675c.2.1
                                            have p3675_2 := h3675c.2.2.1
                                            have p3675_3 := h3675c.2.2.2
                                            linarith only [h3212, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3675_1, u0elo1]
                                          · have p3675_0 := h3675c.1
                                            have p3675_1 := h3675c.2.1
                                            have p3675_2 := h3675c.2.2.1
                                            have p3675_3 := h3675c.2.2.2
                                            linarith only [h3211, h3542, h3606, hc24, hlam, hphi, ht0b, ht45, ht5b, p3675_1, u0elo1]
                                          · have p3675_0 := h3675c.1
                                            have p3675_1 := h3675c.2.1
                                            have p3675_2 := h3675c.2.2.1
                                            have p3675_3 := h3675c.2.2.2
                                            linarith only [hlam, p3675_0]
                                        · linarith only [h3522, h3674, hlam]
                                      · linarith only [h3213, h3673, hlam]
                                  · linarith only [h3210, h3670, hlam]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [h3542, hlam, p3609_1]
                              · have p3609_0 := h3609c.1
                                have p3609_1 := h3609c.2.1
                                have p3609_2 := h3609c.2.2.1
                                have p3609_3 := h3609c.2.2.2
                                linarith only [hlam, p3609_0]
                            · linarith only [h3211, h3213, h3542, h3608, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h2722, h3211, h3542, h3601, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h3212, h3545, hlam]
            · linarith only [h0, h3211, h3544, hlam]
          · linarith only [h0, h3210, h3543, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3735 | h3735
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3736 | h3736
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3737 | h3737
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3738 | h3738
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3739 | h3739
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3740 | h3740
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3741 | h3741
                      · linarith only [h3210, h3213, h3741, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3743 | h3743
                        · linarith only [h3210, h3522, h3743, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3745 | h3745
                          · linarith only [h3211, h3542, h3745, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3747 | h3747
                            · linarith only [h1833, h3213, h3542, h3735, h3738, h3747, hc01, hc12, hlam, hphi]
                            · linarith only [h1833, h3213, h3740, h3747, hc01, hc14, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3750 | h3750
                      · linarith only [h3210, h3213, h3750, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3752 | h3752
                        · linarith only [h3210, h3522, h3752, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3754 | h3754
                          · linarith only [h2722, h3211, h3740, h3754, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3756 | h3756
                            · linarith only [h3738, h3740, h3756, hlam]
                            · rcases h0bigk with h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c | h3758c
                              · have p3758_0 := h3758c.1
                                have p3758_1 := h3758c.2.1
                                have p3758_2 := h3758c.2.2.1
                                have p3758_3 := h3758c.2.2.2
                                linarith only [hlam, p3758_0]
                              · have p3758_0 := h3758c.1
                                have p3758_1 := h3758c.2.1
                                have p3758_2 := h3758c.2.2.1
                                have p3758_3 := h3758c.2.2.2
                                linarith only [h0, hlam, p3758_1]
                              · have p3758_0 := h3758c.1
                                have p3758_1 := h3758c.2.1
                                have p3758_2 := h3758c.2.2.1
                                have p3758_3 := h3758c.2.2.2
                                linarith only [h1833, hlam, p3758_0]
                              · have p3758_0 := h3758c.1
                                have p3758_1 := h3758c.2.1
                                have p3758_2 := h3758c.2.2.1
                                have p3758_3 := h3758c.2.2.2
                                linarith only [h2722, hlam, p3758_1]
                              · have p3758_0 := h3758c.1
                                have p3758_1 := h3758c.2.1
                                have p3758_2 := h3758c.2.2.1
                                have p3758_3 := h3758c.2.2.2
                                linarith only [h3122, hlam, p3758_1]
                              · have p3758_0 := h3758c.1
                                have p3758_1 := h3758c.2.1
                                have p3758_2 := h3758c.2.2.1
                                have p3758_3 := h3758c.2.2.2
                                rcases p3758_3 (m.d 0 1) (by simp) with h3764 | h3764
                                · linarith only [h0, h3764, hlam]
                                · rcases p3758_3 (m.d 0 2) (by simp) with h3766 | h3766
                                  · rcases p3758_3 (m.d 0 3) (by simp) with h3767 | h3767
                                    · linarith only [h3210, h3767, hlam]
                                    · linarith only [h1833, h3767, hlam]
                                  · linarith only [h0, h3766, hlam]
                              · have p3758_0 := h3758c.1
                                have p3758_1 := h3758c.2.1
                                have p3758_2 := h3758c.2.2.1
                                have p3758_3 := h3758c.2.2.2
                                linarith only [hlam, p3758_0]
                              · have p3758_0 := h3758c.1
                                have p3758_1 := h3758c.2.1
                                have p3758_2 := h3758c.2.2.1
                                have p3758_3 := h3758c.2.2.2
                                rcases p3758_3 (m.d 0 1) (by simp) with h3772 | h3772
                                · linarith only [h0, h3772, hlam]
                                · rcases p3758_3 (m.d 0 2) (by simp) with h3774 | h3774
                                  · rcases p3758_3 (m.d 0 3) (by simp) with h3775 | h3775
                                    · linarith only [h3210, h3775, hlam]
                                    · rcases p3758_3 (m.d 0 4) (by simp) with h3777 | h3777
                                      · linarith only [h3211, h3777, hlam]
                                      · linarith only [h3213, h3777, hlam]
                                  · linarith only [h3210, h3774, hlam]
                              · have p3758_0 := h3758c.1
                                have p3758_1 := h3758c.2.1
                                have p3758_2 := h3758c.2.2.1
                                have p3758_3 := h3758c.2.2.2
                                rcases p3758_3 (m.d 0 1) (by simp) with h3781 | h3781
                                · linarith only [h0, h3781, hlam]
                                · rcases p3758_3 (m.d 0 2) (by simp) with h3783 | h3783
                                  · rcases p3758_3 (m.d 0 3) (by simp) with h3784 | h3784
                                    · linarith only [h3210, h3784, hlam]
                                    · rcases p3758_3 (m.d 0 4) (by simp) with h3786 | h3786
                                      · linarith only [h3211, h3786, hlam]
                                      · rcases p3758_3 (m.d 0 5) (by simp) with h3788 | h3788
                                        · linarith only [h3212, h3788, hlam]
                                        · linarith only [h3542, h3788, hlam]
                                  · linarith only [h3211, h3783, hlam]
                              · have p3758_0 := h3758c.1
                                have p3758_1 := h3758c.2.1
                                have p3758_2 := h3758c.2.2.1
                                have p3758_3 := h3758c.2.2.2
                                linarith only [h3212, hlam, hphi, ht0b, ht5b, p3758_1, u0elo1, u5ehi2]
                              · have p3758_0 := h3758c.1
                                have p3758_1 := h3758c.2.1
                                have p3758_2 := h3758c.2.2.1
                                have p3758_3 := h3758c.2.2.2
                                linarith only [h3213, h3738, h3740, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3758_1]
                              · have p3758_0 := h3758c.1
                                have p3758_1 := h3758c.2.1
                                have p3758_2 := h3758c.2.2.1
                                have p3758_3 := h3758c.2.2.2
                                linarith only [h3210, hlam, p3758_1]
                              · have p3758_0 := h3758c.1
                                have p3758_1 := h3758c.2.1
                                have p3758_2 := h3758c.2.2.1
                                have p3758_3 := h3758c.2.2.2
                                linarith only [hlam, p3758_0]
                              · have p3758_0 := h3758c.1
                                have p3758_1 := h3758c.2.1
                                have p3758_2 := h3758c.2.2.1
                                have p3758_3 := h3758c.2.2.2
                                linarith only [h3213, hlam, p3758_1]
                              · have p3758_0 := h3758c.1
                                have p3758_1 := h3758c.2.1
                                have p3758_2 := h3758c.2.2.1
                                have p3758_3 := h3758c.2.2.2
                                linarith only [h3522, hlam, p3758_1]
                              · have p3758_0 := h3758c.1
                                have p3758_1 := h3758c.2.1
                                have p3758_2 := h3758c.2.2.1
                                have p3758_3 := h3758c.2.2.2
                                linarith only [h2722, h3740, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3758_1]
                              · have p3758_0 := h3758c.1
                                have p3758_1 := h3758c.2.1
                                have p3758_2 := h3758c.2.2.1
                                have p3758_3 := h3758c.2.2.2
                                linarith only [h3211, hlam, p3758_0]
                              · have p3758_0 := h3758c.1
                                have p3758_1 := h3758c.2.1
                                have p3758_2 := h3758c.2.2.1
                                have p3758_3 := h3758c.2.2.2
                                linarith only [h3213, h3738, h3740, hc03, hc45, hlam, hphi, ht34, p3758_1]
                              · have p3758_0 := h3758c.1
                                have p3758_1 := h3758c.2.1
                                have p3758_2 := h3758c.2.2.1
                                have p3758_3 := h3758c.2.2.2
                                linarith only [hlam, p3758_0]
                              · have p3758_0 := h3758c.1
                                have p3758_1 := h3758c.2.1
                                have p3758_2 := h3758c.2.2.1
                                have p3758_3 := h3758c.2.2.2
                                linarith only [h3542, hlam, p3758_0]
                              · have p3758_0 := h3758c.1
                                have p3758_1 := h3758c.2.1
                                have p3758_2 := h3758c.2.2.1
                                have p3758_3 := h3758c.2.2.2
                                linarith only [h3522, h3735, h3739, hc01, hc12, hlam, hphi, p3758_1]
                              · have p3758_0 := h3758c.1
                                have p3758_1 := h3758c.2.1
                                have p3758_2 := h3758c.2.2.1
                                have p3758_3 := h3758c.2.2.2
                                linarith only [h3212, hlam, p3758_1]
                              · have p3758_0 := h3758c.1
                                have p3758_1 := h3758c.2.1
                                have p3758_2 := h3758c.2.2.1
                                have p3758_3 := h3758c.2.2.2
                                linarith only [h1833, h3522, h3735, h3739, hc01, hc12, hlam, hphi, p3758_1]
                              · have p3758_0 := h3758c.1
                                have p3758_1 := h3758c.2.1
                                have p3758_2 := h3758c.2.2.1
                                have p3758_3 := h3758c.2.2.2
                                linarith only [h2722, h3522, h3735, h3739, hc01, hc12, hlam, hphi, p3758_1]
                              · have p3758_0 := h3758c.1
                                have p3758_1 := h3758c.2.1
                                have p3758_2 := h3758c.2.2.1
                                have p3758_3 := h3758c.2.2.2
                                linarith only [hlam, p3758_0]
                  · linarith only [h1833, h3213, h3738, h3739, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3809 | h3809
                  · linarith only [h1833, h3522, h3738, h3809, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3811 | h3811
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3812 | h3812
                      · linarith only [h3210, h3213, h3812, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3814 | h3814
                        · linarith only [h1833, h3210, h3213, h3542, h3738, h3809, h3811, h3814, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3816 | h3816
                          · linarith only [h3211, h3542, h3816, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3818 | h3818
                            · rcases h0bigk with h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c | h3819c
                              · have p3819_0 := h3819c.1
                                have p3819_1 := h3819c.2.1
                                have p3819_2 := h3819c.2.2.1
                                have p3819_3 := h3819c.2.2.2
                                linarith only [hlam, p3819_0]
                              · have p3819_0 := h3819c.1
                                have p3819_1 := h3819c.2.1
                                have p3819_2 := h3819c.2.2.1
                                have p3819_3 := h3819c.2.2.2
                                linarith only [h0, hlam, p3819_1]
                              · have p3819_0 := h3819c.1
                                have p3819_1 := h3819c.2.1
                                have p3819_2 := h3819c.2.2.1
                                have p3819_3 := h3819c.2.2.2
                                linarith only [h1833, hlam, p3819_0]
                              · have p3819_0 := h3819c.1
                                have p3819_1 := h3819c.2.1
                                have p3819_2 := h3819c.2.2.1
                                have p3819_3 := h3819c.2.2.2
                                linarith only [h2722, hlam, p3819_1]
                              · have p3819_0 := h3819c.1
                                have p3819_1 := h3819c.2.1
                                have p3819_2 := h3819c.2.2.1
                                have p3819_3 := h3819c.2.2.2
                                linarith only [h3122, hlam, p3819_1]
                              · have p3819_0 := h3819c.1
                                have p3819_1 := h3819c.2.1
                                have p3819_2 := h3819c.2.2.1
                                have p3819_3 := h3819c.2.2.2
                                rcases p3819_3 (m.d 0 1) (by simp) with h3825 | h3825
                                · linarith only [h0, h3825, hlam]
                                · rcases p3819_3 (m.d 0 2) (by simp) with h3827 | h3827
                                  · rcases p3819_3 (m.d 0 3) (by simp) with h3828 | h3828
                                    · linarith only [h3210, h3828, hlam]
                                    · linarith only [h1833, h3828, hlam]
                                  · linarith only [h0, h3827, hlam]
                              · have p3819_0 := h3819c.1
                                have p3819_1 := h3819c.2.1
                                have p3819_2 := h3819c.2.2.1
                                have p3819_3 := h3819c.2.2.2
                                linarith only [hlam, p3819_0]
                              · have p3819_0 := h3819c.1
                                have p3819_1 := h3819c.2.1
                                have p3819_2 := h3819c.2.2.1
                                have p3819_3 := h3819c.2.2.2
                                rcases p3819_3 (m.d 0 1) (by simp) with h3833 | h3833
                                · linarith only [h0, h3833, hlam]
                                · rcases p3819_3 (m.d 0 2) (by simp) with h3835 | h3835
                                  · rcases p3819_3 (m.d 0 3) (by simp) with h3836 | h3836
                                    · linarith only [h3210, h3836, hlam]
                                    · rcases p3819_3 (m.d 0 4) (by simp) with h3838 | h3838
                                      · linarith only [h3211, h3838, hlam]
                                      · linarith only [h3213, h3838, hlam]
                                  · linarith only [h3210, h3835, hlam]
                              · have p3819_0 := h3819c.1
                                have p3819_1 := h3819c.2.1
                                have p3819_2 := h3819c.2.2.1
                                have p3819_3 := h3819c.2.2.2
                                rcases p3819_3 (m.d 0 1) (by simp) with h3842 | h3842
                                · linarith only [h0, h3842, hlam]
                                · rcases p3819_3 (m.d 0 2) (by simp) with h3844 | h3844
                                  · rcases p3819_3 (m.d 0 3) (by simp) with h3845 | h3845
                                    · linarith only [h3210, h3845, hlam]
                                    · rcases p3819_3 (m.d 0 4) (by simp) with h3847 | h3847
                                      · linarith only [h3211, h3847, hlam]
                                      · rcases p3819_3 (m.d 0 5) (by simp) with h3849 | h3849
                                        · linarith only [h3212, h3849, hlam]
                                        · linarith only [h3542, h3849, hlam]
                                  · linarith only [h3211, h3844, hlam]
                              · have p3819_0 := h3819c.1
                                have p3819_1 := h3819c.2.1
                                have p3819_2 := h3819c.2.2.1
                                have p3819_3 := h3819c.2.2.2
                                linarith only [h3212, hlam, hphi, ht0b, ht5b, p3819_1, u0elo1, u5ehi2]
                              · have p3819_0 := h3819c.1
                                have p3819_1 := h3819c.2.1
                                have p3819_2 := h3819c.2.2.1
                                have p3819_3 := h3819c.2.2.2
                                linarith only [h1833, h3809, hc01, hc35, hlam, hphi, ht12, ht23, p3819_1]
                              · have p3819_0 := h3819c.1
                                have p3819_1 := h3819c.2.1
                                have p3819_2 := h3819c.2.2.1
                                have p3819_3 := h3819c.2.2.2
                                linarith only [h3210, hlam, p3819_1]
                              · have p3819_0 := h3819c.1
                                have p3819_1 := h3819c.2.1
                                have p3819_2 := h3819c.2.2.1
                                have p3819_3 := h3819c.2.2.2
                                linarith only [hlam, p3819_0]
                              · have p3819_0 := h3819c.1
                                have p3819_1 := h3819c.2.1
                                have p3819_2 := h3819c.2.2.1
                                have p3819_3 := h3819c.2.2.2
                                linarith only [h3213, hlam, p3819_1]
                              · have p3819_0 := h3819c.1
                                have p3819_1 := h3819c.2.1
                                have p3819_2 := h3819c.2.2.1
                                have p3819_3 := h3819c.2.2.2
                                linarith only [h3522, hlam, p3819_1]
                              · have p3819_0 := h3819c.1
                                have p3819_1 := h3819c.2.1
                                have p3819_2 := h3819c.2.2.1
                                have p3819_3 := h3819c.2.2.2
                                linarith only [h3542, h3738, h3811, hc01, hc34, hlam, hphi, ht12, ht23, p3819_1]
                              · have p3819_0 := h3819c.1
                                have p3819_1 := h3819c.2.1
                                have p3819_2 := h3819c.2.2.1
                                have p3819_3 := h3819c.2.2.2
                                linarith only [h3211, hlam, p3819_0]
                              · have p3819_0 := h3819c.1
                                have p3819_1 := h3819c.2.1
                                have p3819_2 := h3819c.2.2.1
                                have p3819_3 := h3819c.2.2.2
                                linarith only [h3542, h3738, h3811, hc03, hc34, hlam, hphi, p3819_1]
                              · have p3819_0 := h3819c.1
                                have p3819_1 := h3819c.2.1
                                have p3819_2 := h3819c.2.2.1
                                have p3819_3 := h3819c.2.2.2
                                linarith only [hlam, p3819_0]
                              · have p3819_0 := h3819c.1
                                have p3819_1 := h3819c.2.1
                                have p3819_2 := h3819c.2.2.1
                                have p3819_3 := h3819c.2.2.2
                                linarith only [h3542, hlam, p3819_0]
                              · have p3819_0 := h3819c.1
                                have p3819_1 := h3819c.2.1
                                have p3819_2 := h3819c.2.2.1
                                have p3819_3 := h3819c.2.2.2
                                linarith only [h3542, h3738, h3811, hc01, hc34, hlam, hphi, ht12, ht23, p3819_1]
                              · have p3819_0 := h3819c.1
                                have p3819_1 := h3819c.2.1
                                have p3819_2 := h3819c.2.2.1
                                have p3819_3 := h3819c.2.2.2
                                linarith only [h3212, hlam, p3819_1]
                              · have p3819_0 := h3819c.1
                                have p3819_1 := h3819c.2.1
                                have p3819_2 := h3819c.2.2.1
                                have p3819_3 := h3819c.2.2.2
                                linarith only [h1833, h3542, h3738, h3811, hc01, hc34, hlam, hphi, ht12, ht23, p3819_1]
                              · have p3819_0 := h3819c.1
                                have p3819_1 := h3819c.2.1
                                have p3819_2 := h3819c.2.2.1
                                have p3819_3 := h3819c.2.2.2
                                linarith only [h2722, h3542, h3738, h3811, hc01, hc34, hlam, hphi, ht12, ht23, p3819_1]
                              · have p3819_0 := h3819c.1
                                have p3819_1 := h3819c.2.1
                                have p3819_2 := h3819c.2.2.1
                                have p3819_3 := h3819c.2.2.2
                                linarith only [hlam, p3819_0]
                            · linarith only [h3738, h3811, h3818, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3870 | h3870
                      · linarith only [h3210, h3213, h3870, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3872 | h3872
                        · linarith only [h3210, h3872, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3874 | h3874
                          · linarith only [h3211, h3738, h3811, h3874, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3876 | h3876
                            · linarith only [h1833, h3738, h3811, h3876, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h1833, h3738, h3876, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · linarith only [h0, h3212, h3737, hlam]
            · linarith only [h0, h3211, h3736, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · linarith only [h0, h3210, h3735, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3882 | h3882
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3883 | h3883
      · linarith only [h3210, h3212, h3883, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3885 | h3885
        · linarith only [h3211, h3212, h3885, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3887 | h3887
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3888 | h3888
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3889 | h3889
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3890 | h3890
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3891 | h3891
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3892 | h3892
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3893 | h3893
                      · linarith only [h3210, h3212, h3889, h3893, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h3210, h3212, h3882, h3889, h3893, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3896 | h3896
                      · linarith only [h3210, h3212, h3889, h3896, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h3210, h3212, h3882, h3889, h3896, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3899 | h3899
                    · linarith only [h2722, h3885, h3890, h3891, h3899, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3901 | h3901
                      · linarith only [h3210, h3212, h3889, h3901, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h3210, h3212, h3882, h3889, h3901, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h1833, h3210, h3212, h3882, h3889, h3890, hc01, hc12, hlam, hphi]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3905 | h3905
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3906 | h3906
                  · linarith only [h3882, h3883, h3887, h3889, h3906, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3908 | h3908
                    · linarith only [h2722, h3885, h3888, h3889, h3908, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3910 | h3910
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3911 | h3911
                        · linarith only [h3210, h3906, h3911, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3913 | h3913
                          · linarith only [h0, h3211, h3889, h3911, h3913, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                          · linarith only [h0, h3210, h3889, h3910, h3913, hc34, hc45, hlam, hphi]
                      · linarith only [h3882, h3883, h3910, hc23, hc35, hlam, hphi]
                · linarith only [h1833, h3882, h3905, hlam]
            · linarith only [h0, h3211, h3888, hlam]
          · linarith only [h0, h3210, h3887, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3920 | h3920
      · linarith only [h3211, h3212, h3882, h3920, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3922 | h3922
        · linarith only [h3211, h3212, h3922, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3924 | h3924
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3925 | h3925
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3926 | h3926
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3927 | h3927
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3928 | h3928
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3929 | h3929
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3930 | h3930
                      · linarith only [h1833, h3210, h3882, h3930, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3932 | h3932
                        · linarith only [h1833, h3211, h3920, h3930, h3932, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3934 | h3934
                          · linarith only [h3211, h3212, h3922, h3924, h3928, h3932, h3934, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3936 | h3936
                            · linarith only [h3211, h3212, h3930, h3934, h3936, hc23, hc34, hlam, hphi]
                            · linarith only [h1833, h3882, h3924, h3927, h3929, h3936, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3939 | h3939
                      · linarith only [h1833, h3210, h3882, h3939, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3941 | h3941
                        · linarith only [h3211, h3212, h3920, h3926, h3939, h3941, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3943 | h3943
                          · linarith only [h3211, h3212, h3924, h3928, h3929, h3941, h3943, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3945 | h3945
                            · linarith only [h3927, h3929, h3945, hlam]
                            · rcases h0bigk with h3947c | h3947c | h3947c | h3947c | h3947c | h3947c | h3947c | h3947c | h3947c | h3947c | h3947c | h3947c | h3947c | h3947c | h3947c | h3947c | h3947c | h3947c | h3947c | h3947c | h3947c | h3947c | h3947c | h3947c | h3947c
                              · have p3947_0 := h3947c.1
                                have p3947_1 := h3947c.2.1
                                have p3947_2 := h3947c.2.2.1
                                have p3947_3 := h3947c.2.2.2
                                linarith only [hlam, p3947_0]
                              · have p3947_0 := h3947c.1
                                have p3947_1 := h3947c.2.1
                                have p3947_2 := h3947c.2.2.1
                                have p3947_3 := h3947c.2.2.2
                                linarith only [h0, hlam, p3947_1]
                              · have p3947_0 := h3947c.1
                                have p3947_1 := h3947c.2.1
                                have p3947_2 := h3947c.2.2.1
                                have p3947_3 := h3947c.2.2.2
                                linarith only [h1833, hlam, p3947_0]
                              · have p3947_0 := h3947c.1
                                have p3947_1 := h3947c.2.1
                                have p3947_2 := h3947c.2.2.1
                                have p3947_3 := h3947c.2.2.2
                                linarith only [h2722, hlam, p3947_1]
                              · have p3947_0 := h3947c.1
                                have p3947_1 := h3947c.2.1
                                have p3947_2 := h3947c.2.2.1
                                have p3947_3 := h3947c.2.2.2
                                linarith only [h3122, hlam, p3947_1]
                              · have p3947_0 := h3947c.1
                                have p3947_1 := h3947c.2.1
                                have p3947_2 := h3947c.2.2.1
                                have p3947_3 := h3947c.2.2.2
                                linarith only [h3212, h3924, h3928, h3941, hc01, hc12, hlam, hphi, p3947_1]
                              · have p3947_0 := h3947c.1
                                have p3947_1 := h3947c.2.1
                                have p3947_2 := h3947c.2.2.1
                                have p3947_3 := h3947c.2.2.2
                                linarith only [hlam, p3947_0]
                              · have p3947_0 := h3947c.1
                                have p3947_1 := h3947c.2.1
                                have p3947_2 := h3947c.2.2.1
                                have p3947_3 := h3947c.2.2.2
                                linarith only [h1833, h3212, h3924, h3928, h3941, hc01, hc12, hlam, hphi, p3947_1]
                              · have p3947_0 := h3947c.1
                                have p3947_1 := h3947c.2.1
                                have p3947_2 := h3947c.2.2.1
                                have p3947_3 := h3947c.2.2.2
                                linarith only [h1833, h3212, h3882, h3924, h3928, h3941, hc01, hc12, hlam, hphi, p3947_1]
                              · have p3947_0 := h3947c.1
                                have p3947_1 := h3947c.2.1
                                have p3947_2 := h3947c.2.2.1
                                have p3947_3 := h3947c.2.2.2
                                linarith only [h3212, hlam, p3947_0]
                              · have p3947_0 := h3947c.1
                                have p3947_1 := h3947c.2.1
                                have p3947_2 := h3947c.2.2.1
                                have p3947_3 := h3947c.2.2.2
                                linarith only [h3882, h3927, hc01, hc14, hlam, hphi, p3947_1]
                              · have p3947_0 := h3947c.1
                                have p3947_1 := h3947c.2.1
                                have p3947_2 := h3947c.2.2.1
                                have p3947_3 := h3947c.2.2.2
                                linarith only [h3210, hlam, p3947_1]
                              · have p3947_0 := h3947c.1
                                have p3947_1 := h3947c.2.1
                                have p3947_2 := h3947c.2.2.1
                                have p3947_3 := h3947c.2.2.2
                                linarith only [hlam, p3947_0]
                              · have p3947_0 := h3947c.1
                                have p3947_1 := h3947c.2.1
                                have p3947_2 := h3947c.2.2.1
                                have p3947_3 := h3947c.2.2.2
                                linarith only [h3882, hlam, p3947_1]
                              · have p3947_0 := h3947c.1
                                have p3947_1 := h3947c.2.1
                                have p3947_2 := h3947c.2.2.1
                                have p3947_3 := h3947c.2.2.2
                                linarith only [h3920, hlam, p3947_1]
                              · have p3947_0 := h3947c.1
                                have p3947_1 := h3947c.2.1
                                have p3947_2 := h3947c.2.2.1
                                have p3947_3 := h3947c.2.2.2
                                linarith only [h2722, h3211, h3212, h3924, h3928, h3929, h3939, h3941, hc01, hc12, hc23, hc45, hlam, hphi, ht34, p3947_1]
                              · have p3947_0 := h3947c.1
                                have p3947_1 := h3947c.2.1
                                have p3947_2 := h3947c.2.2.1
                                have p3947_3 := h3947c.2.2.2
                                linarith only [h3211, hlam, p3947_0]
                              · have p3947_0 := h3947c.1
                                have p3947_1 := h3947c.2.1
                                have p3947_2 := h3947c.2.2.1
                                have p3947_3 := h3947c.2.2.2
                                linarith only [h2722, h3929, hc03, hc45, hlam, hphi, ht34, p3947_1]
                              · have p3947_0 := h3947c.1
                                have p3947_1 := h3947c.2.1
                                have p3947_2 := h3947c.2.2.1
                                have p3947_3 := h3947c.2.2.2
                                linarith only [hlam, p3947_0]
                              · have p3947_0 := h3947c.1
                                have p3947_1 := h3947c.2.1
                                have p3947_2 := h3947c.2.2.1
                                have p3947_3 := h3947c.2.2.2
                                linarith only [h3922, hlam, p3947_0]
                              · have p3947_0 := h3947c.1
                                have p3947_1 := h3947c.2.1
                                have p3947_2 := h3947c.2.2.1
                                have p3947_3 := h3947c.2.2.2
                                linarith only [h3212, h3924, h3928, h3941, hc01, hc12, hlam, hphi, p3947_1]
                              · have p3947_0 := h3947c.1
                                have p3947_1 := h3947c.2.1
                                have p3947_2 := h3947c.2.2.1
                                have p3947_3 := h3947c.2.2.2
                                linarith only [h3211, h3212, h3924, h3928, h3939, h3941, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3947_1]
                              · have p3947_0 := h3947c.1
                                have p3947_1 := h3947c.2.1
                                have p3947_2 := h3947c.2.2.1
                                have p3947_3 := h3947c.2.2.2
                                linarith only [h1833, h3212, h3924, h3928, h3941, hc01, hc12, hlam, hphi, p3947_1]
                              · have p3947_0 := h3947c.1
                                have p3947_1 := h3947c.2.1
                                have p3947_2 := h3947c.2.2.1
                                have p3947_3 := h3947c.2.2.2
                                linarith only [h2722, h3212, h3924, h3928, h3941, hc01, hc12, hlam, hphi, p3947_1]
                              · have p3947_0 := h3947c.1
                                have p3947_1 := h3947c.2.1
                                have p3947_2 := h3947c.2.2.1
                                have p3947_3 := h3947c.2.2.2
                                linarith only [hlam, p3947_0]
                  · linarith only [h1833, h3882, h3927, h3928, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3974 | h3974
                  · linarith only [h1833, h3920, h3927, h3974, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3976 | h3976
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3977 | h3977
                      · linarith only [h3210, h3927, h3977, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3979 | h3979
                        · linarith only [h3211, h3212, h3926, h3977, h3979, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3981 | h3981
                          · linarith only [h1833, h3211, h3212, h3882, h3922, h3926, h3981, hc01, hc12, hlam, hphi]
                          · linarith only [h3211, h3212, h3927, h3976, h3977, h3981, hc23, hc34, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3984 | h3984
                      · linarith only [h1833, h3927, h3984, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3986 | h3986
                        · linarith only [h3211, h3984, h3986, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3988 | h3988
                          · linarith only [h1833, h3211, h3212, h3926, h3927, h3976, h3988, hc01, hc12, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3990 | h3990
                            · linarith only [h1833, h3927, h3976, h3990, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h1833, h3927, h3990, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3993 | h3993
                · linarith only [h1833, h3882, h3924, h3926, h3993, hc01, hc25, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3995 | h3995
                  · linarith only [h1833, h3920, h3925, h3926, h3993, h3995, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3997 | h3997
                    · linarith only [h1833, h3882, h3922, h3925, h3926, h3997, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3999 | h3999
                      · linarith only [h1833, h3993, h3999, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4001 | h4001
                        · linarith only [h3211, h3999, h4001, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4003 | h4003
                          · linarith only [h2722, h3122, h3211, h3925, h3926, h3997, h4001, h4003, hc01, hc35, hlam, hphi, ht12, ht23]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4005 | h4005
                            · linarith only [h3211, h3212, h3999, h4003, h4005, hc23, hc34, hlam, hphi]
                            · linarith only [h1833, h3993, h4005, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · linarith only [h3211, h3212, h3925, hc12, hc25, hlam, hphi]
          · linarith only [h0, h3210, h3924, hlam]

end R2N4
