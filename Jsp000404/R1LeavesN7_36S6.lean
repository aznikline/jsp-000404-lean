import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_36S2
import Jsp000404.R1LeavesN7_36S3
import Jsp000404.R1LeavesN7_36S4
import Jsp000404.R1LeavesN7_36S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7634000 in
theorem r1l7_10_12_13_25_L_0_L_I_L_I_M_IR_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1494 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2055 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h2897 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  rcases m.htr 0 2 5 (by decide) (by decide) with h3206 | h3206
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3207 | h3207
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3208 | h3208
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3209 | h3209
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3210 | h3210
          · linarith only [h2055, h3206, h3210, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3212 | h3212
            · linarith only [h2897, h3206, h3212, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3214 | h3214
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3215 | h3215
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3216 | h3216
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3217 | h3217
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3218 | h3218
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3219 | h3219
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3220 | h3220
                          · linarith only [h3207, h3220, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                          · rcases h2bigk with h3222c | h3222c | h3222c | h3222c | h3222c | h3222c | h3222c | h3222c | h3222c | h3222c | h3222c | h3222c | h3222c | h3222c | h3222c | h3222c | h3222c | h3222c | h3222c | h3222c | h3222c | h3222c | h3222c | h3222c | h3222c
                            · have p3222_0 := h3222c.1
                              have p3222_1 := h3222c.2.1
                              have p3222_2 := h3222c.2.2.1
                              have p3222_3 := h3222c.2.2.2
                              linarith only [hlam, p3222_0]
                            · have p3222_0 := h3222c.1
                              have p3222_1 := h3222c.2.1
                              have p3222_2 := h3222c.2.2.1
                              have p3222_3 := h3222c.2.2.2
                              linarith only [h0, hlam, p3222_1]
                            · have p3222_0 := h3222c.1
                              have p3222_1 := h3222c.2.1
                              have p3222_2 := h3222c.2.2.1
                              have p3222_3 := h3222c.2.2.2
                              linarith only [h2055, hlam, p3222_0]
                            · have p3222_0 := h3222c.1
                              have p3222_1 := h3222c.2.1
                              have p3222_2 := h3222c.2.2.1
                              have p3222_3 := h3222c.2.2.2
                              linarith only [h2897, hlam, p3222_0]
                            · have p3222_0 := h3222c.1
                              have p3222_1 := h3222c.2.1
                              have p3222_2 := h3222c.2.2.1
                              have p3222_3 := h3222c.2.2.2
                              linarith only [h3219, h3220, hc34, hlam, hphi, ht0b, ht45, ht5b, p3222_1, u0elo1]
                            · have p3222_0 := h3222c.1
                              have p3222_1 := h3222c.2.1
                              have p3222_2 := h3222c.2.2.1
                              have p3222_3 := h3222c.2.2.2
                              linarith only [h3212, h3217, hc02, hc23, hlam, hphi, p3222_1]
                            · have p3222_0 := h3222c.1
                              have p3222_1 := h3222c.2.1
                              have p3222_2 := h3222c.2.2.1
                              have p3222_3 := h3222c.2.2.2
                              linarith only [hlam, p3222_0]
                            · have p3222_0 := h3222c.1
                              have p3222_1 := h3222c.2.1
                              have p3222_2 := h3222c.2.2.1
                              have p3222_3 := h3222c.2.2.2
                              linarith only [h3210, hlam, p3222_0]
                            · have p3222_0 := h3222c.1
                              have p3222_1 := h3222c.2.1
                              have p3222_2 := h3222c.2.2.1
                              have p3222_3 := h3222c.2.2.2
                              linarith only [h3212, hlam, p3222_0]
                            · have p3222_0 := h3222c.1
                              have p3222_1 := h3222c.2.1
                              have p3222_2 := h3222c.2.2.1
                              have p3222_3 := h3222c.2.2.2
                              linarith only [h3212, h3217, h3219, h3220, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3222_1]
                            · have p3222_0 := h3222c.1
                              have p3222_1 := h3222c.2.1
                              have p3222_2 := h3222c.2.2.1
                              have p3222_3 := h3222c.2.2.2
                              linarith only [h3206, h3219, h3220, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3222_1]
                            · have p3222_0 := h3222c.1
                              have p3222_1 := h3222c.2.1
                              have p3222_2 := h3222c.2.2.1
                              have p3222_3 := h3222c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p3222_1]
                            · have p3222_0 := h3222c.1
                              have p3222_1 := h3222c.2.1
                              have p3222_2 := h3222c.2.2.1
                              have p3222_3 := h3222c.2.2.2
                              linarith only [hlam, p3222_0]
                            · have p3222_0 := h3222c.1
                              have p3222_1 := h3222c.2.1
                              have p3222_2 := h3222c.2.2.1
                              have p3222_3 := h3222c.2.2.2
                              linarith only [h2897, h3206, h3219, h3220, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3222_1]
                            · have p3222_0 := h3222c.1
                              have p3222_1 := h3222c.2.1
                              have p3222_2 := h3222c.2.2.1
                              have p3222_3 := h3222c.2.2.2
                              rcases p3222_3 (m.d 0 2) (by simp) with h3237 | h3237
                              · linarith only [h2055, h3237, hlam]
                              · linarith only [h3206, h3237, hlam]
                            · have p3222_0 := h3222c.1
                              have p3222_1 := h3222c.2.1
                              have p3222_2 := h3222c.2.2.1
                              have p3222_3 := h3222c.2.2.2
                              linarith only [h3206, h3219, h3220, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3222_1]
                            · have p3222_0 := h3222c.1
                              have p3222_1 := h3222c.2.1
                              have p3222_2 := h3222c.2.2.1
                              have p3222_3 := h3222c.2.2.2
                              linarith only [h0, h3206, h3219, h3220, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3222_1]
                            · have p3222_0 := h3222c.1
                              have p3222_1 := h3222c.2.1
                              have p3222_2 := h3222c.2.2.1
                              have p3222_3 := h3222c.2.2.2
                              linarith only [h3217, hlam, p3222_1]
                            · have p3222_0 := h3222c.1
                              have p3222_1 := h3222c.2.1
                              have p3222_2 := h3222c.2.2.1
                              have p3222_3 := h3222c.2.2.2
                              linarith only [hlam, p3222_0]
                            · have p3222_0 := h3222c.1
                              have p3222_1 := h3222c.2.1
                              have p3222_2 := h3222c.2.2.1
                              have p3222_3 := h3222c.2.2.2
                              rcases p3222_3 (m.d 0 2) (by simp) with h3244 | h3244
                              · linarith only [h2897, h3244, hlam]
                              · linarith only [h3206, h3244, hlam]
                            · have p3222_0 := h3222c.1
                              have p3222_1 := h3222c.2.1
                              have p3222_2 := h3222c.2.2.1
                              have p3222_3 := h3222c.2.2.2
                              linarith only [h3206, hlam, p3222_0]
                            · have p3222_0 := h3222c.1
                              have p3222_1 := h3222c.2.1
                              have p3222_2 := h3222c.2.2.1
                              have p3222_3 := h3222c.2.2.2
                              linarith only [h3214, hlam, p3222_0]
                            · have p3222_0 := h3222c.1
                              have p3222_1 := h3222c.2.1
                              have p3222_2 := h3222c.2.2.1
                              have p3222_3 := h3222c.2.2.2
                              linarith only [h3218, hlam, p3222_1]
                            · have p3222_0 := h3222c.1
                              have p3222_1 := h3222c.2.1
                              have p3222_2 := h3222c.2.2.1
                              have p3222_3 := h3222c.2.2.2
                              linarith only [h3219, hlam, p3222_0]
                            · have p3222_0 := h3222c.1
                              have p3222_1 := h3222c.2.1
                              have p3222_2 := h3222c.2.2.1
                              have p3222_3 := h3222c.2.2.2
                              linarith only [hlam, p3222_0]
                        · linarith only [h2897, h3206, h3219, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                      · linarith only [h2055, h3206, h3218, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h0, h3206, h3210, h3217, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                  · linarith only [h1494, h2055, h3206, h3208, h3216, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi2]
                · linarith only [h1494, h3207, h3215, hlam]
              · linarith only [h0, h3206, h3214, hlam]
        · linarith only [h2897, h3206, h3209, hlam]
      · linarith only [h2055, h3206, h3208, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3260 | h3260
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3261 | h3261
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3262 | h3262
          · linarith only [h2055, h3206, h3262, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3264 | h3264
            · linarith only [h2897, h3206, h3262, h3264, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3266 | h3266
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3267 | h3267
                · linarith only [h2055, h3206, h3207, h3267, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3269 | h3269
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3270 | h3270
                    · linarith only [h0, h3262, h3267, h3270, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h2055, h3206, h3270, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                  · linarith only [h0, h3206, h3260, h3262, h3269, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi2]
              · linarith only [h0, h3206, h3266, hlam]
        · linarith only [h2055, h3206, h3207, h3261, hlam]
      · linarith only [h2055, h3206, h3260, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3277 | h3277
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3278 | h3278
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3279 | h3279
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3280 | h3280
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3281 | h3281
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3282 | h3282
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3283 | h3283
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3284 | h3284
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3285 | h3285
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3286 | h3286
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3287 | h3287
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3288 | h3288
                          · linarith only [h3277, h3288, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                          · rcases h2bigk with h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c | h3290c
                            · have p3290_0 := h3290c.1
                              have p3290_1 := h3290c.2.1
                              have p3290_2 := h3290c.2.2.1
                              have p3290_3 := h3290c.2.2.2
                              linarith only [hlam, p3290_0]
                            · have p3290_0 := h3290c.1
                              have p3290_1 := h3290c.2.1
                              have p3290_2 := h3290c.2.2.1
                              have p3290_3 := h3290c.2.2.2
                              linarith only [h0, hlam, p3290_1]
                            · have p3290_0 := h3290c.1
                              have p3290_1 := h3290c.2.1
                              have p3290_2 := h3290c.2.2.1
                              have p3290_3 := h3290c.2.2.2
                              linarith only [h2055, hlam, p3290_0]
                            · have p3290_0 := h3290c.1
                              have p3290_1 := h3290c.2.1
                              have p3290_2 := h3290c.2.2.1
                              have p3290_3 := h3290c.2.2.2
                              linarith only [h2897, hlam, p3290_0]
                            · have p3290_0 := h3290c.1
                              have p3290_1 := h3290c.2.1
                              have p3290_2 := h3290c.2.2.1
                              have p3290_3 := h3290c.2.2.2
                              linarith only [h3206, hlam, p3290_0]
                            · have p3290_0 := h3290c.1
                              have p3290_1 := h3290c.2.1
                              have p3290_2 := h3290c.2.2.1
                              have p3290_3 := h3290c.2.2.2
                              rcases p3290_3 (m.d 0 2) (by simp) with h3296 | h3296
                              · linarith only [h0, h3296, hlam]
                              · rcases p3290_3 (m.d 1 2) (by simp) with h3298 | h3298
                                · rcases p3290_3 (m.d 2 3) (by simp) with h3299 | h3299
                                  · linarith only [h3280, h3299, hlam]
                                  · linarith only [h2055, h3299, hlam]
                                · linarith only [h0, h3298, hlam]
                            · have p3290_0 := h3290c.1
                              have p3290_1 := h3290c.2.1
                              have p3290_2 := h3290c.2.2.1
                              have p3290_3 := h3290c.2.2.2
                              linarith only [hlam, p3290_0]
                            · have p3290_0 := h3290c.1
                              have p3290_1 := h3290c.2.1
                              have p3290_2 := h3290c.2.2.1
                              have p3290_3 := h3290c.2.2.2
                              linarith only [h0, h3206, h3285, h3287, hc01, hc12, hlam, hphi, p3290_1]
                            · have p3290_0 := h3290c.1
                              have p3290_1 := h3290c.2.1
                              have p3290_2 := h3290c.2.2.1
                              have p3290_3 := h3290c.2.2.2
                              linarith only [h2897, h3279, h3288, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3290_1]
                            · have p3290_0 := h3290c.1
                              have p3290_1 := h3290c.2.1
                              have p3290_2 := h3290c.2.2.1
                              have p3290_3 := h3290c.2.2.2
                              linarith only [h0, h3206, hc01, hc12, hlam, hphi, p3290_1]
                            · have p3290_0 := h3290c.1
                              have p3290_1 := h3290c.2.1
                              have p3290_2 := h3290c.2.2.1
                              have p3290_3 := h3290c.2.2.2
                              linarith only [h0, h3280, hc01, hc12, hlam, hphi, p3290_1]
                            · have p3290_0 := h3290c.1
                              have p3290_1 := h3290c.2.1
                              have p3290_2 := h3290c.2.2.1
                              have p3290_3 := h3290c.2.2.2
                              linarith only [h3280, hlam, p3290_0]
                            · have p3290_0 := h3290c.1
                              have p3290_1 := h3290c.2.1
                              have p3290_2 := h3290c.2.2.1
                              have p3290_3 := h3290c.2.2.2
                              linarith only [hlam, p3290_0]
                            · have p3290_0 := h3290c.1
                              have p3290_1 := h3290c.2.1
                              have p3290_2 := h3290c.2.2.1
                              have p3290_3 := h3290c.2.2.2
                              linarith only [h2897, h3279, h3280, h3288, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3290_1]
                            · have p3290_0 := h3290c.1
                              have p3290_1 := h3290c.2.1
                              have p3290_2 := h3290c.2.2.1
                              have p3290_3 := h3290c.2.2.2
                              linarith only [h0, h3206, h3280, hc01, hc12, hlam, hphi, p3290_1]
                            · have p3290_0 := h3290c.1
                              have p3290_1 := h3290c.2.1
                              have p3290_2 := h3290c.2.2.1
                              have p3290_3 := h3290c.2.2.2
                              linarith only [h0, h3281, hc01, hc12, hlam, hphi, p3290_1]
                            · have p3290_0 := h3290c.1
                              have p3290_1 := h3290c.2.1
                              have p3290_2 := h3290c.2.2.1
                              have p3290_3 := h3290c.2.2.2
                              linarith only [h3281, hlam, p3290_0]
                            · have p3290_0 := h3290c.1
                              have p3290_1 := h3290c.2.1
                              have p3290_2 := h3290c.2.2.1
                              have p3290_3 := h3290c.2.2.2
                              linarith only [h3285, hlam, p3290_1]
                            · have p3290_0 := h3290c.1
                              have p3290_1 := h3290c.2.1
                              have p3290_2 := h3290c.2.2.1
                              have p3290_3 := h3290c.2.2.2
                              linarith only [hlam, p3290_0]
                            · have p3290_0 := h3290c.1
                              have p3290_1 := h3290c.2.1
                              have p3290_2 := h3290c.2.2.1
                              have p3290_3 := h3290c.2.2.2
                              linarith only [h0, h3206, h3280, h3285, hc01, hc12, hlam, hphi, p3290_1]
                            · have p3290_0 := h3290c.1
                              have p3290_1 := h3290c.2.1
                              have p3290_2 := h3290c.2.2.1
                              have p3290_3 := h3290c.2.2.2
                              linarith only [h0, h3282, hc01, hc12, hlam, hphi, p3290_1]
                            · have p3290_0 := h3290c.1
                              have p3290_1 := h3290c.2.1
                              have p3290_2 := h3290c.2.2.1
                              have p3290_3 := h3290c.2.2.2
                              linarith only [h3282, hlam, p3290_0]
                            · have p3290_0 := h3290c.1
                              have p3290_1 := h3290c.2.1
                              have p3290_2 := h3290c.2.2.1
                              have p3290_3 := h3290c.2.2.2
                              linarith only [h3286, hlam, p3290_1]
                            · have p3290_0 := h3290c.1
                              have p3290_1 := h3290c.2.1
                              have p3290_2 := h3290c.2.2.1
                              have p3290_3 := h3290c.2.2.2
                              linarith only [h3287, hlam, p3290_0]
                            · have p3290_0 := h3290c.1
                              have p3290_1 := h3290c.2.1
                              have p3290_2 := h3290c.2.2.1
                              have p3290_3 := h3290c.2.2.2
                              linarith only [hlam, p3290_0]
                        · linarith only [h0, h2897, h3279, h3287, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h2055, h3278, h3286, hlam]
                    · linarith only [h2055, h3277, h3285, hlam]
                  · linarith only [h2055, h3277, h3278, h3279, h3280, h3284, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi4]
                · linarith only [h2055, h3277, h3280, h3283, hlam]
              · linarith only [h2055, h3277, h3279, h3280, h3282, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
            · linarith only [h2055, h3277, h3279, h3280, h3281, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3329 | h3329
            · linarith only [h0, h2897, h3280, h3329, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3331 | h3331
              · linarith only [h0, h3206, h3280, h3331, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3333 | h3333
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3334 | h3334
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3335 | h3335
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3336 | h3336
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3337 | h3337
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3338 | h3338
                          · linarith only [h3277, h3338, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                          · rcases h2bigk with h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c | h3340c
                            · have p3340_0 := h3340c.1
                              have p3340_1 := h3340c.2.1
                              have p3340_2 := h3340c.2.2.1
                              have p3340_3 := h3340c.2.2.2
                              linarith only [hlam, p3340_0]
                            · have p3340_0 := h3340c.1
                              have p3340_1 := h3340c.2.1
                              have p3340_2 := h3340c.2.2.1
                              have p3340_3 := h3340c.2.2.2
                              linarith only [h0, hlam, p3340_1]
                            · have p3340_0 := h3340c.1
                              have p3340_1 := h3340c.2.1
                              have p3340_2 := h3340c.2.2.1
                              have p3340_3 := h3340c.2.2.2
                              linarith only [h2055, hlam, p3340_0]
                            · have p3340_0 := h3340c.1
                              have p3340_1 := h3340c.2.1
                              have p3340_2 := h3340c.2.2.1
                              have p3340_3 := h3340c.2.2.2
                              linarith only [h2897, hlam, p3340_0]
                            · have p3340_0 := h3340c.1
                              have p3340_1 := h3340c.2.1
                              have p3340_2 := h3340c.2.2.1
                              have p3340_3 := h3340c.2.2.2
                              linarith only [h3206, hlam, p3340_0]
                            · have p3340_0 := h3340c.1
                              have p3340_1 := h3340c.2.1
                              have p3340_2 := h3340c.2.2.1
                              have p3340_3 := h3340c.2.2.2
                              linarith only [h0, h3331, h3335, h3337, hc01, hc23, hlam, hphi, ht12, p3340_1]
                            · have p3340_0 := h3340c.1
                              have p3340_1 := h3340c.2.1
                              have p3340_2 := h3340c.2.2.1
                              have p3340_3 := h3340c.2.2.2
                              linarith only [hlam, p3340_0]
                            · have p3340_0 := h3340c.1
                              have p3340_1 := h3340c.2.1
                              have p3340_2 := h3340c.2.2.1
                              have p3340_3 := h3340c.2.2.2
                              linarith only [h3280, hlam, p3340_0]
                            · have p3340_0 := h3340c.1
                              have p3340_1 := h3340c.2.1
                              have p3340_2 := h3340c.2.2.1
                              have p3340_3 := h3340c.2.2.2
                              linarith only [h3329, hlam, p3340_0]
                            · have p3340_0 := h3340c.1
                              have p3340_1 := h3340c.2.1
                              have p3340_2 := h3340c.2.2.1
                              have p3340_3 := h3340c.2.2.2
                              linarith only [h3331, hlam, p3340_0]
                            · have p3340_0 := h3340c.1
                              have p3340_1 := h3340c.2.1
                              have p3340_2 := h3340c.2.2.1
                              have p3340_3 := h3340c.2.2.2
                              rcases p3340_3 (m.d 0 2) (by simp) with h3351 | h3351
                              · linarith only [h3351, hlam, p3340_0]
                              · rcases p3340_3 (m.d 1 2) (by simp) with h3353 | h3353
                                · linarith only [h3280, h3353, hlam]
                                · linarith only [h0, h3353, hlam]
                            · have p3340_0 := h3340c.1
                              have p3340_1 := h3340c.2.1
                              have p3340_2 := h3340c.2.2.1
                              have p3340_3 := h3340c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p3340_1]
                            · have p3340_0 := h3340c.1
                              have p3340_1 := h3340c.2.1
                              have p3340_2 := h3340c.2.2.1
                              have p3340_3 := h3340c.2.2.2
                              linarith only [hlam, p3340_0]
                            · have p3340_0 := h3340c.1
                              have p3340_1 := h3340c.2.1
                              have p3340_2 := h3340c.2.2.1
                              have p3340_3 := h3340c.2.2.2
                              linarith only [h0, h2897, hc01, hc23, hlam, hphi, ht12, p3340_1]
                            · have p3340_0 := h3340c.1
                              have p3340_1 := h3340c.2.1
                              have p3340_2 := h3340c.2.2.1
                              have p3340_3 := h3340c.2.2.2
                              linarith only [h0, h3331, hc01, hc23, hlam, hphi, ht12, p3340_1]
                            · have p3340_0 := h3340c.1
                              have p3340_1 := h3340c.2.1
                              have p3340_2 := h3340c.2.2.1
                              have p3340_3 := h3340c.2.2.2
                              rcases p3340_3 (m.d 0 2) (by simp) with h3360 | h3360
                              · linarith only [h3360, hlam, p3340_0]
                              · rcases p3340_3 (m.d 1 2) (by simp) with h3362 | h3362
                                · linarith only [h3329, h3362, hlam]
                                · linarith only [h0, h3362, hlam]
                            · have p3340_0 := h3340c.1
                              have p3340_1 := h3340c.2.1
                              have p3340_2 := h3340c.2.2.1
                              have p3340_3 := h3340c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p3340_1]
                            · have p3340_0 := h3340c.1
                              have p3340_1 := h3340c.2.1
                              have p3340_2 := h3340c.2.2.1
                              have p3340_3 := h3340c.2.2.2
                              linarith only [h3335, hlam, p3340_1]
                            · have p3340_0 := h3340c.1
                              have p3340_1 := h3340c.2.1
                              have p3340_2 := h3340c.2.2.1
                              have p3340_3 := h3340c.2.2.2
                              linarith only [hlam, p3340_0]
                            · have p3340_0 := h3340c.1
                              have p3340_1 := h3340c.2.1
                              have p3340_2 := h3340c.2.2.1
                              have p3340_3 := h3340c.2.2.2
                              linarith only [h0, h3331, h3335, hc01, hc23, hlam, hphi, ht12, p3340_1]
                            · have p3340_0 := h3340c.1
                              have p3340_1 := h3340c.2.1
                              have p3340_2 := h3340c.2.2.1
                              have p3340_3 := h3340c.2.2.2
                              rcases p3340_3 (m.d 0 2) (by simp) with h3369 | h3369
                              · linarith only [h3369, hlam, p3340_0]
                              · rcases p3340_3 (m.d 1 2) (by simp) with h3371 | h3371
                                · linarith only [h3331, h3371, hlam]
                                · linarith only [h0, h3371, hlam]
                            · have p3340_0 := h3340c.1
                              have p3340_1 := h3340c.2.1
                              have p3340_2 := h3340c.2.2.1
                              have p3340_3 := h3340c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3340_1]
                            · have p3340_0 := h3340c.1
                              have p3340_1 := h3340c.2.1
                              have p3340_2 := h3340c.2.2.1
                              have p3340_3 := h3340c.2.2.2
                              linarith only [h3336, hlam, p3340_1]
                            · have p3340_0 := h3340c.1
                              have p3340_1 := h3340c.2.1
                              have p3340_2 := h3340c.2.2.1
                              have p3340_3 := h3340c.2.2.2
                              linarith only [h3337, hlam, p3340_0]
                            · have p3340_0 := h3340c.1
                              have p3340_1 := h3340c.2.1
                              have p3340_2 := h3340c.2.2.1
                              have p3340_3 := h3340c.2.2.2
                              linarith only [hlam, p3340_0]
                        · linarith only [h0, h2897, h3279, h3337, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h2055, h3278, h3336, hlam]
                    · linarith only [h1494, h3277, h3280, h3335, hlam]
                  · linarith only [h1494, h3278, h3334, hlam]
                · linarith only [h1494, h3277, h3333, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3383 | h3383
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3384 | h3384
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3385 | h3385
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3386 | h3386
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3387 | h3387
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3388 | h3388
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3389 | h3389
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3390 | h3390
                        · linarith only [h0, h2897, h3279, h3384, h3390, hc01, hc12, hlam, hphi]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3392 | h3392
                          · linarith only [h0, h2897, h3277, h3390, h3392, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                          · rcases h2bigk with h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c | h3394c
                            · have p3394_0 := h3394c.1
                              have p3394_1 := h3394c.2.1
                              have p3394_2 := h3394c.2.2.1
                              have p3394_3 := h3394c.2.2.2
                              linarith only [hlam, p3394_0]
                            · have p3394_0 := h3394c.1
                              have p3394_1 := h3394c.2.1
                              have p3394_2 := h3394c.2.2.1
                              have p3394_3 := h3394c.2.2.2
                              linarith only [h0, hlam, p3394_1]
                            · have p3394_0 := h3394c.1
                              have p3394_1 := h3394c.2.1
                              have p3394_2 := h3394c.2.2.1
                              have p3394_3 := h3394c.2.2.2
                              linarith only [h2055, hlam, p3394_0]
                            · have p3394_0 := h3394c.1
                              have p3394_1 := h3394c.2.1
                              have p3394_2 := h3394c.2.2.1
                              have p3394_3 := h3394c.2.2.2
                              linarith only [h2897, hlam, p3394_0]
                            · have p3394_0 := h3394c.1
                              have p3394_1 := h3394c.2.1
                              have p3394_2 := h3394c.2.2.1
                              have p3394_3 := h3394c.2.2.2
                              linarith only [h3206, hlam, p3394_0]
                            · have p3394_0 := h3394c.1
                              have p3394_1 := h3394c.2.1
                              have p3394_2 := h3394c.2.2.1
                              have p3394_3 := h3394c.2.2.2
                              rcases p3394_3 (m.d 0 2) (by simp) with h3400 | h3400
                              · linarith only [h0, h3400, hlam]
                              · rcases p3394_3 (m.d 1 2) (by simp) with h3402 | h3402
                                · rcases p3394_3 (m.d 2 3) (by simp) with h3403 | h3403
                                  · linarith only [h3383, h3403, hlam]
                                  · linarith only [h2055, h3403, hlam]
                                · linarith only [h0, h3402, hlam]
                            · have p3394_0 := h3394c.1
                              have p3394_1 := h3394c.2.1
                              have p3394_2 := h3394c.2.2.1
                              have p3394_3 := h3394c.2.2.2
                              linarith only [hlam, p3394_0]
                            · have p3394_0 := h3394c.1
                              have p3394_1 := h3394c.2.1
                              have p3394_2 := h3394c.2.2.1
                              have p3394_3 := h3394c.2.2.2
                              linarith only [h2055, h3278, hc12, hlam, hphi, ht01, ht0b, ht5b, p3394_1, u5ehi3]
                            · have p3394_0 := h3394c.1
                              have p3394_1 := h3394c.2.1
                              have p3394_2 := h3394c.2.2.1
                              have p3394_3 := h3394c.2.2.2
                              linarith only [h0, h2897, hc01, hc12, hlam, hphi, p3394_1]
                            · have p3394_0 := h3394c.1
                              have p3394_1 := h3394c.2.1
                              have p3394_2 := h3394c.2.2.1
                              have p3394_3 := h3394c.2.2.2
                              linarith only [h0, h3206, hc01, hc12, hlam, hphi, p3394_1]
                            · have p3394_0 := h3394c.1
                              have p3394_1 := h3394c.2.1
                              have p3394_2 := h3394c.2.2.1
                              have p3394_3 := h3394c.2.2.2
                              linarith only [h0, h3383, hc01, hc12, hlam, hphi, p3394_1]
                            · have p3394_0 := h3394c.1
                              have p3394_1 := h3394c.2.1
                              have p3394_2 := h3394c.2.2.1
                              have p3394_3 := h3394c.2.2.2
                              linarith only [h3383, hlam, p3394_0]
                            · have p3394_0 := h3394c.1
                              have p3394_1 := h3394c.2.1
                              have p3394_2 := h3394c.2.2.1
                              have p3394_3 := h3394c.2.2.2
                              linarith only [hlam, p3394_0]
                            · have p3394_0 := h3394c.1
                              have p3394_1 := h3394c.2.1
                              have p3394_2 := h3394c.2.2.1
                              have p3394_3 := h3394c.2.2.2
                              linarith only [h0, h2897, h3383, hc01, hc12, hlam, hphi, p3394_1]
                            · have p3394_0 := h3394c.1
                              have p3394_1 := h3394c.2.1
                              have p3394_2 := h3394c.2.2.1
                              have p3394_3 := h3394c.2.2.2
                              linarith only [h3206, h3383, hc12, hlam, hphi, ht01, ht0b, ht5b, p3394_1, u5ehi0]
                            · have p3394_0 := h3394c.1
                              have p3394_1 := h3394c.2.1
                              have p3394_2 := h3394c.2.2.1
                              have p3394_3 := h3394c.2.2.2
                              linarith only [h0, h3384, hc01, hc12, hlam, hphi, p3394_1]
                            · have p3394_0 := h3394c.1
                              have p3394_1 := h3394c.2.1
                              have p3394_2 := h3394c.2.2.1
                              have p3394_3 := h3394c.2.2.2
                              linarith only [h3384, hlam, p3394_0]
                            · have p3394_0 := h3394c.1
                              have p3394_1 := h3394c.2.1
                              have p3394_2 := h3394c.2.2.1
                              have p3394_3 := h3394c.2.2.2
                              linarith only [h3388, hlam, p3394_1]
                            · have p3394_0 := h3394c.1
                              have p3394_1 := h3394c.2.1
                              have p3394_2 := h3394c.2.2.1
                              have p3394_3 := h3394c.2.2.2
                              linarith only [hlam, p3394_0]
                            · have p3394_0 := h3394c.1
                              have p3394_1 := h3394c.2.1
                              have p3394_2 := h3394c.2.2.1
                              have p3394_3 := h3394c.2.2.2
                              linarith only [h3390, hlam, p3394_1]
                            · have p3394_0 := h3394c.1
                              have p3394_1 := h3394c.2.1
                              have p3394_2 := h3394c.2.2.1
                              have p3394_3 := h3394c.2.2.2
                              linarith only [h0, h3385, hc01, hc12, hlam, hphi, p3394_1]
                            · have p3394_0 := h3394c.1
                              have p3394_1 := h3394c.2.1
                              have p3394_2 := h3394c.2.2.1
                              have p3394_3 := h3394c.2.2.2
                              linarith only [h3385, hlam, p3394_0]
                            · have p3394_0 := h3394c.1
                              have p3394_1 := h3394c.2.1
                              have p3394_2 := h3394c.2.2.1
                              have p3394_3 := h3394c.2.2.2
                              linarith only [h3389, hlam, p3394_1]
                            · have p3394_0 := h3394c.1
                              have p3394_1 := h3394c.2.1
                              have p3394_2 := h3394c.2.2.1
                              have p3394_3 := h3394c.2.2.2
                              linarith only [h0, h2897, h3383, h3389, hc01, hc12, hlam, hphi, p3394_1]
                            · have p3394_0 := h3394c.1
                              have p3394_1 := h3394c.2.1
                              have p3394_2 := h3394c.2.2.1
                              have p3394_3 := h3394c.2.2.2
                              linarith only [hlam, p3394_0]
                      · linarith only [h0, h2055, h3278, h3389, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h2055, h3277, h3388, hlam]
                  · linarith only [h2055, h3278, h3383, h3387, hlam]
                · linarith only [h2055, h3277, h3383, h3386, hlam]
              · linarith only [h2055, h3278, h3383, h3385, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
            · linarith only [h2055, h3278, h3383, h3384, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3432 | h3432
            · linarith only [h0, h2897, h3383, h3432, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3434 | h3434
              · linarith only [h0, h3206, h3383, h3434, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3436 | h3436
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3437 | h3437
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3438 | h3438
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3439 | h3439
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3440 | h3440
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3441 | h3441
                          · linarith only [h3277, h3279, h3441, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                          · rcases h2bigk with h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c | h3443c
                            · have p3443_0 := h3443c.1
                              have p3443_1 := h3443c.2.1
                              have p3443_2 := h3443c.2.2.1
                              have p3443_3 := h3443c.2.2.2
                              linarith only [hlam, p3443_0]
                            · have p3443_0 := h3443c.1
                              have p3443_1 := h3443c.2.1
                              have p3443_2 := h3443c.2.2.1
                              have p3443_3 := h3443c.2.2.2
                              linarith only [h0, hlam, p3443_1]
                            · have p3443_0 := h3443c.1
                              have p3443_1 := h3443c.2.1
                              have p3443_2 := h3443c.2.2.1
                              have p3443_3 := h3443c.2.2.2
                              linarith only [h2055, hlam, p3443_0]
                            · have p3443_0 := h3443c.1
                              have p3443_1 := h3443c.2.1
                              have p3443_2 := h3443c.2.2.1
                              have p3443_3 := h3443c.2.2.2
                              linarith only [h2897, hlam, p3443_0]
                            · have p3443_0 := h3443c.1
                              have p3443_1 := h3443c.2.1
                              have p3443_2 := h3443c.2.2.1
                              have p3443_3 := h3443c.2.2.2
                              linarith only [h3206, hlam, p3443_0]
                            · have p3443_0 := h3443c.1
                              have p3443_1 := h3443c.2.1
                              have p3443_2 := h3443c.2.2.1
                              have p3443_3 := h3443c.2.2.2
                              linarith only [h0, h3434, h3438, h3440, hc01, hc23, hlam, hphi, ht12, p3443_1]
                            · have p3443_0 := h3443c.1
                              have p3443_1 := h3443c.2.1
                              have p3443_2 := h3443c.2.2.1
                              have p3443_3 := h3443c.2.2.2
                              linarith only [hlam, p3443_0]
                            · have p3443_0 := h3443c.1
                              have p3443_1 := h3443c.2.1
                              have p3443_2 := h3443c.2.2.1
                              have p3443_3 := h3443c.2.2.2
                              linarith only [h3383, hlam, p3443_0]
                            · have p3443_0 := h3443c.1
                              have p3443_1 := h3443c.2.1
                              have p3443_2 := h3443c.2.2.1
                              have p3443_3 := h3443c.2.2.2
                              linarith only [h3432, hlam, p3443_0]
                            · have p3443_0 := h3443c.1
                              have p3443_1 := h3443c.2.1
                              have p3443_2 := h3443c.2.2.1
                              have p3443_3 := h3443c.2.2.2
                              linarith only [h3434, hlam, p3443_0]
                            · have p3443_0 := h3443c.1
                              have p3443_1 := h3443c.2.1
                              have p3443_2 := h3443c.2.2.1
                              have p3443_3 := h3443c.2.2.2
                              rcases p3443_3 (m.d 0 2) (by simp) with h3454 | h3454
                              · linarith only [h3454, hlam, p3443_0]
                              · rcases p3443_3 (m.d 1 2) (by simp) with h3456 | h3456
                                · linarith only [h3383, h3456, hlam]
                                · linarith only [h0, h3456, hlam]
                            · have p3443_0 := h3443c.1
                              have p3443_1 := h3443c.2.1
                              have p3443_2 := h3443c.2.2.1
                              have p3443_3 := h3443c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p3443_1]
                            · have p3443_0 := h3443c.1
                              have p3443_1 := h3443c.2.1
                              have p3443_2 := h3443c.2.2.1
                              have p3443_3 := h3443c.2.2.2
                              linarith only [hlam, p3443_0]
                            · have p3443_0 := h3443c.1
                              have p3443_1 := h3443c.2.1
                              have p3443_2 := h3443c.2.2.1
                              have p3443_3 := h3443c.2.2.2
                              linarith only [h0, h2897, hc01, hc23, hlam, hphi, ht12, p3443_1]
                            · have p3443_0 := h3443c.1
                              have p3443_1 := h3443c.2.1
                              have p3443_2 := h3443c.2.2.1
                              have p3443_3 := h3443c.2.2.2
                              linarith only [h0, h3434, hc01, hc23, hlam, hphi, ht12, p3443_1]
                            · have p3443_0 := h3443c.1
                              have p3443_1 := h3443c.2.1
                              have p3443_2 := h3443c.2.2.1
                              have p3443_3 := h3443c.2.2.2
                              rcases p3443_3 (m.d 0 2) (by simp) with h3463 | h3463
                              · linarith only [h3463, hlam, p3443_0]
                              · rcases p3443_3 (m.d 1 2) (by simp) with h3465 | h3465
                                · linarith only [h3432, h3465, hlam]
                                · linarith only [h0, h3465, hlam]
                            · have p3443_0 := h3443c.1
                              have p3443_1 := h3443c.2.1
                              have p3443_2 := h3443c.2.2.1
                              have p3443_3 := h3443c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p3443_1]
                            · have p3443_0 := h3443c.1
                              have p3443_1 := h3443c.2.1
                              have p3443_2 := h3443c.2.2.1
                              have p3443_3 := h3443c.2.2.2
                              linarith only [h3438, hlam, p3443_1]
                            · have p3443_0 := h3443c.1
                              have p3443_1 := h3443c.2.1
                              have p3443_2 := h3443c.2.2.1
                              have p3443_3 := h3443c.2.2.2
                              linarith only [hlam, p3443_0]
                            · have p3443_0 := h3443c.1
                              have p3443_1 := h3443c.2.1
                              have p3443_2 := h3443c.2.2.1
                              have p3443_3 := h3443c.2.2.2
                              linarith only [h0, h3434, h3438, hc01, hc23, hlam, hphi, ht12, p3443_1]
                            · have p3443_0 := h3443c.1
                              have p3443_1 := h3443c.2.1
                              have p3443_2 := h3443c.2.2.1
                              have p3443_3 := h3443c.2.2.2
                              rcases p3443_3 (m.d 0 2) (by simp) with h3472 | h3472
                              · linarith only [h3472, hlam, p3443_0]
                              · rcases p3443_3 (m.d 1 2) (by simp) with h3474 | h3474
                                · linarith only [h3434, h3474, hlam]
                                · linarith only [h0, h3474, hlam]
                            · have p3443_0 := h3443c.1
                              have p3443_1 := h3443c.2.1
                              have p3443_2 := h3443c.2.2.1
                              have p3443_3 := h3443c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3443_1]
                            · have p3443_0 := h3443c.1
                              have p3443_1 := h3443c.2.1
                              have p3443_2 := h3443c.2.2.1
                              have p3443_3 := h3443c.2.2.2
                              linarith only [h3439, hlam, p3443_1]
                            · have p3443_0 := h3443c.1
                              have p3443_1 := h3443c.2.1
                              have p3443_2 := h3443c.2.2.1
                              have p3443_3 := h3443c.2.2.2
                              linarith only [h3440, hlam, p3443_0]
                            · have p3443_0 := h3443c.1
                              have p3443_1 := h3443c.2.1
                              have p3443_2 := h3443c.2.2.1
                              have p3443_3 := h3443c.2.2.2
                              linarith only [hlam, p3443_0]
                        · linarith only [h0, h3432, h3440, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h2055, h3278, h3439, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h1494, h3277, h3278, h3383, h3438, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi3]
                  · linarith only [h1494, h3278, h3437, hlam]
                · linarith only [h1494, h3277, h3436, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3486 | h3486
        · linarith only [h3277, h3278, h3486, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3488 | h3488
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3489 | h3489
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3490 | h3490
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3491 | h3491
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3492 | h3492
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3493 | h3493
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3494 | h3494
                      · linarith only [h3277, h3278, h3488, h3494, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h2055, h3488, h3492, h3494, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h2055, h3277, h3493, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3498 | h3498
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3499 | h3499
                      · linarith only [h3488, h3492, h3499, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3501 | h3501
                        · linarith only [h0, h2897, h3486, h3489, h3501, hc01, hc12, hlam, hphi]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3503 | h3503
                          · linarith only [h0, h2055, h2897, h3277, h3488, h3492, h3501, h3503, hc01, hc35, hlam, hphi, ht12, ht23]
                          · rcases h2bigk with h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [hlam, p3505_0]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h0, hlam, p3505_1]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h2055, hlam, p3505_0]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h2897, hlam, p3505_0]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h3206, hlam, p3505_0]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              rcases p3505_3 (m.d 0 2) (by simp) with h3511 | h3511
                              · linarith only [h0, h3511, hlam]
                              · rcases p3505_3 (m.d 1 2) (by simp) with h3513 | h3513
                                · rcases p3505_3 (m.d 2 3) (by simp) with h3514 | h3514
                                  · linarith only [h3488, h3514, hlam]
                                  · linarith only [h2055, h3514, hlam]
                                · linarith only [h0, h3513, hlam]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [hlam, p3505_0]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h0, h2055, hc01, hc12, hlam, hphi, p3505_1]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h0, h2897, hc01, hc12, hlam, hphi, p3505_1]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h0, h3206, hc01, hc12, hlam, hphi, p3505_1]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h0, h3488, hc01, hc12, hlam, hphi, p3505_1]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h3488, hlam, p3505_0]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [hlam, p3505_0]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h0, h2897, h3488, h3492, h3503, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3505_1]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h3499, hlam, p3505_0]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h0, h3489, hc01, hc12, hlam, hphi, p3505_1]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h3489, hlam, p3505_0]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h3498, hlam, p3505_1]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [hlam, p3505_0]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h3501, hlam, p3505_1]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h0, h3490, hc01, hc12, hlam, hphi, p3505_1]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h3490, hlam, p3505_0]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h2055, h3277, h3490, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3505_1]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h0, h2897, h3490, hc01, hc12, hlam, hphi, p3505_1]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [hlam, p3505_0]
                    · linarith only [h1494, h3277, h3492, h3498, hc23, hc35, hlam, hphi]
                · linarith only [h2055, h3277, h3488, h3491, hlam]
              · linarith only [h0, h2055, h3488, h3490, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h2055, h3488, h3489, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3541 | h3541
            · linarith only [h0, h2897, h3488, h3541, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3543 | h3543
              · linarith only [h0, h3206, h3488, h3543, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3545 | h3545
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3546 | h3546
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3547 | h3547
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3548 | h3548
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3549 | h3549
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3550 | h3550
                          · linarith only [h3277, h3278, h3488, h3546, h3550, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                          · rcases h2bigk with h3552c | h3552c | h3552c | h3552c | h3552c | h3552c | h3552c | h3552c | h3552c | h3552c | h3552c | h3552c | h3552c | h3552c | h3552c | h3552c | h3552c | h3552c | h3552c | h3552c | h3552c | h3552c | h3552c | h3552c | h3552c
                            · have p3552_0 := h3552c.1
                              have p3552_1 := h3552c.2.1
                              have p3552_2 := h3552c.2.2.1
                              have p3552_3 := h3552c.2.2.2
                              linarith only [hlam, p3552_0]
                            · have p3552_0 := h3552c.1
                              have p3552_1 := h3552c.2.1
                              have p3552_2 := h3552c.2.2.1
                              have p3552_3 := h3552c.2.2.2
                              linarith only [h0, hlam, p3552_1]
                            · have p3552_0 := h3552c.1
                              have p3552_1 := h3552c.2.1
                              have p3552_2 := h3552c.2.2.1
                              have p3552_3 := h3552c.2.2.2
                              linarith only [h2055, hlam, p3552_0]
                            · have p3552_0 := h3552c.1
                              have p3552_1 := h3552c.2.1
                              have p3552_2 := h3552c.2.2.1
                              have p3552_3 := h3552c.2.2.2
                              linarith only [h2897, hlam, p3552_0]
                            · have p3552_0 := h3552c.1
                              have p3552_1 := h3552c.2.1
                              have p3552_2 := h3552c.2.2.1
                              have p3552_3 := h3552c.2.2.2
                              linarith only [h3206, hlam, p3552_0]
                            · have p3552_0 := h3552c.1
                              have p3552_1 := h3552c.2.1
                              have p3552_2 := h3552c.2.2.1
                              have p3552_3 := h3552c.2.2.2
                              linarith only [h0, h3543, h3547, h3549, hc01, hc23, hlam, hphi, ht12, p3552_1]
                            · have p3552_0 := h3552c.1
                              have p3552_1 := h3552c.2.1
                              have p3552_2 := h3552c.2.2.1
                              have p3552_3 := h3552c.2.2.2
                              linarith only [hlam, p3552_0]
                            · have p3552_0 := h3552c.1
                              have p3552_1 := h3552c.2.1
                              have p3552_2 := h3552c.2.2.1
                              have p3552_3 := h3552c.2.2.2
                              linarith only [h3488, hlam, p3552_0]
                            · have p3552_0 := h3552c.1
                              have p3552_1 := h3552c.2.1
                              have p3552_2 := h3552c.2.2.1
                              have p3552_3 := h3552c.2.2.2
                              linarith only [h3541, hlam, p3552_0]
                            · have p3552_0 := h3552c.1
                              have p3552_1 := h3552c.2.1
                              have p3552_2 := h3552c.2.2.1
                              have p3552_3 := h3552c.2.2.2
                              linarith only [h3543, hlam, p3552_0]
                            · have p3552_0 := h3552c.1
                              have p3552_1 := h3552c.2.1
                              have p3552_2 := h3552c.2.2.1
                              have p3552_3 := h3552c.2.2.2
                              rcases p3552_3 (m.d 0 2) (by simp) with h3563 | h3563
                              · linarith only [h3563, hlam, p3552_0]
                              · rcases p3552_3 (m.d 1 2) (by simp) with h3565 | h3565
                                · linarith only [h3488, h3565, hlam]
                                · linarith only [h0, h3565, hlam]
                            · have p3552_0 := h3552c.1
                              have p3552_1 := h3552c.2.1
                              have p3552_2 := h3552c.2.2.1
                              have p3552_3 := h3552c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p3552_1]
                            · have p3552_0 := h3552c.1
                              have p3552_1 := h3552c.2.1
                              have p3552_2 := h3552c.2.2.1
                              have p3552_3 := h3552c.2.2.2
                              linarith only [hlam, p3552_0]
                            · have p3552_0 := h3552c.1
                              have p3552_1 := h3552c.2.1
                              have p3552_2 := h3552c.2.2.1
                              have p3552_3 := h3552c.2.2.2
                              linarith only [h3277, h3278, h3549, h3550, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3552_1]
                            · have p3552_0 := h3552c.1
                              have p3552_1 := h3552c.2.1
                              have p3552_2 := h3552c.2.2.1
                              have p3552_3 := h3552c.2.2.2
                              linarith only [h0, h3206, hc01, hc23, hlam, hphi, ht12, p3552_1]
                            · have p3552_0 := h3552c.1
                              have p3552_1 := h3552c.2.1
                              have p3552_2 := h3552c.2.2.1
                              have p3552_3 := h3552c.2.2.2
                              rcases p3552_3 (m.d 0 2) (by simp) with h3572 | h3572
                              · linarith only [h3572, hlam, p3552_0]
                              · rcases p3552_3 (m.d 1 2) (by simp) with h3574 | h3574
                                · linarith only [h3541, h3574, hlam]
                                · linarith only [h0, h3574, hlam]
                            · have p3552_0 := h3552c.1
                              have p3552_1 := h3552c.2.1
                              have p3552_2 := h3552c.2.2.1
                              have p3552_3 := h3552c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p3552_1]
                            · have p3552_0 := h3552c.1
                              have p3552_1 := h3552c.2.1
                              have p3552_2 := h3552c.2.2.1
                              have p3552_3 := h3552c.2.2.2
                              linarith only [h3547, hlam, p3552_1]
                            · have p3552_0 := h3552c.1
                              have p3552_1 := h3552c.2.1
                              have p3552_2 := h3552c.2.2.1
                              have p3552_3 := h3552c.2.2.2
                              linarith only [hlam, p3552_0]
                            · have p3552_0 := h3552c.1
                              have p3552_1 := h3552c.2.1
                              have p3552_2 := h3552c.2.2.1
                              have p3552_3 := h3552c.2.2.2
                              linarith only [h0, h3543, h3547, hc01, hc23, hlam, hphi, ht12, p3552_1]
                            · have p3552_0 := h3552c.1
                              have p3552_1 := h3552c.2.1
                              have p3552_2 := h3552c.2.2.1
                              have p3552_3 := h3552c.2.2.2
                              rcases p3552_3 (m.d 0 2) (by simp) with h3581 | h3581
                              · linarith only [h3581, hlam, p3552_0]
                              · rcases p3552_3 (m.d 1 2) (by simp) with h3583 | h3583
                                · linarith only [h3543, h3583, hlam]
                                · linarith only [h0, h3583, hlam]
                            · have p3552_0 := h3552c.1
                              have p3552_1 := h3552c.2.1
                              have p3552_2 := h3552c.2.2.1
                              have p3552_3 := h3552c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3552_1]
                            · have p3552_0 := h3552c.1
                              have p3552_1 := h3552c.2.1
                              have p3552_2 := h3552c.2.2.1
                              have p3552_3 := h3552c.2.2.2
                              linarith only [h3548, hlam, p3552_1]
                            · have p3552_0 := h3552c.1
                              have p3552_1 := h3552c.2.1
                              have p3552_2 := h3552c.2.2.1
                              have p3552_3 := h3552c.2.2.2
                              linarith only [h3549, hlam, p3552_0]
                            · have p3552_0 := h3552c.1
                              have p3552_1 := h3552c.2.1
                              have p3552_2 := h3552c.2.2.1
                              have p3552_3 := h3552c.2.2.2
                              linarith only [hlam, p3552_0]
                        · linarith only [h0, h3541, h3549, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h3488, h3548, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h3277, h3278, h3488, h3546, h3547, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3593 | h3593
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3594 | h3594
                      · linarith only [h1494, h3546, h3594, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h3488, h3594, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h3277, h3488, h3593, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h1494, h3277, h3545, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3599 | h3599
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3600 | h3600
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3601 | h3601
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3602 | h3602
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3603 | h3603
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3604 | h3604
                · linarith only [h3277, h3599, h3604, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3606 | h3606
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3607 | h3607
                    · linarith only [h3601, h3604, h3607, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3609 | h3609
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3610 | h3610
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3611 | h3611
                          · rcases h2bigk with h3612c | h3612c | h3612c | h3612c | h3612c | h3612c | h3612c | h3612c | h3612c | h3612c | h3612c | h3612c | h3612c | h3612c | h3612c | h3612c | h3612c | h3612c | h3612c | h3612c | h3612c | h3612c | h3612c | h3612c | h3612c
                            · have p3612_0 := h3612c.1
                              have p3612_1 := h3612c.2.1
                              have p3612_2 := h3612c.2.2.1
                              have p3612_3 := h3612c.2.2.2
                              linarith only [hlam, p3612_0]
                            · have p3612_0 := h3612c.1
                              have p3612_1 := h3612c.2.1
                              have p3612_2 := h3612c.2.2.1
                              have p3612_3 := h3612c.2.2.2
                              linarith only [h0, hlam, p3612_1]
                            · have p3612_0 := h3612c.1
                              have p3612_1 := h3612c.2.1
                              have p3612_2 := h3612c.2.2.1
                              have p3612_3 := h3612c.2.2.2
                              linarith only [h2055, hlam, p3612_0]
                            · have p3612_0 := h3612c.1
                              have p3612_1 := h3612c.2.1
                              have p3612_2 := h3612c.2.2.1
                              have p3612_3 := h3612c.2.2.2
                              linarith only [h2897, hlam, p3612_0]
                            · have p3612_0 := h3612c.1
                              have p3612_1 := h3612c.2.1
                              have p3612_2 := h3612c.2.2.1
                              have p3612_3 := h3612c.2.2.2
                              linarith only [h3206, hlam, p3612_0]
                            · have p3612_0 := h3612c.1
                              have p3612_1 := h3612c.2.1
                              have p3612_2 := h3612c.2.2.1
                              have p3612_3 := h3612c.2.2.2
                              rcases p3612_3 (m.d 0 2) (by simp) with h3618 | h3618
                              · linarith only [h0, h3618, hlam]
                              · rcases p3612_3 (m.d 1 2) (by simp) with h3620 | h3620
                                · rcases p3612_3 (m.d 2 3) (by simp) with h3621 | h3621
                                  · linarith only [h3601, h3621, hlam]
                                  · linarith only [h2055, h3621, hlam]
                                · linarith only [h0, h3620, hlam]
                            · have p3612_0 := h3612c.1
                              have p3612_1 := h3612c.2.1
                              have p3612_2 := h3612c.2.2.1
                              have p3612_3 := h3612c.2.2.2
                              linarith only [hlam, p3612_0]
                            · have p3612_0 := h3612c.1
                              have p3612_1 := h3612c.2.1
                              have p3612_2 := h3612c.2.2.1
                              have p3612_3 := h3612c.2.2.2
                              linarith only [h0, h2055, hc01, hc12, hlam, hphi, p3612_1]
                            · have p3612_0 := h3612c.1
                              have p3612_1 := h3612c.2.1
                              have p3612_2 := h3612c.2.2.1
                              have p3612_3 := h3612c.2.2.2
                              linarith only [h0, h2897, hc01, hc12, hlam, hphi, p3612_1]
                            · have p3612_0 := h3612c.1
                              have p3612_1 := h3612c.2.1
                              have p3612_2 := h3612c.2.2.1
                              have p3612_3 := h3612c.2.2.2
                              linarith only [h0, h3206, hc01, hc12, hlam, hphi, p3612_1]
                            · have p3612_0 := h3612c.1
                              have p3612_1 := h3612c.2.1
                              have p3612_2 := h3612c.2.2.1
                              have p3612_3 := h3612c.2.2.2
                              linarith only [h0, h3601, hc01, hc12, hlam, hphi, p3612_1]
                            · have p3612_0 := h3612c.1
                              have p3612_1 := h3612c.2.1
                              have p3612_2 := h3612c.2.2.1
                              have p3612_3 := h3612c.2.2.2
                              linarith only [h3601, hlam, p3612_0]
                            · have p3612_0 := h3612c.1
                              have p3612_1 := h3612c.2.1
                              have p3612_2 := h3612c.2.2.1
                              have p3612_3 := h3612c.2.2.2
                              linarith only [hlam, p3612_0]
                            · have p3612_0 := h3612c.1
                              have p3612_1 := h3612c.2.1
                              have p3612_2 := h3612c.2.2.1
                              have p3612_3 := h3612c.2.2.2
                              linarith only [h3607, hlam, p3612_0]
                            · have p3612_0 := h3612c.1
                              have p3612_1 := h3612c.2.1
                              have p3612_2 := h3612c.2.2.1
                              have p3612_3 := h3612c.2.2.2
                              linarith only [h0, h3206, h3601, h3604, hc01, hc34, hlam, hphi, ht12, ht23, p3612_1]
                            · have p3612_0 := h3612c.1
                              have p3612_1 := h3612c.2.1
                              have p3612_2 := h3612c.2.2.1
                              have p3612_3 := h3612c.2.2.2
                              linarith only [h0, h3602, hc01, hc12, hlam, hphi, p3612_1]
                            · have p3612_0 := h3612c.1
                              have p3612_1 := h3612c.2.1
                              have p3612_2 := h3612c.2.2.1
                              have p3612_3 := h3612c.2.2.2
                              linarith only [h3602, hlam, p3612_0]
                            · have p3612_0 := h3612c.1
                              have p3612_1 := h3612c.2.1
                              have p3612_2 := h3612c.2.2.1
                              have p3612_3 := h3612c.2.2.2
                              linarith only [h0, h2055, h3602, hc01, hc12, hlam, hphi, p3612_1]
                            · have p3612_0 := h3612c.1
                              have p3612_1 := h3612c.2.1
                              have p3612_2 := h3612c.2.2.1
                              have p3612_3 := h3612c.2.2.2
                              linarith only [hlam, p3612_0]
                            · have p3612_0 := h3612c.1
                              have p3612_1 := h3612c.2.1
                              have p3612_2 := h3612c.2.2.1
                              have p3612_3 := h3612c.2.2.2
                              linarith only [h0, h3206, h3602, hc01, hc12, hlam, hphi, p3612_1]
                            · have p3612_0 := h3612c.1
                              have p3612_1 := h3612c.2.1
                              have p3612_2 := h3612c.2.2.1
                              have p3612_3 := h3612c.2.2.2
                              linarith only [h0, h3603, hc01, hc12, hlam, hphi, p3612_1]
                            · have p3612_0 := h3612c.1
                              have p3612_1 := h3612c.2.1
                              have p3612_2 := h3612c.2.2.1
                              have p3612_3 := h3612c.2.2.2
                              linarith only [h3603, hlam, p3612_0]
                            · have p3612_0 := h3612c.1
                              have p3612_1 := h3612c.2.1
                              have p3612_2 := h3612c.2.2.1
                              have p3612_3 := h3612c.2.2.2
                              linarith only [h3609, hlam, p3612_1]
                            · have p3612_0 := h3612c.1
                              have p3612_1 := h3612c.2.1
                              have p3612_2 := h3612c.2.2.1
                              have p3612_3 := h3612c.2.2.2
                              linarith only [h3610, hlam, p3612_0]
                            · have p3612_0 := h3612c.1
                              have p3612_1 := h3612c.2.1
                              have p3612_2 := h3612c.2.2.1
                              have p3612_3 := h3612c.2.2.2
                              linarith only [hlam, p3612_0]
                          · linarith only [h1494, h3604, h3611, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h0, h2897, h3600, h3610, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h1494, h3599, h3604, h3609, hc23, hc34, hlam, hphi]
                  · linarith only [h2055, h3599, h3601, h3606, hlam]
              · linarith only [h2055, h3599, h3601, h3603, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
            · linarith only [h2055, h3599, h3601, h3602, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3650 | h3650
            · linarith only [h0, h2897, h3601, h3650, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3652 | h3652
              · linarith only [h0, h3206, h3601, h3652, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3654 | h3654
                · linarith only [h3277, h3599, h3654, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3656 | h3656
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3657 | h3657
                    · linarith only [h0, h3652, h3654, h3656, h3657, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h3601, h3657, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h1494, h3599, h3656, hlam]
        · linarith only [h3277, h3599, h3600, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3662 | h3662
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3663 | h3663
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3664 | h3664
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3665 | h3665
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3666 | h3666
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3667 | h3667
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3668 | h3668
                    · linarith only [h3277, h3662, h3663, h3668, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · linarith only [h0, h2055, h3666, h3668, hc01, hc13, hlam, hphi]
                  · linarith only [h0, h2055, h3277, h3666, h3667, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3672 | h3672
                  · linarith only [h0, h2055, h3599, h3666, h3672, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3674 | h3674
                    · linarith only [h1494, h3666, h3674, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3676 | h3676
                      · linarith only [h3663, h3672, h3676, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3678 | h3678
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3679 | h3679
                          · rcases h2bigk with h3680c | h3680c | h3680c | h3680c | h3680c | h3680c | h3680c | h3680c | h3680c | h3680c | h3680c | h3680c | h3680c | h3680c | h3680c | h3680c | h3680c | h3680c | h3680c | h3680c | h3680c | h3680c | h3680c | h3680c | h3680c
                            · have p3680_0 := h3680c.1
                              have p3680_1 := h3680c.2.1
                              have p3680_2 := h3680c.2.2.1
                              have p3680_3 := h3680c.2.2.2
                              linarith only [hlam, p3680_0]
                            · have p3680_0 := h3680c.1
                              have p3680_1 := h3680c.2.1
                              have p3680_2 := h3680c.2.2.1
                              have p3680_3 := h3680c.2.2.2
                              linarith only [h0, hlam, p3680_1]
                            · have p3680_0 := h3680c.1
                              have p3680_1 := h3680c.2.1
                              have p3680_2 := h3680c.2.2.1
                              have p3680_3 := h3680c.2.2.2
                              linarith only [h2055, hlam, p3680_0]
                            · have p3680_0 := h3680c.1
                              have p3680_1 := h3680c.2.1
                              have p3680_2 := h3680c.2.2.1
                              have p3680_3 := h3680c.2.2.2
                              linarith only [h2897, hlam, p3680_0]
                            · have p3680_0 := h3680c.1
                              have p3680_1 := h3680c.2.1
                              have p3680_2 := h3680c.2.2.1
                              have p3680_3 := h3680c.2.2.2
                              linarith only [h3206, hlam, p3680_0]
                            · have p3680_0 := h3680c.1
                              have p3680_1 := h3680c.2.1
                              have p3680_2 := h3680c.2.2.1
                              have p3680_3 := h3680c.2.2.2
                              rcases p3680_3 (m.d 0 2) (by simp) with h3686 | h3686
                              · linarith only [h0, h3686, hlam]
                              · rcases p3680_3 (m.d 1 2) (by simp) with h3688 | h3688
                                · rcases p3680_3 (m.d 2 3) (by simp) with h3689 | h3689
                                  · linarith only [h3663, h3689, hlam]
                                  · linarith only [h2055, h3689, hlam]
                                · linarith only [h0, h3688, hlam]
                            · have p3680_0 := h3680c.1
                              have p3680_1 := h3680c.2.1
                              have p3680_2 := h3680c.2.2.1
                              have p3680_3 := h3680c.2.2.2
                              linarith only [hlam, p3680_0]
                            · have p3680_0 := h3680c.1
                              have p3680_1 := h3680c.2.1
                              have p3680_2 := h3680c.2.2.1
                              have p3680_3 := h3680c.2.2.2
                              linarith only [h0, h2055, hc01, hc12, hlam, hphi, p3680_1]
                            · have p3680_0 := h3680c.1
                              have p3680_1 := h3680c.2.1
                              have p3680_2 := h3680c.2.2.1
                              have p3680_3 := h3680c.2.2.2
                              linarith only [h0, h2897, hc01, hc12, hlam, hphi, p3680_1]
                            · have p3680_0 := h3680c.1
                              have p3680_1 := h3680c.2.1
                              have p3680_2 := h3680c.2.2.1
                              have p3680_3 := h3680c.2.2.2
                              linarith only [h0, h3206, hc01, hc12, hlam, hphi, p3680_1]
                            · have p3680_0 := h3680c.1
                              have p3680_1 := h3680c.2.1
                              have p3680_2 := h3680c.2.2.1
                              have p3680_3 := h3680c.2.2.2
                              linarith only [h0, h3663, h3672, h3679, hc01, hc34, hlam, hphi, ht12, ht23, p3680_1]
                            · have p3680_0 := h3680c.1
                              have p3680_1 := h3680c.2.1
                              have p3680_2 := h3680c.2.2.1
                              have p3680_3 := h3680c.2.2.2
                              linarith only [h3663, hlam, p3680_0]
                            · have p3680_0 := h3680c.1
                              have p3680_1 := h3680c.2.1
                              have p3680_2 := h3680c.2.2.1
                              have p3680_3 := h3680c.2.2.2
                              linarith only [hlam, p3680_0]
                            · have p3680_0 := h3680c.1
                              have p3680_1 := h3680c.2.1
                              have p3680_2 := h3680c.2.2.1
                              have p3680_3 := h3680c.2.2.2
                              linarith only [h3674, hlam, p3680_0]
                            · have p3680_0 := h3680c.1
                              have p3680_1 := h3680c.2.1
                              have p3680_2 := h3680c.2.2.1
                              have p3680_3 := h3680c.2.2.2
                              linarith only [h3676, hlam, p3680_0]
                            · have p3680_0 := h3680c.1
                              have p3680_1 := h3680c.2.1
                              have p3680_2 := h3680c.2.2.1
                              have p3680_3 := h3680c.2.2.2
                              linarith only [h0, h3664, hc01, hc12, hlam, hphi, p3680_1]
                            · have p3680_0 := h3680c.1
                              have p3680_1 := h3680c.2.1
                              have p3680_2 := h3680c.2.2.1
                              have p3680_3 := h3680c.2.2.2
                              linarith only [h3664, hlam, p3680_0]
                            · have p3680_0 := h3680c.1
                              have p3680_1 := h3680c.2.1
                              have p3680_2 := h3680c.2.2.1
                              have p3680_3 := h3680c.2.2.2
                              linarith only [h0, h2055, h3664, hc01, hc12, hlam, hphi, p3680_1]
                            · have p3680_0 := h3680c.1
                              have p3680_1 := h3680c.2.1
                              have p3680_2 := h3680c.2.2.1
                              have p3680_3 := h3680c.2.2.2
                              linarith only [hlam, p3680_0]
                            · have p3680_0 := h3680c.1
                              have p3680_1 := h3680c.2.1
                              have p3680_2 := h3680c.2.2.1
                              have p3680_3 := h3680c.2.2.2
                              linarith only [h0, h2055, h3664, h3676, hc01, hc12, hlam, hphi, p3680_1]
                            · have p3680_0 := h3680c.1
                              have p3680_1 := h3680c.2.1
                              have p3680_2 := h3680c.2.2.1
                              have p3680_3 := h3680c.2.2.2
                              linarith only [h0, h3665, hc01, hc12, hlam, hphi, p3680_1]
                            · have p3680_0 := h3680c.1
                              have p3680_1 := h3680c.2.1
                              have p3680_2 := h3680c.2.2.1
                              have p3680_3 := h3680c.2.2.2
                              linarith only [h3665, hlam, p3680_0]
                            · have p3680_0 := h3680c.1
                              have p3680_1 := h3680c.2.1
                              have p3680_2 := h3680c.2.2.1
                              have p3680_3 := h3680c.2.2.2
                              linarith only [h0, h2055, h3665, hc01, hc12, hlam, hphi, p3680_1]
                            · have p3680_0 := h3680c.1
                              have p3680_1 := h3680c.2.1
                              have p3680_2 := h3680c.2.2.1
                              have p3680_3 := h3680c.2.2.2
                              linarith only [h3678, hlam, p3680_0]
                            · have p3680_0 := h3680c.1
                              have p3680_1 := h3680c.2.1
                              have p3680_2 := h3680c.2.2.1
                              have p3680_3 := h3680c.2.2.2
                              linarith only [hlam, p3680_0]
                          · linarith only [h0, h2055, h2897, h3277, h3662, h3664, h3679, hc01, hc12, hlam, hphi]
                        · linarith only [h2897, h3662, h3678, hlam]
              · linarith only [h0, h2055, h3663, h3665, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h2055, h3663, h3664, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3716 | h3716
            · linarith only [h2897, h3662, h3663, h3716, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3718 | h3718
              · linarith only [h0, h3206, h3663, h3718, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3720 | h3720
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3721 | h3721
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3722 | h3722
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3723 | h3723
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3724 | h3724
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3725 | h3725
                          · rcases h2bigk with h3726c | h3726c | h3726c | h3726c | h3726c | h3726c | h3726c | h3726c | h3726c | h3726c | h3726c | h3726c | h3726c | h3726c | h3726c | h3726c | h3726c | h3726c | h3726c | h3726c | h3726c | h3726c | h3726c | h3726c | h3726c
                            · have p3726_0 := h3726c.1
                              have p3726_1 := h3726c.2.1
                              have p3726_2 := h3726c.2.2.1
                              have p3726_3 := h3726c.2.2.2
                              linarith only [hlam, p3726_0]
                            · have p3726_0 := h3726c.1
                              have p3726_1 := h3726c.2.1
                              have p3726_2 := h3726c.2.2.1
                              have p3726_3 := h3726c.2.2.2
                              linarith only [h0, hlam, p3726_1]
                            · have p3726_0 := h3726c.1
                              have p3726_1 := h3726c.2.1
                              have p3726_2 := h3726c.2.2.1
                              have p3726_3 := h3726c.2.2.2
                              linarith only [h2055, hlam, p3726_0]
                            · have p3726_0 := h3726c.1
                              have p3726_1 := h3726c.2.1
                              have p3726_2 := h3726c.2.2.1
                              have p3726_3 := h3726c.2.2.2
                              linarith only [h2897, hlam, p3726_0]
                            · have p3726_0 := h3726c.1
                              have p3726_1 := h3726c.2.1
                              have p3726_2 := h3726c.2.2.1
                              have p3726_3 := h3726c.2.2.2
                              linarith only [h3206, hlam, p3726_0]
                            · have p3726_0 := h3726c.1
                              have p3726_1 := h3726c.2.1
                              have p3726_2 := h3726c.2.2.1
                              have p3726_3 := h3726c.2.2.2
                              linarith only [h0, h3718, h3722, h3724, hc01, hc23, hlam, hphi, ht12, p3726_1]
                            · have p3726_0 := h3726c.1
                              have p3726_1 := h3726c.2.1
                              have p3726_2 := h3726c.2.2.1
                              have p3726_3 := h3726c.2.2.2
                              linarith only [hlam, p3726_0]
                            · have p3726_0 := h3726c.1
                              have p3726_1 := h3726c.2.1
                              have p3726_2 := h3726c.2.2.1
                              have p3726_3 := h3726c.2.2.2
                              linarith only [h3663, hlam, p3726_0]
                            · have p3726_0 := h3726c.1
                              have p3726_1 := h3726c.2.1
                              have p3726_2 := h3726c.2.2.1
                              have p3726_3 := h3726c.2.2.2
                              linarith only [h3716, hlam, p3726_0]
                            · have p3726_0 := h3726c.1
                              have p3726_1 := h3726c.2.1
                              have p3726_2 := h3726c.2.2.1
                              have p3726_3 := h3726c.2.2.2
                              linarith only [h3718, hlam, p3726_0]
                            · have p3726_0 := h3726c.1
                              have p3726_1 := h3726c.2.1
                              have p3726_2 := h3726c.2.2.1
                              have p3726_3 := h3726c.2.2.2
                              rcases p3726_3 (m.d 0 2) (by simp) with h3737 | h3737
                              · linarith only [h3737, hlam, p3726_0]
                              · rcases p3726_3 (m.d 1 2) (by simp) with h3739 | h3739
                                · linarith only [h3663, h3739, hlam]
                                · linarith only [h0, h3739, hlam]
                            · have p3726_0 := h3726c.1
                              have p3726_1 := h3726c.2.1
                              have p3726_2 := h3726c.2.2.1
                              have p3726_3 := h3726c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p3726_1]
                            · have p3726_0 := h3726c.1
                              have p3726_1 := h3726c.2.1
                              have p3726_2 := h3726c.2.2.1
                              have p3726_3 := h3726c.2.2.2
                              linarith only [hlam, p3726_0]
                            · have p3726_0 := h3726c.1
                              have p3726_1 := h3726c.2.1
                              have p3726_2 := h3726c.2.2.1
                              have p3726_3 := h3726c.2.2.2
                              linarith only [h0, h2897, hc01, hc23, hlam, hphi, ht12, p3726_1]
                            · have p3726_0 := h3726c.1
                              have p3726_1 := h3726c.2.1
                              have p3726_2 := h3726c.2.2.1
                              have p3726_3 := h3726c.2.2.2
                              linarith only [h0, h3718, hc01, hc23, hlam, hphi, ht12, p3726_1]
                            · have p3726_0 := h3726c.1
                              have p3726_1 := h3726c.2.1
                              have p3726_2 := h3726c.2.2.1
                              have p3726_3 := h3726c.2.2.2
                              rcases p3726_3 (m.d 0 2) (by simp) with h3746 | h3746
                              · linarith only [h3746, hlam, p3726_0]
                              · rcases p3726_3 (m.d 1 2) (by simp) with h3748 | h3748
                                · linarith only [h3716, h3748, hlam]
                                · linarith only [h0, h3748, hlam]
                            · have p3726_0 := h3726c.1
                              have p3726_1 := h3726c.2.1
                              have p3726_2 := h3726c.2.2.1
                              have p3726_3 := h3726c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p3726_1]
                            · have p3726_0 := h3726c.1
                              have p3726_1 := h3726c.2.1
                              have p3726_2 := h3726c.2.2.1
                              have p3726_3 := h3726c.2.2.2
                              linarith only [h3722, hlam, p3726_1]
                            · have p3726_0 := h3726c.1
                              have p3726_1 := h3726c.2.1
                              have p3726_2 := h3726c.2.2.1
                              have p3726_3 := h3726c.2.2.2
                              linarith only [hlam, p3726_0]
                            · have p3726_0 := h3726c.1
                              have p3726_1 := h3726c.2.1
                              have p3726_2 := h3726c.2.2.1
                              have p3726_3 := h3726c.2.2.2
                              linarith only [h0, h3718, h3722, hc01, hc23, hlam, hphi, ht12, p3726_1]
                            · have p3726_0 := h3726c.1
                              have p3726_1 := h3726c.2.1
                              have p3726_2 := h3726c.2.2.1
                              have p3726_3 := h3726c.2.2.2
                              rcases p3726_3 (m.d 0 2) (by simp) with h3755 | h3755
                              · linarith only [h3755, hlam, p3726_0]
                              · rcases p3726_3 (m.d 1 2) (by simp) with h3757 | h3757
                                · linarith only [h3718, h3757, hlam]
                                · linarith only [h0, h3757, hlam]
                            · have p3726_0 := h3726c.1
                              have p3726_1 := h3726c.2.1
                              have p3726_2 := h3726c.2.2.1
                              have p3726_3 := h3726c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3726_1]
                            · have p3726_0 := h3726c.1
                              have p3726_1 := h3726c.2.1
                              have p3726_2 := h3726c.2.2.1
                              have p3726_3 := h3726c.2.2.2
                              linarith only [h3723, hlam, p3726_1]
                            · have p3726_0 := h3726c.1
                              have p3726_1 := h3726c.2.1
                              have p3726_2 := h3726c.2.2.1
                              have p3726_3 := h3726c.2.2.2
                              linarith only [h3724, hlam, p3726_0]
                            · have p3726_0 := h3726c.1
                              have p3726_1 := h3726c.2.1
                              have p3726_2 := h3726c.2.2.1
                              have p3726_3 := h3726c.2.2.2
                              linarith only [hlam, p3726_0]
                          · linarith only [h3277, h3662, h3725, hlam]
                        · linarith only [h0, h2897, h3662, h3724, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h3277, h3662, h3663, h3720, h3723, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · linarith only [h3663, h3720, h3722, hlam]
                  · linarith only [h3277, h3662, h3720, h3721, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3769 | h3769
                  · linarith only [h0, h2055, h3599, h3720, h3769, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3771 | h3771
                    · linarith only [h1494, h3720, h3771, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h3663, h3771, hc01, hc34, hlam, hphi, ht12, ht23]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3774 | h3774
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3775 | h3775
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3776 | h3776
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3777 | h3777
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3778 | h3778
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3779 | h3779
                    · linarith only [h0, h2055, h3277, h3774, h3779, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h2055, h3774, h3777, h3779, hc01, hc12, hlam, hphi]
                  · linarith only [h3277, h3777, h3778, hc03, hc35, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3783 | h3783
                  · linarith only [h0, h2055, h3599, h3777, h3783, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3785 | h3785
                    · linarith only [h1494, h3777, h3785, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3787 | h3787
                      · linarith only [h3774, h3783, h3787, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3789 | h3789
                        · linarith only [h0, h2897, h3662, h3775, h3789, hc01, hc12, hlam, hphi]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3791 | h3791
                          · linarith only [h0, h2897, h3789, h3791, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h0, h2055, h3774, h3777, h3791, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · linarith only [h0, h2055, h3774, h3776, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h2055, h3774, h3775, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3796 | h3796
            · linarith only [h0, h2897, h3774, h3796, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3798 | h3798
              · linarith only [h0, h3206, h3774, h3798, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3800 | h3800
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3801 | h3801
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3802 | h3802
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3803 | h3803
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3804 | h3804
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3805 | h3805
                          · linarith only [h0, h2055, h3277, h3662, h3800, h3805, hc01, hc13, hlam, hphi]
                          · linarith only [h0, h2055, h3277, h3802, h3804, h3805, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h3796, h3804, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h3774, h3801, h3803, hlam]
                    · linarith only [h0, h2055, h3599, h3774, h3801, h3802, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h2055, h3277, h3800, h3801, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3812 | h3812
                  · linarith only [h0, h2055, h3599, h3800, h3812, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3814 | h3814
                    · linarith only [h1494, h3800, h3814, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h3774, h3814, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 7634000 in
theorem r1l7_10_12_13_25_L_0_L_I_L_I_M_IR_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1494 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2055 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h2897 | h2897
  · exact r1l7_10_12_13_25_L_0_L_I_L_I_M_IR_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 h0 h1494 h2055 h2897
  · exact r1l7_10_12_13_25_L_0_L_I_L_I_M_IR_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 h0 h1494 h2055 h2897

set_option maxHeartbeats 7634000 in
theorem r1l7_10_12_13_25_L_0_L_I_L_I_M_IR_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1494 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  rcases m.htr 0 2 3 (by decide) (by decide) with h2055 | h2055
  · exact r1l7_10_12_13_25_L_0_L_I_L_I_M_IR_x1_x1_x0 m hb0 hb2 hb3 hb5 h0 h1494 h2055
  · exact r1l7_10_12_13_25_L_0_L_I_L_I_M_IR_x1_x1_x1 m hb0 hb2 hb3 hb5 h0 h1494 h2055

set_option maxHeartbeats 7634000 in
theorem r1l7_10_12_13_25_L_0_L_I_L_I_M_IR_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  rcases m.htr 0 1 3 (by decide) (by decide) with h1494 | h1494
  · exact r1l7_10_12_13_25_L_0_L_I_L_I_M_IR_x1_x0 m hb0 hb2 hb3 hb5 h0 h1494
  · exact r1l7_10_12_13_25_L_0_L_I_L_I_M_IR_x1_x1 m hb0 hb2 hb3 hb5 h0 h1494

set_option maxHeartbeats 7634000 in
theorem r1l7_10_12_13_25_L_0_L_I_L_I_M_IR (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_13_25_L_0_L_I_L_I_M_IR_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_10_12_13_25_L_0_L_I_L_I_M_IR_x1 m hb0 hb2 hb3 hb5 h0

end R2N4
