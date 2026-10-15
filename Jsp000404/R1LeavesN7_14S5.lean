import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_14S4

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7196000 in
set_option maxHeartbeats 7196000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s2 m hb0 hb2 hb3 hb5 h0 h1 h2
  · rcases m.htr 0 1 5 (by decide) (by decide) with h3283 | h3283
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3284 | h3284
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3285 | h3285
        · linarith only [h0, h2, h3285, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3287 | h3287
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3288 | h3288
            · linarith only [h1, h2, h3288, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3290 | h3290
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3291 | h3291
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3292 | h3292
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3293 | h3293
                    · linarith only [h0, h3285, h3293, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3295 | h3295
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3296 | h3296
                        · linarith only [h0, h1, h2, h3288, h3292, h3296, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h2, h3292, h3296, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h2, h3287, h3292, h3293, h3295, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h3284, h3285, h3292, hc12, hc24, hlam, hphi]
                · linarith only [h0, h2, h3284, h3290, h3291, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3302 | h3302
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3303 | h3303
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3304 | h3304
                    · linarith only [h0, h3285, h3304, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3306 | h3306
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3307 | h3307
                        · linarith only [h1, h3288, h3307, hlam]
                        · linarith only [h0, h2, h3303, h3307, hc23, hc34, hlam, hphi]
                      · linarith only [h3287, h3303, h3306, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h3284, h3285, h3303, hc12, hc24, hlam, hphi]
                · linarith only [h2, h3283, h3302, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3313 | h3313
            · linarith only [h1, h2, h3313, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3315 | h3315
              · linarith only [h3284, h3287, h3315, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3317 | h3317
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3318 | h3318
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3319 | h3319
                    · linarith only [h0, h3285, h3319, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3321 | h3321
                      · linarith only [h0, h3287, h3321, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3323 | h3323
                        · linarith only [h0, h2, h3313, h3318, h3323, hlam]
                        · linarith only [h2, h3283, h3318, h3321, h3323, hc23, hc34, hlam, hphi]
                  · linarith only [h3284, h3287, h3318, hc12, hc25, hlam, hphi]
                · linarith only [h2, h3283, h3317, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3328 | h3328
        · linarith only [h0, h2, h3328, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3330 | h3330
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3331 | h3331
            · linarith only [h1, h2, h3331, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3333 | h3333
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3334 | h3334
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3335 | h3335
                  · linarith only [h0, h3284, h3335, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3337 | h3337
                    · linarith only [h0, h2, h3328, h3337, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3339 | h3339
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3340 | h3340
                        · linarith only [h1, h2, h3331, h3340, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3342 | h3342
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3343 | h3343
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3344 | h3344
                              · linarith only [h1, h2, h3335, h3340, h3344, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3346 | h3346
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3347 | h3347
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3348 | h3348
                                    · rcases h0bigk with h3349c | h3349c | h3349c | h3349c | h3349c | h3349c | h3349c | h3349c | h3349c | h3349c | h3349c | h3349c | h3349c | h3349c | h3349c | h3349c | h3349c | h3349c | h3349c | h3349c | h3349c | h3349c | h3349c | h3349c | h3349c
                                      · have p3349_0 := h3349c.1
                                        have p3349_1 := h3349c.2.1
                                        have p3349_2 := h3349c.2.2.1
                                        have p3349_3 := h3349c.2.2.2
                                        linarith only [hlam, p3349_0]
                                      · have p3349_0 := h3349c.1
                                        have p3349_1 := h3349c.2.1
                                        have p3349_2 := h3349c.2.2.1
                                        have p3349_3 := h3349c.2.2.2
                                        linarith only [h2, h3337, h3344, hc02, hc34, hlam, hphi, ht23, p3349_1]
                                      · have p3349_0 := h3349c.1
                                        have p3349_1 := h3349c.2.1
                                        have p3349_2 := h3349c.2.2.1
                                        have p3349_3 := h3349c.2.2.2
                                        linarith only [h0, h2, h3284, h3337, h3339, h3344, h3346, h3348, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3349_1]
                                      · have p3349_0 := h3349c.1
                                        have p3349_1 := h3349c.2.1
                                        have p3349_2 := h3349c.2.2.1
                                        have p3349_3 := h3349c.2.2.2
                                        linarith only [h2, hlam, p3349_1]
                                      · have p3349_0 := h3349c.1
                                        have p3349_1 := h3349c.2.1
                                        have p3349_2 := h3349c.2.2.1
                                        have p3349_3 := h3349c.2.2.2
                                        rcases p3349_3 (m.d 0 1) (by simp) with h3354 | h3354
                                        · rcases p3349_3 (m.d 0 2) (by simp) with h3355 | h3355
                                          · linarith only [h0, h3355, hlam]
                                          · linarith only [h3330, h3355, hlam]
                                        · linarith only [h3283, h3354, hlam]
                                      · have p3349_0 := h3349c.1
                                        have p3349_1 := h3349c.2.1
                                        have p3349_2 := h3349c.2.2.1
                                        have p3349_3 := h3349c.2.2.2
                                        linarith only [h0, hlam, p3349_0]
                                      · have p3349_0 := h3349c.1
                                        have p3349_1 := h3349c.2.1
                                        have p3349_2 := h3349c.2.2.1
                                        have p3349_3 := h3349c.2.2.2
                                        linarith only [hlam, p3349_0]
                                      · have p3349_0 := h3349c.1
                                        have p3349_1 := h3349c.2.1
                                        have p3349_2 := h3349c.2.2.1
                                        have p3349_3 := h3349c.2.2.2
                                        linarith only [h3284, hlam, p3349_0]
                                      · have p3349_0 := h3349c.1
                                        have p3349_1 := h3349c.2.1
                                        have p3349_2 := h3349c.2.2.1
                                        have p3349_3 := h3349c.2.2.2
                                        linarith only [h3328, hlam, p3349_1]
                                      · have p3349_0 := h3349c.1
                                        have p3349_1 := h3349c.2.1
                                        have p3349_2 := h3349c.2.2.1
                                        have p3349_3 := h3349c.2.2.2
                                        linarith only [h3283, h3284, h3344, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3349_1]
                                      · have p3349_0 := h3349c.1
                                        have p3349_1 := h3349c.2.1
                                        have p3349_2 := h3349c.2.2.1
                                        have p3349_3 := h3349c.2.2.2
                                        linarith only [h1, hlam, p3349_1]
                                      · have p3349_0 := h3349c.1
                                        have p3349_1 := h3349c.2.1
                                        have p3349_2 := h3349c.2.2.1
                                        have p3349_3 := h3349c.2.2.2
                                        linarith only [h0, h3339, h3346, h3348, hc45, hlam, hphi, ht0b, ht5b, p3349_1, u0elo2]
                                      · have p3349_0 := h3349c.1
                                        have p3349_1 := h3349c.2.1
                                        have p3349_2 := h3349c.2.2.1
                                        have p3349_3 := h3349c.2.2.2
                                        linarith only [hlam, p3349_0]
                                      · have p3349_0 := h3349c.1
                                        have p3349_1 := h3349c.2.1
                                        have p3349_2 := h3349c.2.2.1
                                        have p3349_3 := h3349c.2.2.2
                                        linarith only [h3331, hlam, p3349_1]
                                      · have p3349_0 := h3349c.1
                                        have p3349_1 := h3349c.2.1
                                        have p3349_2 := h3349c.2.2.1
                                        have p3349_3 := h3349c.2.2.2
                                        rcases p3349_3 (m.d 0 1) (by simp) with h3368 | h3368
                                        · rcases p3349_3 (m.d 0 2) (by simp) with h3369 | h3369
                                          · linarith only [h3284, h3369, hlam]
                                          · linarith only [h3330, h3369, hlam]
                                        · linarith only [h3283, h3368, hlam]
                                      · have p3349_0 := h3349c.1
                                        have p3349_1 := h3349c.2.1
                                        have p3349_2 := h3349c.2.2.1
                                        have p3349_3 := h3349c.2.2.2
                                        linarith only [h0, h3339, h3346, h3348, hc45, hlam, hphi, ht0b, ht5b, p3349_1, u0elo3]
                                      · have p3349_0 := h3349c.1
                                        have p3349_1 := h3349c.2.1
                                        have p3349_2 := h3349c.2.2.1
                                        have p3349_3 := h3349c.2.2.2
                                        linarith only [h0, h3339, h3346, h3348, hc45, hlam, hphi, ht0b, ht5b, p3349_1, u0elo3]
                                      · have p3349_0 := h3349c.1
                                        have p3349_1 := h3349c.2.1
                                        have p3349_2 := h3349c.2.2.1
                                        have p3349_3 := h3349c.2.2.2
                                        linarith only [h1, h3335, h3339, h3346, h3348, hc45, hlam, hphi, ht0b, ht5b, p3349_1, u0elo3]
                                      · have p3349_0 := h3349c.1
                                        have p3349_1 := h3349c.2.1
                                        have p3349_2 := h3349c.2.2.1
                                        have p3349_3 := h3349c.2.2.2
                                        linarith only [hlam, p3349_0]
                                      · have p3349_0 := h3349c.1
                                        have p3349_1 := h3349c.2.1
                                        have p3349_2 := h3349c.2.2.1
                                        have p3349_3 := h3349c.2.2.2
                                        rcases p3349_3 (m.d 0 1) (by simp) with h3377 | h3377
                                        · linarith only [h2, h3377, hlam]
                                        · linarith only [h3283, h3377, hlam]
                                      · have p3349_0 := h3349c.1
                                        have p3349_1 := h3349c.2.1
                                        have p3349_2 := h3349c.2.2.1
                                        have p3349_3 := h3349c.2.2.2
                                        linarith only [h3283, hlam, p3349_0]
                                      · have p3349_0 := h3349c.1
                                        have p3349_1 := h3349c.2.1
                                        have p3349_2 := h3349c.2.2.1
                                        have p3349_3 := h3349c.2.2.2
                                        linarith only [h3330, hlam, p3349_1]
                                      · have p3349_0 := h3349c.1
                                        have p3349_1 := h3349c.2.1
                                        have p3349_2 := h3349c.2.2.1
                                        have p3349_3 := h3349c.2.2.2
                                        linarith only [h3333, hlam, p3349_0]
                                      · have p3349_0 := h3349c.1
                                        have p3349_1 := h3349c.2.1
                                        have p3349_2 := h3349c.2.2.1
                                        have p3349_3 := h3349c.2.2.2
                                        linarith only [h3334, hlam, p3349_1]
                                      · have p3349_0 := h3349c.1
                                        have p3349_1 := h3349c.2.1
                                        have p3349_2 := h3349c.2.2.1
                                        have p3349_3 := h3349c.2.2.2
                                        linarith only [hlam, p3349_0]
                                    · linarith only [h3284, h3344, h3348, hc02, hc45, hlam, hphi, ht23, ht34]
                                  · linarith only [h1, h2, h3283, h3335, h3337, h3339, h3343, h3346, h3347, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                                · linarith only [h0, h3284, h3333, h3339, h3346, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                            · linarith only [h1, h2, h3343, hc13, hc45, hlam, hphi, ht34]
                          · linarith only [h3333, h3335, h3339, h3342, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                      · linarith only [h1, h2, h3284, h3330, h3337, h3339, hc12, hc24, hlam, hphi]
                · linarith only [h1, h2, h3284, h3330, h3334, hlam]
              · linarith only [h3284, h3330, h3333, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3393 | h3393
            · linarith only [h1, h2, h3393, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3395 | h3395
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3396 | h3396
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3397 | h3397
                  · linarith only [h0, h3284, h3397, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3399 | h3399
                    · linarith only [h0, h3328, h3399, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3401 | h3401
                      · linarith only [h0, h3330, h3401, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3403 | h3403
                        · linarith only [h1, h2, h3393, h3399, h3403, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3405 | h3405
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3406 | h3406
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3407 | h3407
                              · linarith only [h0, h2, h3403, h3407, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3409 | h3409
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3410 | h3410
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3411 | h3411
                                    · rcases h0bigk with h3412c | h3412c | h3412c | h3412c | h3412c | h3412c | h3412c | h3412c | h3412c | h3412c | h3412c | h3412c | h3412c | h3412c | h3412c | h3412c | h3412c | h3412c | h3412c | h3412c | h3412c | h3412c | h3412c | h3412c | h3412c
                                      · have p3412_0 := h3412c.1
                                        have p3412_1 := h3412c.2.1
                                        have p3412_2 := h3412c.2.2.1
                                        have p3412_3 := h3412c.2.2.2
                                        linarith only [hlam, p3412_0]
                                      · have p3412_0 := h3412c.1
                                        have p3412_1 := h3412c.2.1
                                        have p3412_2 := h3412c.2.2.1
                                        have p3412_3 := h3412c.2.2.2
                                        linarith only [h0, h2, h3399, hc12, hc24, hlam, hphi, p3412_1]
                                      · have p3412_0 := h3412c.1
                                        have p3412_1 := h3412c.2.1
                                        have p3412_2 := h3412c.2.2.1
                                        have p3412_3 := h3412c.2.2.2
                                        linarith only [h1, h2, h3399, h3405, h3411, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3412_1]
                                      · have p3412_0 := h3412c.1
                                        have p3412_1 := h3412c.2.1
                                        have p3412_2 := h3412c.2.2.1
                                        have p3412_3 := h3412c.2.2.2
                                        linarith only [h2, hlam, p3412_1]
                                      · have p3412_0 := h3412c.1
                                        have p3412_1 := h3412c.2.1
                                        have p3412_2 := h3412c.2.2.1
                                        have p3412_3 := h3412c.2.2.2
                                        linarith only [h0, h2, h3330, h3399, hc12, hc24, hlam, hphi, p3412_1]
                                      · have p3412_0 := h3412c.1
                                        have p3412_1 := h3412c.2.1
                                        have p3412_2 := h3412c.2.2.1
                                        have p3412_3 := h3412c.2.2.2
                                        linarith only [h0, hlam, p3412_0]
                                      · have p3412_0 := h3412c.1
                                        have p3412_1 := h3412c.2.1
                                        have p3412_2 := h3412c.2.2.1
                                        have p3412_3 := h3412c.2.2.2
                                        linarith only [hlam, p3412_0]
                                      · have p3412_0 := h3412c.1
                                        have p3412_1 := h3412c.2.1
                                        have p3412_2 := h3412c.2.2.1
                                        have p3412_3 := h3412c.2.2.2
                                        linarith only [h3284, hlam, p3412_0]
                                      · have p3412_0 := h3412c.1
                                        have p3412_1 := h3412c.2.1
                                        have p3412_2 := h3412c.2.2.1
                                        have p3412_3 := h3412c.2.2.2
                                        linarith only [h3328, hlam, p3412_1]
                                      · have p3412_0 := h3412c.1
                                        have p3412_1 := h3412c.2.1
                                        have p3412_2 := h3412c.2.2.1
                                        have p3412_3 := h3412c.2.2.2
                                        linarith only [h3330, hlam, p3412_0]
                                      · have p3412_0 := h3412c.1
                                        have p3412_1 := h3412c.2.1
                                        have p3412_2 := h3412c.2.2.1
                                        have p3412_3 := h3412c.2.2.2
                                        linarith only [h1, hlam, p3412_1]
                                      · have p3412_0 := h3412c.1
                                        have p3412_1 := h3412c.2.1
                                        have p3412_2 := h3412c.2.2.1
                                        have p3412_3 := h3412c.2.2.2
                                        linarith only [h0, h1, h2, h3399, hc12, hc24, hlam, hphi, p3412_1]
                                      · have p3412_0 := h3412c.1
                                        have p3412_1 := h3412c.2.1
                                        have p3412_2 := h3412c.2.2.1
                                        have p3412_3 := h3412c.2.2.2
                                        linarith only [hlam, p3412_0]
                                      · have p3412_0 := h3412c.1
                                        have p3412_1 := h3412c.2.1
                                        have p3412_2 := h3412c.2.2.1
                                        have p3412_3 := h3412c.2.2.2
                                        linarith only [h3393, hlam, p3412_1]
                                      · have p3412_0 := h3412c.1
                                        have p3412_1 := h3412c.2.1
                                        have p3412_2 := h3412c.2.2.1
                                        have p3412_3 := h3412c.2.2.2
                                        linarith only [h0, h1, h2, h3330, h3399, hc12, hc24, hlam, hphi, p3412_1]
                                      · have p3412_0 := h3412c.1
                                        have p3412_1 := h3412c.2.1
                                        have p3412_2 := h3412c.2.2.1
                                        have p3412_3 := h3412c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3412_1, u0elo3]
                                      · have p3412_0 := h3412c.1
                                        have p3412_1 := h3412c.2.1
                                        have p3412_2 := h3412c.2.2.1
                                        have p3412_3 := h3412c.2.2.2
                                        rcases p3412_3 (m.d 0 1) (by simp) with h3429 | h3429
                                        · linarith only [h2, h3429, hlam]
                                        · linarith only [h0, h3429, hlam]
                                      · have p3412_0 := h3412c.1
                                        have p3412_1 := h3412c.2.1
                                        have p3412_2 := h3412c.2.2.1
                                        have p3412_3 := h3412c.2.2.2
                                        linarith only [h1, h3405, h3411, hc45, hlam, hphi, ht0b, ht5b, p3412_1, u0elo3]
                                      · have p3412_0 := h3412c.1
                                        have p3412_1 := h3412c.2.1
                                        have p3412_2 := h3412c.2.2.1
                                        have p3412_3 := h3412c.2.2.2
                                        linarith only [hlam, p3412_0]
                                      · have p3412_0 := h3412c.1
                                        have p3412_1 := h3412c.2.1
                                        have p3412_2 := h3412c.2.2.1
                                        have p3412_3 := h3412c.2.2.2
                                        rcases p3412_3 (m.d 0 1) (by simp) with h3434 | h3434
                                        · linarith only [h2, h3434, hlam]
                                        · linarith only [h3283, h3434, hlam]
                                      · have p3412_0 := h3412c.1
                                        have p3412_1 := h3412c.2.1
                                        have p3412_2 := h3412c.2.2.1
                                        have p3412_3 := h3412c.2.2.2
                                        linarith only [h3283, hlam, p3412_0]
                                      · have p3412_0 := h3412c.1
                                        have p3412_1 := h3412c.2.1
                                        have p3412_2 := h3412c.2.2.1
                                        have p3412_3 := h3412c.2.2.2
                                        linarith only [h0, h2, h3283, h3399, h3407, hc12, hc34, hlam, hphi, ht23, p3412_1]
                                      · have p3412_0 := h3412c.1
                                        have p3412_1 := h3412c.2.1
                                        have p3412_2 := h3412c.2.2.1
                                        have p3412_3 := h3412c.2.2.2
                                        linarith only [h3395, hlam, p3412_0]
                                      · have p3412_0 := h3412c.1
                                        have p3412_1 := h3412c.2.1
                                        have p3412_2 := h3412c.2.2.1
                                        have p3412_3 := h3412c.2.2.2
                                        linarith only [h3396, hlam, p3412_1]
                                      · have p3412_0 := h3412c.1
                                        have p3412_1 := h3412c.2.1
                                        have p3412_2 := h3412c.2.2.1
                                        have p3412_3 := h3412c.2.2.2
                                        linarith only [hlam, p3412_0]
                                    · linarith only [h1, h2, h3399, h3405, h3407, h3411, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                                  · linarith only [h1, h2, h3399, h3405, h3406, h3410, hc15, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h1, h3405, h3409, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · linarith only [h1, h2, h3395, h3396, h3406, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h1, h2, h3395, h3397, h3403, h3405, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h1, h2, h3395, h3396, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3448 | h3448
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3449 | h3449
                  · linarith only [h0, h3284, h3449, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3451 | h3451
                    · linarith only [h0, h3328, h3451, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3453 | h3453
                      · linarith only [h0, h3330, h3453, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3455 | h3455
                        · linarith only [h1, h2, h3284, h3393, h3451, h3455, hc02, hc24, hlam, hphi]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3457 | h3457
                          · linarith only [h1, h3395, h3457, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3459 | h3459
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3460 | h3460
                              · linarith only [h0, h2, h3455, h3460, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3462 | h3462
                                · linarith only [h0, h3284, h3395, h3460, h3462, hc12, hc34, hlam, hphi, ht23]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3464 | h3464
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3465 | h3465
                                    · rcases h0bigk with h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c | h3466c
                                      · have p3466_0 := h3466c.1
                                        have p3466_1 := h3466c.2.1
                                        have p3466_2 := h3466c.2.2.1
                                        have p3466_3 := h3466c.2.2.2
                                        linarith only [hlam, p3466_0]
                                      · have p3466_0 := h3466c.1
                                        have p3466_1 := h3466c.2.1
                                        have p3466_2 := h3466c.2.2.1
                                        have p3466_3 := h3466c.2.2.2
                                        linarith only [h0, h2, h3451, hc12, hc24, hlam, hphi, p3466_1]
                                      · have p3466_0 := h3466c.1
                                        have p3466_1 := h3466c.2.1
                                        have p3466_2 := h3466c.2.2.1
                                        have p3466_3 := h3466c.2.2.2
                                        linarith only [h0, h2, h3284, h3451, hc12, hc24, hlam, hphi, p3466_1]
                                      · have p3466_0 := h3466c.1
                                        have p3466_1 := h3466c.2.1
                                        have p3466_2 := h3466c.2.2.1
                                        have p3466_3 := h3466c.2.2.2
                                        linarith only [h2, hlam, p3466_1]
                                      · have p3466_0 := h3466c.1
                                        have p3466_1 := h3466c.2.1
                                        have p3466_2 := h3466c.2.2.1
                                        have p3466_3 := h3466c.2.2.2
                                        linarith only [h0, h2, h3284, h3395, h3451, hc12, hc24, hlam, hphi, p3466_1]
                                      · have p3466_0 := h3466c.1
                                        have p3466_1 := h3466c.2.1
                                        have p3466_2 := h3466c.2.2.1
                                        have p3466_3 := h3466c.2.2.2
                                        linarith only [h0, hlam, p3466_0]
                                      · have p3466_0 := h3466c.1
                                        have p3466_1 := h3466c.2.1
                                        have p3466_2 := h3466c.2.2.1
                                        have p3466_3 := h3466c.2.2.2
                                        linarith only [hlam, p3466_0]
                                      · have p3466_0 := h3466c.1
                                        have p3466_1 := h3466c.2.1
                                        have p3466_2 := h3466c.2.2.1
                                        have p3466_3 := h3466c.2.2.2
                                        linarith only [h3284, hlam, p3466_0]
                                      · have p3466_0 := h3466c.1
                                        have p3466_1 := h3466c.2.1
                                        have p3466_2 := h3466c.2.2.1
                                        have p3466_3 := h3466c.2.2.2
                                        linarith only [h3328, hlam, p3466_1]
                                      · have p3466_0 := h3466c.1
                                        have p3466_1 := h3466c.2.1
                                        have p3466_2 := h3466c.2.2.1
                                        have p3466_3 := h3466c.2.2.2
                                        linarith only [h3330, hlam, p3466_0]
                                      · have p3466_0 := h3466c.1
                                        have p3466_1 := h3466c.2.1
                                        have p3466_2 := h3466c.2.2.1
                                        have p3466_3 := h3466c.2.2.2
                                        linarith only [h1, hlam, p3466_1]
                                      · have p3466_0 := h3466c.1
                                        have p3466_1 := h3466c.2.1
                                        have p3466_2 := h3466c.2.2.1
                                        have p3466_3 := h3466c.2.2.2
                                        linarith only [h0, h1, h2, h3451, hc12, hc24, hlam, hphi, p3466_1]
                                      · have p3466_0 := h3466c.1
                                        have p3466_1 := h3466c.2.1
                                        have p3466_2 := h3466c.2.2.1
                                        have p3466_3 := h3466c.2.2.2
                                        linarith only [hlam, p3466_0]
                                      · have p3466_0 := h3466c.1
                                        have p3466_1 := h3466c.2.1
                                        have p3466_2 := h3466c.2.2.1
                                        have p3466_3 := h3466c.2.2.2
                                        linarith only [h3393, hlam, p3466_1]
                                      · have p3466_0 := h3466c.1
                                        have p3466_1 := h3466c.2.1
                                        have p3466_2 := h3466c.2.2.1
                                        have p3466_3 := h3466c.2.2.2
                                        linarith only [h3395, hlam, p3466_1]
                                      · have p3466_0 := h3466c.1
                                        have p3466_1 := h3466c.2.1
                                        have p3466_2 := h3466c.2.2.1
                                        have p3466_3 := h3466c.2.2.2
                                        linarith only [h1, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3466_1, u0elo3]
                                      · have p3466_0 := h3466c.1
                                        have p3466_1 := h3466c.2.1
                                        have p3466_2 := h3466c.2.2.1
                                        have p3466_3 := h3466c.2.2.2
                                        rcases p3466_3 (m.d 0 1) (by simp) with h3483 | h3483
                                        · linarith only [h2, h3483, hlam]
                                        · linarith only [h0, h3483, hlam]
                                      · have p3466_0 := h3466c.1
                                        have p3466_1 := h3466c.2.1
                                        have p3466_2 := h3466c.2.2.1
                                        have p3466_3 := h3466c.2.2.2
                                        rcases p3466_3 (m.d 0 1) (by simp) with h3486 | h3486
                                        · linarith only [h2, h3486, hlam]
                                        · linarith only [h1, h3486, hlam]
                                      · have p3466_0 := h3466c.1
                                        have p3466_1 := h3466c.2.1
                                        have p3466_2 := h3466c.2.2.1
                                        have p3466_3 := h3466c.2.2.2
                                        linarith only [hlam, p3466_0]
                                      · have p3466_0 := h3466c.1
                                        have p3466_1 := h3466c.2.1
                                        have p3466_2 := h3466c.2.2.1
                                        have p3466_3 := h3466c.2.2.2
                                        rcases p3466_3 (m.d 0 1) (by simp) with h3490 | h3490
                                        · linarith only [h2, h3490, hlam]
                                        · linarith only [h3283, h3490, hlam]
                                      · have p3466_0 := h3466c.1
                                        have p3466_1 := h3466c.2.1
                                        have p3466_2 := h3466c.2.2.1
                                        have p3466_3 := h3466c.2.2.2
                                        linarith only [h3283, hlam, p3466_0]
                                      · have p3466_0 := h3466c.1
                                        have p3466_1 := h3466c.2.1
                                        have p3466_2 := h3466c.2.2.1
                                        have p3466_3 := h3466c.2.2.2
                                        linarith only [h0, h2, h3283, h3451, h3460, hc12, hc34, hlam, hphi, ht23, p3466_1]
                                      · have p3466_0 := h3466c.1
                                        have p3466_1 := h3466c.2.1
                                        have p3466_2 := h3466c.2.2.1
                                        have p3466_3 := h3466c.2.2.2
                                        linarith only [h1, h2, h3283, h3449, h3451, h3460, hc12, hc34, hlam, hphi, ht23, p3466_1]
                                      · have p3466_0 := h3466c.1
                                        have p3466_1 := h3466c.2.1
                                        have p3466_2 := h3466c.2.2.1
                                        have p3466_3 := h3466c.2.2.2
                                        linarith only [h3448, hlam, p3466_1]
                                      · have p3466_0 := h3466c.1
                                        have p3466_1 := h3466c.2.1
                                        have p3466_2 := h3466c.2.2.1
                                        have p3466_3 := h3466c.2.2.2
                                        linarith only [hlam, p3466_0]
                                    · linarith only [h0, h2, h3451, h3460, h3465, hc12, hc45, hlam, hphi, ht23, ht34]
                                  · linarith only [h2, h3283, h3451, h3459, h3464, hlam]
                            · linarith only [h2, h3283, h3449, h3457, h3459, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h2, h3283, h3448, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3502 | h3502
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3503 | h3503
        · linarith only [h0, h2, h3503, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3505 | h3505
          · linarith only [h0, h3283, h3505, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3507 | h3507
            · linarith only [h1, h2, h3507, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3509 | h3509
              · linarith only [h0, h3283, h3502, h3509, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3511 | h3511
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3512 | h3512
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3513 | h3513
                    · linarith only [h0, h3283, h3503, h3511, h3513, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3515 | h3515
                      · linarith only [h0, h3283, h3505, h3515, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3517 | h3517
                        · linarith only [h1, h2, h3507, h3513, h3517, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · linarith only [h0, h2, h3512, h3517, hc23, hc34, hlam, hphi]
                  · linarith only [h3502, h3503, h3512, hc12, hc24, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3521 | h3521
                  · linarith only [h0, h2, h3511, h3521, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h2, h3502, h3511, h3521, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3524 | h3524
        · linarith only [h0, h2, h3524, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3526 | h3526
          · linarith only [h1, h3283, h3502, h3526, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3528 | h3528
            · linarith only [h1, h2, h3528, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3530 | h3530
              · linarith only [h1, h3283, h3530, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3532 | h3532
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3533 | h3533
                  · linarith only [h0, h3502, h3533, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3535 | h3535
                    · linarith only [h0, h3283, h3524, h3532, h3535, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3537 | h3537
                      · linarith only [h1, h3526, h3533, h3537, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3539 | h3539
                        · linarith only [h1, h2, h3528, h3535, h3539, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3541 | h3541
                          · linarith only [h1, h3283, h3530, h3541, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3543 | h3543
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3544 | h3544
                              · linarith only [h0, h3283, h3539, h3543, h3544, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3546 | h3546
                                · linarith only [h1, h3283, h3533, h3541, h3546, hc12, hc23, hlam, hphi]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3548 | h3548
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3549 | h3549
                                    · rcases h0bigk with h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c | h3550c
                                      · have p3550_0 := h3550c.1
                                        have p3550_1 := h3550c.2.1
                                        have p3550_2 := h3550c.2.2.1
                                        have p3550_3 := h3550c.2.2.2
                                        linarith only [hlam, p3550_0]
                                      · have p3550_0 := h3550c.1
                                        have p3550_1 := h3550c.2.1
                                        have p3550_2 := h3550c.2.2.1
                                        have p3550_3 := h3550c.2.2.2
                                        linarith only [h0, h3283, h3535, h3543, hc12, hc24, hlam, hphi, p3550_1]
                                      · have p3550_0 := h3550c.1
                                        have p3550_1 := h3550c.2.1
                                        have p3550_2 := h3550c.2.2.1
                                        have p3550_3 := h3550c.2.2.2
                                        linarith only [h0, h3283, h3502, h3535, h3543, hc12, hc24, hlam, hphi, p3550_1]
                                      · have p3550_0 := h3550c.1
                                        have p3550_1 := h3550c.2.1
                                        have p3550_2 := h3550c.2.2.1
                                        have p3550_3 := h3550c.2.2.2
                                        linarith only [h2, hlam, p3550_1]
                                      · have p3550_0 := h3550c.1
                                        have p3550_1 := h3550c.2.1
                                        have p3550_2 := h3550c.2.2.1
                                        have p3550_3 := h3550c.2.2.2
                                        linarith only [h3283, hlam, p3550_1]
                                      · have p3550_0 := h3550c.1
                                        have p3550_1 := h3550c.2.1
                                        have p3550_2 := h3550c.2.2.1
                                        have p3550_3 := h3550c.2.2.2
                                        linarith only [h0, hlam, p3550_0]
                                      · have p3550_0 := h3550c.1
                                        have p3550_1 := h3550c.2.1
                                        have p3550_2 := h3550c.2.2.1
                                        have p3550_3 := h3550c.2.2.2
                                        linarith only [hlam, p3550_0]
                                      · have p3550_0 := h3550c.1
                                        have p3550_1 := h3550c.2.1
                                        have p3550_2 := h3550c.2.2.1
                                        have p3550_3 := h3550c.2.2.2
                                        linarith only [h3502, hlam, p3550_0]
                                      · have p3550_0 := h3550c.1
                                        have p3550_1 := h3550c.2.1
                                        have p3550_2 := h3550c.2.2.1
                                        have p3550_3 := h3550c.2.2.2
                                        linarith only [h3524, hlam, p3550_1]
                                      · have p3550_0 := h3550c.1
                                        have p3550_1 := h3550c.2.1
                                        have p3550_2 := h3550c.2.2.1
                                        have p3550_3 := h3550c.2.2.2
                                        linarith only [h3526, hlam, p3550_0]
                                      · have p3550_0 := h3550c.1
                                        have p3550_1 := h3550c.2.1
                                        have p3550_2 := h3550c.2.2.1
                                        have p3550_3 := h3550c.2.2.2
                                        linarith only [h1, hlam, p3550_1]
                                      · have p3550_0 := h3550c.1
                                        have p3550_1 := h3550c.2.1
                                        have p3550_2 := h3550c.2.2.1
                                        have p3550_3 := h3550c.2.2.2
                                        linarith only [h0, h1, h3283, h3535, h3543, hc12, hc24, hlam, hphi, p3550_1]
                                      · have p3550_0 := h3550c.1
                                        have p3550_1 := h3550c.2.1
                                        have p3550_2 := h3550c.2.2.1
                                        have p3550_3 := h3550c.2.2.2
                                        linarith only [hlam, p3550_0]
                                      · have p3550_0 := h3550c.1
                                        have p3550_1 := h3550c.2.1
                                        have p3550_2 := h3550c.2.2.1
                                        have p3550_3 := h3550c.2.2.2
                                        linarith only [h3528, hlam, p3550_1]
                                      · have p3550_0 := h3550c.1
                                        have p3550_1 := h3550c.2.1
                                        have p3550_2 := h3550c.2.2.1
                                        have p3550_3 := h3550c.2.2.2
                                        linarith only [h3530, hlam, p3550_1]
                                      · have p3550_0 := h3550c.1
                                        have p3550_1 := h3550c.2.1
                                        have p3550_2 := h3550c.2.2.1
                                        have p3550_3 := h3550c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3550_1, u0elo3]
                                      · have p3550_0 := h3550c.1
                                        have p3550_1 := h3550c.2.1
                                        have p3550_2 := h3550c.2.2.1
                                        have p3550_3 := h3550c.2.2.2
                                        rcases p3550_3 (m.d 0 1) (by simp) with h3567 | h3567
                                        · linarith only [h2, h3567, hlam]
                                        · linarith only [h0, h3567, hlam]
                                      · have p3550_0 := h3550c.1
                                        have p3550_1 := h3550c.2.1
                                        have p3550_2 := h3550c.2.2.1
                                        have p3550_3 := h3550c.2.2.2
                                        rcases p3550_3 (m.d 0 1) (by simp) with h3570 | h3570
                                        · linarith only [h2, h3570, hlam]
                                        · linarith only [h1, h3570, hlam]
                                      · have p3550_0 := h3550c.1
                                        have p3550_1 := h3550c.2.1
                                        have p3550_2 := h3550c.2.2.1
                                        have p3550_3 := h3550c.2.2.2
                                        linarith only [hlam, p3550_0]
                                      · have p3550_0 := h3550c.1
                                        have p3550_1 := h3550c.2.1
                                        have p3550_2 := h3550c.2.2.1
                                        have p3550_3 := h3550c.2.2.2
                                        linarith only [h1, h3283, h3533, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3550_1, u0elo3]
                                      · have p3550_0 := h3550c.1
                                        have p3550_1 := h3550c.2.1
                                        have p3550_2 := h3550c.2.2.1
                                        have p3550_3 := h3550c.2.2.2
                                        linarith only [h1, h3533, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3550_1, u0elo4]
                                      · have p3550_0 := h3550c.1
                                        have p3550_1 := h3550c.2.1
                                        have p3550_2 := h3550c.2.2.1
                                        have p3550_3 := h3550c.2.2.2
                                        rcases p3550_3 (m.d 0 1) (by simp) with h3576 | h3576
                                        · linarith only [h3283, h3576, hlam]
                                        · linarith only [h0, h3576, hlam]
                                      · have p3550_0 := h3550c.1
                                        have p3550_1 := h3550c.2.1
                                        have p3550_2 := h3550c.2.2.1
                                        have p3550_3 := h3550c.2.2.2
                                        rcases p3550_3 (m.d 0 1) (by simp) with h3579 | h3579
                                        · linarith only [h3283, h3579, hlam]
                                        · linarith only [h1, h3579, hlam]
                                      · have p3550_0 := h3550c.1
                                        have p3550_1 := h3550c.2.1
                                        have p3550_2 := h3550c.2.2.1
                                        have p3550_3 := h3550c.2.2.2
                                        linarith only [h3532, hlam, p3550_1]
                                      · have p3550_0 := h3550c.1
                                        have p3550_1 := h3550c.2.1
                                        have p3550_2 := h3550c.2.2.1
                                        have p3550_3 := h3550c.2.2.2
                                        linarith only [hlam, p3550_0]
                                    · linarith only [h1, h2, h3532, h3533, h3535, h3544, h3549, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                                  · linarith only [h2, h3532, h3535, h3548, hlam]
                            · linarith only [h2, h3532, h3543, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3587 | h3587
                  · linarith only [h0, h3502, h3587, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3589 | h3589
                    · linarith only [h0, h2, h3532, h3589, hc24, hc45, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3591 | h3591
                      · linarith only [h1, h3283, h3526, h3587, h3591, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3593 | h3593
                        · linarith only [h1, h3502, h3528, h3593, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3595 | h3595
                          · linarith only [h1, h3530, h3595, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3597 | h3597
                            · linarith only [h0, h2, h3532, h3593, h3597, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h1, h2, h3587, h3597, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 9218000 in
set_option maxHeartbeats 9218000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s1 m hb0 hb2 hb3 hb5 h0 h1

end R2N4
