import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_38S2
import Jsp000404.R1LeavesN7_38S3
import Jsp000404.R1LeavesN7_38S4

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7280000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x1_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1750 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2167 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2337 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2650 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h3270 | h3270
  · rcases m.htr 0 2 5 (by decide) (by decide) with h3271 | h3271
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3272 | h3272
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3273 | h3273
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3274 | h3274
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3275 | h3275
            · linarith only [h2650, h3270, h3274, h3275, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3277 | h3277
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3278 | h3278
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3279 | h3279
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3280 | h3280
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3281 | h3281
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3282 | h3282
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3283 | h3283
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3284 | h3284
                            · linarith only [h2650, h3270, h3284, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3286 | h3286
                              · linarith only [h3282, h3284, h3286, hlam]
                              · rcases h2bigk with h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c | h3288c
                                · have p3288_0 := h3288c.1
                                  have p3288_1 := h3288c.2.1
                                  have p3288_2 := h3288c.2.2.1
                                  have p3288_3 := h3288c.2.2.2
                                  linarith only [hlam, p3288_0]
                                · have p3288_0 := h3288c.1
                                  have p3288_1 := h3288c.2.1
                                  have p3288_2 := h3288c.2.2.1
                                  have p3288_3 := h3288c.2.2.2
                                  linarith only [h0, hlam, p3288_1]
                                · have p3288_0 := h3288c.1
                                  have p3288_1 := h3288c.2.1
                                  have p3288_2 := h3288c.2.2.1
                                  have p3288_3 := h3288c.2.2.2
                                  linarith only [h2650, hlam, p3288_0]
                                · have p3288_0 := h3288c.1
                                  have p3288_1 := h3288c.2.1
                                  have p3288_2 := h3288c.2.2.1
                                  have p3288_3 := h3288c.2.2.2
                                  rcases p3288_3 (m.d 0 2) (by simp) with h3292 | h3292
                                  · rcases p3288_3 (m.d 1 2) (by simp) with h3293 | h3293
                                    · rcases p3288_3 (m.d 2 3) (by simp) with h3294 | h3294
                                      · rcases p3288_3 (m.d 2 4) (by simp) with h3295 | h3295
                                        · linarith only [h3295, hlam, p3288_0]
                                        · rcases p3288_3 (m.d 2 5) (by simp) with h3297 | h3297
                                          · linarith only [h3271, h3297, hlam]
                                          · linarith only [h3284, h3297, hlam]
                                      · linarith only [h3282, h3294, hlam]
                                    · linarith only [h3277, h3293, hlam]
                                  · linarith only [h3292, hlam, p3288_0]
                                · have p3288_0 := h3288c.1
                                  have p3288_1 := h3288c.2.1
                                  have p3288_2 := h3288c.2.2.1
                                  have p3288_3 := h3288c.2.2.2
                                  linarith only [h0, h3275, h3283, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3288_1, u5ehi8]
                                · have p3288_0 := h3288c.1
                                  have p3288_1 := h3288c.2.1
                                  have p3288_2 := h3288c.2.2.1
                                  have p3288_3 := h3288c.2.2.2
                                  linarith only [h3275, hc02, hc23, hlam, hphi, p3288_1]
                                · have p3288_0 := h3288c.1
                                  have p3288_1 := h3288c.2.1
                                  have p3288_2 := h3288c.2.2.1
                                  have p3288_3 := h3288c.2.2.2
                                  linarith only [hlam, p3288_0]
                                · have p3288_0 := h3288c.1
                                  have p3288_1 := h3288c.2.1
                                  have p3288_2 := h3288c.2.2.1
                                  have p3288_3 := h3288c.2.2.2
                                  linarith only [h3275, hlam, p3288_0]
                                · have p3288_0 := h3288c.1
                                  have p3288_1 := h3288c.2.1
                                  have p3288_2 := h3288c.2.2.1
                                  have p3288_3 := h3288c.2.2.2
                                  rcases p3288_3 (m.d 0 2) (by simp) with h3307 | h3307
                                  · linarith only [h0, h3307, hlam]
                                  · linarith only [h3270, h3307, hlam]
                                · have p3288_0 := h3288c.1
                                  have p3288_1 := h3288c.2.1
                                  have p3288_2 := h3288c.2.2.1
                                  have p3288_3 := h3288c.2.2.2
                                  linarith only [h3275, h3283, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3288_1, u5ehi8]
                                · have p3288_0 := h3288c.1
                                  have p3288_1 := h3288c.2.1
                                  have p3288_2 := h3288c.2.2.1
                                  have p3288_3 := h3288c.2.2.2
                                  linarith only [h3270, h3274, h3282, h3284, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3288_1]
                                · have p3288_0 := h3288c.1
                                  have p3288_1 := h3288c.2.1
                                  have p3288_2 := h3288c.2.2.1
                                  have p3288_3 := h3288c.2.2.2
                                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p3288_1]
                                · have p3288_0 := h3288c.1
                                  have p3288_1 := h3288c.2.1
                                  have p3288_2 := h3288c.2.2.1
                                  have p3288_3 := h3288c.2.2.2
                                  linarith only [hlam, p3288_0]
                                · have p3288_0 := h3288c.1
                                  have p3288_1 := h3288c.2.1
                                  have p3288_2 := h3288c.2.2.1
                                  have p3288_3 := h3288c.2.2.2
                                  linarith only [h2650, h3270, h3274, h3284, hlam, p3288_2]
                                · have p3288_0 := h3288c.1
                                  have p3288_1 := h3288c.2.1
                                  have p3288_2 := h3288c.2.2.1
                                  have p3288_3 := h3288c.2.2.2
                                  rcases p3288_3 (m.d 0 2) (by simp) with h3315 | h3315
                                  · linarith only [h2650, h3315, hlam]
                                  · linarith only [h3271, h3315, hlam]
                                · have p3288_0 := h3288c.1
                                  have p3288_1 := h3288c.2.1
                                  have p3288_2 := h3288c.2.2.1
                                  have p3288_3 := h3288c.2.2.2
                                  linarith only [h3270, hlam, p3288_0]
                                · have p3288_0 := h3288c.1
                                  have p3288_1 := h3288c.2.1
                                  have p3288_2 := h3288c.2.2.1
                                  have p3288_3 := h3288c.2.2.2
                                  linarith only [h3277, hlam, p3288_0]
                                · have p3288_0 := h3288c.1
                                  have p3288_1 := h3288c.2.1
                                  have p3288_2 := h3288c.2.2.1
                                  have p3288_3 := h3288c.2.2.2
                                  linarith only [h3282, hlam, p3288_1]
                                · have p3288_0 := h3288c.1
                                  have p3288_1 := h3288c.2.1
                                  have p3288_2 := h3288c.2.2.1
                                  have p3288_3 := h3288c.2.2.2
                                  linarith only [hlam, p3288_0]
                                · have p3288_0 := h3288c.1
                                  have p3288_1 := h3288c.2.1
                                  have p3288_2 := h3288c.2.2.1
                                  have p3288_3 := h3288c.2.2.2
                                  linarith only [h3284, hlam, p3288_1]
                                · have p3288_0 := h3288c.1
                                  have p3288_1 := h3288c.2.1
                                  have p3288_2 := h3288c.2.2.1
                                  have p3288_3 := h3288c.2.2.2
                                  linarith only [h3271, hlam, p3288_0]
                                · have p3288_0 := h3288c.1
                                  have p3288_1 := h3288c.2.1
                                  have p3288_2 := h3288c.2.2.1
                                  have p3288_3 := h3288c.2.2.2
                                  linarith only [h3278, hlam, p3288_0]
                                · have p3288_0 := h3288c.1
                                  have p3288_1 := h3288c.2.1
                                  have p3288_2 := h3288c.2.2.1
                                  have p3288_3 := h3288c.2.2.2
                                  linarith only [h3283, hlam, p3288_1]
                                · have p3288_0 := h3288c.1
                                  have p3288_1 := h3288c.2.1
                                  have p3288_2 := h3288c.2.2.1
                                  have p3288_3 := h3288c.2.2.2
                                  linarith only [h3282, hc34, hlam, hphi, ht45, p3288_1, u5elo2]
                                · have p3288_0 := h3288c.1
                                  have p3288_1 := h3288c.2.1
                                  have p3288_2 := h3288c.2.2.1
                                  have p3288_3 := h3288c.2.2.2
                                  linarith only [hlam, p3288_0]
                          · linarith only [h0, h3270, h3274, h3275, h3283, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
                        · linarith only [h0, h3270, h3274, h3275, h3282, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
                      · linarith only [h0, h2167, h3270, h3274, h3281, hc01, hc12, hlam, hphi]
                    · linarith only [h1750, h2650, h3270, h3273, h3274, h3280, hlam, hphi, u5ehi9, u5elo0]
                  · linarith only [h1750, h3272, h3279, hlam]
                · linarith only [h0, h3278, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h3270, h3277, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3335 | h3335
            · linarith only [h2650, h3271, h3335, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3337 | h3337
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3338 | h3338
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3339 | h3339
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3340 | h3340
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3341 | h3341
                      · linarith only [h2167, h3274, h3335, h3337, h3341, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h2167, h3341, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                    · linarith only [h0, h3335, h3340, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                  · linarith only [h1750, h3272, h3339, hlam]
                · linarith only [h0, h3271, h3338, hlam]
              · linarith only [h0, h3270, h3337, hlam]
        · linarith only [h2650, h3271, h3273, hlam, hphi, u5ehi7, u5elo3]
      · linarith only [h2650, h3270, h3272, hlam]
    · linarith only [h3270, h3271, hc24, hlam, hphi, ht45, u5elo2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h3351 | h3351
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3352 | h3352
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3353 | h3353
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3354 | h3354
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3355 | h3355
            · linarith only [h2650, h3351, h3355, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3357 | h3357
              · linarith only [h3270, h3351, h3357, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3359 | h3359
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3360 | h3360
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3361 | h3361
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3362 | h3362
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3363 | h3363
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3364 | h3364
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3365 | h3365
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3366 | h3366
                              · rcases h2bigk with h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c
                                · have p3367_0 := h3367c.1
                                  have p3367_1 := h3367c.2.1
                                  have p3367_2 := h3367c.2.2.1
                                  have p3367_3 := h3367c.2.2.2
                                  linarith only [hlam, p3367_0]
                                · have p3367_0 := h3367c.1
                                  have p3367_1 := h3367c.2.1
                                  have p3367_2 := h3367c.2.2.1
                                  have p3367_3 := h3367c.2.2.2
                                  linarith only [h0, hlam, p3367_1]
                                · have p3367_0 := h3367c.1
                                  have p3367_1 := h3367c.2.1
                                  have p3367_2 := h3367c.2.2.1
                                  have p3367_3 := h3367c.2.2.2
                                  linarith only [h2650, hlam, p3367_0]
                                · have p3367_0 := h3367c.1
                                  have p3367_1 := h3367c.2.1
                                  have p3367_2 := h3367c.2.2.1
                                  have p3367_3 := h3367c.2.2.2
                                  linarith only [h3270, hlam, p3367_0]
                                · have p3367_0 := h3367c.1
                                  have p3367_1 := h3367c.2.1
                                  have p3367_2 := h3367c.2.2.1
                                  have p3367_3 := h3367c.2.2.2
                                  linarith only [h0, h3357, h3363, h3364, h3366, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3367_1, u5ehi9]
                                · have p3367_0 := h3367c.1
                                  have p3367_1 := h3367c.2.1
                                  have p3367_2 := h3367c.2.2.1
                                  have p3367_3 := h3367c.2.2.2
                                  linarith only [h3357, h3363, hc02, hc23, hlam, hphi, p3367_1]
                                · have p3367_0 := h3367c.1
                                  have p3367_1 := h3367c.2.1
                                  have p3367_2 := h3367c.2.2.1
                                  have p3367_3 := h3367c.2.2.2
                                  linarith only [hlam, p3367_0]
                                · have p3367_0 := h3367c.1
                                  have p3367_1 := h3367c.2.1
                                  have p3367_2 := h3367c.2.2.1
                                  have p3367_3 := h3367c.2.2.2
                                  linarith only [h3355, hlam, p3367_0]
                                · have p3367_0 := h3367c.1
                                  have p3367_1 := h3367c.2.1
                                  have p3367_2 := h3367c.2.2.1
                                  have p3367_3 := h3367c.2.2.2
                                  linarith only [h3357, hlam, p3367_0]
                                · have p3367_0 := h3367c.1
                                  have p3367_1 := h3367c.2.1
                                  have p3367_2 := h3367c.2.2.1
                                  have p3367_3 := h3367c.2.2.2
                                  linarith only [h3357, h3363, h3364, h3366, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3367_1, u5ehi9]
                                · have p3367_0 := h3367c.1
                                  have p3367_1 := h3367c.2.1
                                  have p3367_2 := h3367c.2.2.1
                                  have p3367_3 := h3367c.2.2.2
                                  linarith only [h3351, h3364, h3366, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3367_1, u5ehi9]
                                · have p3367_0 := h3367c.1
                                  have p3367_1 := h3367c.2.1
                                  have p3367_2 := h3367c.2.2.1
                                  have p3367_3 := h3367c.2.2.2
                                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p3367_1]
                                · have p3367_0 := h3367c.1
                                  have p3367_1 := h3367c.2.1
                                  have p3367_2 := h3367c.2.2.1
                                  have p3367_3 := h3367c.2.2.2
                                  linarith only [hlam, p3367_0]
                                · have p3367_0 := h3367c.1
                                  have p3367_1 := h3367c.2.1
                                  have p3367_2 := h3367c.2.2.1
                                  have p3367_3 := h3367c.2.2.2
                                  linarith only [h3270, h3351, h3364, h3366, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3367_1, u5ehi9]
                                · have p3367_0 := h3367c.1
                                  have p3367_1 := h3367c.2.1
                                  have p3367_2 := h3367c.2.2.1
                                  have p3367_3 := h3367c.2.2.2
                                  rcases p3367_3 (m.d 0 2) (by simp) with h3382 | h3382
                                  · linarith only [h2650, h3382, hlam]
                                  · linarith only [h3351, h3382, hlam]
                                · have p3367_0 := h3367c.1
                                  have p3367_1 := h3367c.2.1
                                  have p3367_2 := h3367c.2.2.1
                                  have p3367_3 := h3367c.2.2.2
                                  linarith only [h3351, h3364, h3366, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p3367_1, u5ehi9]
                                · have p3367_0 := h3367c.1
                                  have p3367_1 := h3367c.2.1
                                  have p3367_2 := h3367c.2.2.1
                                  have p3367_3 := h3367c.2.2.2
                                  linarith only [h0, h3351, h3364, h3366, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p3367_1, u5ehi9]
                                · have p3367_0 := h3367c.1
                                  have p3367_1 := h3367c.2.1
                                  have p3367_2 := h3367c.2.2.1
                                  have p3367_3 := h3367c.2.2.2
                                  linarith only [h3363, hlam, p3367_1]
                                · have p3367_0 := h3367c.1
                                  have p3367_1 := h3367c.2.1
                                  have p3367_2 := h3367c.2.2.1
                                  have p3367_3 := h3367c.2.2.2
                                  linarith only [hlam, p3367_0]
                                · have p3367_0 := h3367c.1
                                  have p3367_1 := h3367c.2.1
                                  have p3367_2 := h3367c.2.2.1
                                  have p3367_3 := h3367c.2.2.2
                                  rcases p3367_3 (m.d 0 2) (by simp) with h3389 | h3389
                                  · linarith only [h3270, h3389, hlam]
                                  · linarith only [h3351, h3389, hlam]
                                · have p3367_0 := h3367c.1
                                  have p3367_1 := h3367c.2.1
                                  have p3367_2 := h3367c.2.2.1
                                  have p3367_3 := h3367c.2.2.2
                                  linarith only [h3351, hlam, p3367_0]
                                · have p3367_0 := h3367c.1
                                  have p3367_1 := h3367c.2.1
                                  have p3367_2 := h3367c.2.2.1
                                  have p3367_3 := h3367c.2.2.2
                                  linarith only [h3359, hlam, p3367_0]
                                · have p3367_0 := h3367c.1
                                  have p3367_1 := h3367c.2.1
                                  have p3367_2 := h3367c.2.2.1
                                  have p3367_3 := h3367c.2.2.2
                                  linarith only [h3364, hlam, p3367_1]
                                · have p3367_0 := h3367c.1
                                  have p3367_1 := h3367c.2.1
                                  have p3367_2 := h3367c.2.2.1
                                  have p3367_3 := h3367c.2.2.2
                                  linarith only [h3365, hlam, p3367_0]
                                · have p3367_0 := h3367c.1
                                  have p3367_1 := h3367c.2.1
                                  have p3367_2 := h3367c.2.2.1
                                  have p3367_3 := h3367c.2.2.2
                                  linarith only [hlam, p3367_0]
                              · rcases h2bigk with h3397c | h3397c | h3397c | h3397c | h3397c | h3397c | h3397c | h3397c | h3397c | h3397c | h3397c | h3397c | h3397c | h3397c | h3397c | h3397c | h3397c | h3397c | h3397c | h3397c | h3397c | h3397c | h3397c | h3397c | h3397c
                                · have p3397_0 := h3397c.1
                                  have p3397_1 := h3397c.2.1
                                  have p3397_2 := h3397c.2.2.1
                                  have p3397_3 := h3397c.2.2.2
                                  linarith only [hlam, p3397_0]
                                · have p3397_0 := h3397c.1
                                  have p3397_1 := h3397c.2.1
                                  have p3397_2 := h3397c.2.2.1
                                  have p3397_3 := h3397c.2.2.2
                                  linarith only [h0, hlam, p3397_1]
                                · have p3397_0 := h3397c.1
                                  have p3397_1 := h3397c.2.1
                                  have p3397_2 := h3397c.2.2.1
                                  have p3397_3 := h3397c.2.2.2
                                  linarith only [h2650, hlam, p3397_0]
                                · have p3397_0 := h3397c.1
                                  have p3397_1 := h3397c.2.1
                                  have p3397_2 := h3397c.2.2.1
                                  have p3397_3 := h3397c.2.2.2
                                  linarith only [h3270, hlam, p3397_0]
                                · have p3397_0 := h3397c.1
                                  have p3397_1 := h3397c.2.1
                                  have p3397_2 := h3397c.2.2.1
                                  have p3397_3 := h3397c.2.2.2
                                  linarith only [h2650, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3397_1, u5ehi7]
                                · have p3397_0 := h3397c.1
                                  have p3397_1 := h3397c.2.1
                                  have p3397_2 := h3397c.2.2.1
                                  have p3397_3 := h3397c.2.2.2
                                  linarith only [h3351, h3357, h3365, h3366, hc14, hlam, hphi, ht01, ht0b, ht5b, p3397_1, u5ehi8]
                                · have p3397_0 := h3397c.1
                                  have p3397_1 := h3397c.2.1
                                  have p3397_2 := h3397c.2.2.1
                                  have p3397_3 := h3397c.2.2.2
                                  linarith only [hlam, p3397_0]
                                · have p3397_0 := h3397c.1
                                  have p3397_1 := h3397c.2.1
                                  have p3397_2 := h3397c.2.2.1
                                  have p3397_3 := h3397c.2.2.2
                                  linarith only [h3355, hlam, p3397_0]
                                · have p3397_0 := h3397c.1
                                  have p3397_1 := h3397c.2.1
                                  have p3397_2 := h3397c.2.2.1
                                  have p3397_3 := h3397c.2.2.2
                                  linarith only [h3357, hlam, p3397_0]
                                · have p3397_0 := h3397c.1
                                  have p3397_1 := h3397c.2.1
                                  have p3397_2 := h3397c.2.2.1
                                  have p3397_3 := h3397c.2.2.2
                                  linarith only [h3357, h3363, h3365, h3366, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3397_1, u5ehi8]
                                · have p3397_0 := h3397c.1
                                  have p3397_1 := h3397c.2.1
                                  have p3397_2 := h3397c.2.2.1
                                  have p3397_3 := h3397c.2.2.2
                                  linarith only [h3351, h3365, h3366, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3397_1, u5ehi8]
                                · have p3397_0 := h3397c.1
                                  have p3397_1 := h3397c.2.1
                                  have p3397_2 := h3397c.2.2.1
                                  have p3397_3 := h3397c.2.2.2
                                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p3397_1]
                                · have p3397_0 := h3397c.1
                                  have p3397_1 := h3397c.2.1
                                  have p3397_2 := h3397c.2.2.1
                                  have p3397_3 := h3397c.2.2.2
                                  linarith only [hlam, p3397_0]
                                · have p3397_0 := h3397c.1
                                  have p3397_1 := h3397c.2.1
                                  have p3397_2 := h3397c.2.2.1
                                  have p3397_3 := h3397c.2.2.2
                                  linarith only [h2167, h3357, hc01, hc23, hlam, hphi, ht12, p3397_1]
                                · have p3397_0 := h3397c.1
                                  have p3397_1 := h3397c.2.1
                                  have p3397_2 := h3397c.2.2.1
                                  have p3397_3 := h3397c.2.2.2
                                  rcases p3397_3 (m.d 0 2) (by simp) with h3412 | h3412
                                  · linarith only [h2650, h3412, hlam]
                                  · linarith only [h3351, h3412, hlam]
                                · have p3397_0 := h3397c.1
                                  have p3397_1 := h3397c.2.1
                                  have p3397_2 := h3397c.2.2.1
                                  have p3397_3 := h3397c.2.2.2
                                  linarith only [h3351, h3365, h3366, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p3397_1, u5ehi8]
                                · have p3397_0 := h3397c.1
                                  have p3397_1 := h3397c.2.1
                                  have p3397_2 := h3397c.2.2.1
                                  have p3397_3 := h3397c.2.2.2
                                  linarith only [h0, h3351, h3365, h3366, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p3397_1, u5ehi8]
                                · have p3397_0 := h3397c.1
                                  have p3397_1 := h3397c.2.1
                                  have p3397_2 := h3397c.2.2.1
                                  have p3397_3 := h3397c.2.2.2
                                  linarith only [h3363, hlam, p3397_1]
                                · have p3397_0 := h3397c.1
                                  have p3397_1 := h3397c.2.1
                                  have p3397_2 := h3397c.2.2.1
                                  have p3397_3 := h3397c.2.2.2
                                  linarith only [hlam, p3397_0]
                                · have p3397_0 := h3397c.1
                                  have p3397_1 := h3397c.2.1
                                  have p3397_2 := h3397c.2.2.1
                                  have p3397_3 := h3397c.2.2.2
                                  rcases p3397_3 (m.d 0 2) (by simp) with h3419 | h3419
                                  · linarith only [h3270, h3419, hlam]
                                  · linarith only [h3351, h3419, hlam]
                                · have p3397_0 := h3397c.1
                                  have p3397_1 := h3397c.2.1
                                  have p3397_2 := h3397c.2.2.1
                                  have p3397_3 := h3397c.2.2.2
                                  linarith only [h3351, hlam, p3397_0]
                                · have p3397_0 := h3397c.1
                                  have p3397_1 := h3397c.2.1
                                  have p3397_2 := h3397c.2.2.1
                                  have p3397_3 := h3397c.2.2.2
                                  linarith only [h3359, hlam, p3397_0]
                                · have p3397_0 := h3397c.1
                                  have p3397_1 := h3397c.2.1
                                  have p3397_2 := h3397c.2.2.1
                                  have p3397_3 := h3397c.2.2.2
                                  linarith only [h3364, hlam, p3397_1]
                                · have p3397_0 := h3397c.1
                                  have p3397_1 := h3397c.2.1
                                  have p3397_2 := h3397c.2.2.1
                                  have p3397_3 := h3397c.2.2.2
                                  linarith only [h3365, hlam, p3397_0]
                                · have p3397_0 := h3397c.1
                                  have p3397_1 := h3397c.2.1
                                  have p3397_2 := h3397c.2.2.1
                                  have p3397_3 := h3397c.2.2.2
                                  linarith only [hlam, p3397_0]
                            · linarith only [h3270, h3351, h3365, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi7]
                          · linarith only [h1750, h3355, h3364, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                        · linarith only [h0, h3351, h3355, h3363, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                      · linarith only [h2167, h3354, h3362, hlam]
                    · linarith only [h1750, h3353, h3361, hlam]
                  · linarith only [h1750, h3352, h3360, hlam]
                · linarith only [h0, h3351, h3359, hlam]
          · linarith only [h3270, h3351, h3354, hlam, hphi, u5ehi7, u5elo4]
        · linarith only [h3270, h3351, h3352, h3353, hlam, hphi, u5ehi7, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3436 | h3436
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3437 | h3437
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3438 | h3438
            · linarith only [h2650, h3351, h3438, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3440 | h3440
              · linarith only [h3270, h3351, h3440, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3442 | h3442
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3443 | h3443
                  · linarith only [h3352, h3436, h3443, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3445 | h3445
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3446 | h3446
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3447 | h3447
                        · linarith only [h0, h3438, h3443, h3447, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h2650, h3351, h3447, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                      · linarith only [h0, h3351, h3437, h3438, h3443, h3446, hc04, hlam, hphi, ht0b, ht5b, u5ehi7]
                    · linarith only [h0, h3351, h3438, h3445, hlam, hphi, u5ehi7, u5elo3]
                · linarith only [h0, h3351, h3442, hlam]
          · linarith only [h3270, h3351, h3437, hlam, hphi, u5ehi7, u5elo4]
        · linarith only [h2650, h3351, h3436, hlam, hphi, u5ehi7, u5elo3]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3455 | h3455
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3456 | h3456
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3457 | h3457
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3458 | h3458
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3459 | h3459
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3460 | h3460
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3461 | h3461
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3462 | h3462
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3463 | h3463
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3464 | h3464
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3465 | h3465
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3466 | h3466
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3467 | h3467
                              · linarith only [h2650, h3455, h3458, h3467, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                              · rcases h2bigk with h3469c | h3469c | h3469c | h3469c | h3469c | h3469c | h3469c | h3469c | h3469c | h3469c | h3469c | h3469c | h3469c | h3469c | h3469c | h3469c | h3469c | h3469c | h3469c | h3469c | h3469c | h3469c | h3469c | h3469c | h3469c
                                · have p3469_0 := h3469c.1
                                  have p3469_1 := h3469c.2.1
                                  have p3469_2 := h3469c.2.2.1
                                  have p3469_3 := h3469c.2.2.2
                                  linarith only [hlam, p3469_0]
                                · have p3469_0 := h3469c.1
                                  have p3469_1 := h3469c.2.1
                                  have p3469_2 := h3469c.2.2.1
                                  have p3469_3 := h3469c.2.2.2
                                  linarith only [h0, hlam, p3469_1]
                                · have p3469_0 := h3469c.1
                                  have p3469_1 := h3469c.2.1
                                  have p3469_2 := h3469c.2.2.1
                                  have p3469_3 := h3469c.2.2.2
                                  linarith only [h2650, hlam, p3469_0]
                                · have p3469_0 := h3469c.1
                                  have p3469_1 := h3469c.2.1
                                  have p3469_2 := h3469c.2.2.1
                                  have p3469_3 := h3469c.2.2.2
                                  linarith only [h3270, hlam, p3469_0]
                                · have p3469_0 := h3469c.1
                                  have p3469_1 := h3469c.2.1
                                  have p3469_2 := h3469c.2.2.1
                                  have p3469_3 := h3469c.2.2.2
                                  linarith only [h3351, hlam, p3469_0]
                                · have p3469_0 := h3469c.1
                                  have p3469_1 := h3469c.2.1
                                  have p3469_2 := h3469c.2.2.1
                                  have p3469_3 := h3469c.2.2.2
                                  rcases p3469_3 (m.d 0 2) (by simp) with h3475 | h3475
                                  · linarith only [h0, h3475, hlam]
                                  · rcases p3469_3 (m.d 1 2) (by simp) with h3477 | h3477
                                    · rcases p3469_3 (m.d 2 3) (by simp) with h3478 | h3478
                                      · linarith only [h3458, h3478, hlam]
                                      · linarith only [h2650, h3478, hlam]
                                    · linarith only [h0, h3477, hlam]
                                · have p3469_0 := h3469c.1
                                  have p3469_1 := h3469c.2.1
                                  have p3469_2 := h3469c.2.2.1
                                  have p3469_3 := h3469c.2.2.2
                                  linarith only [hlam, p3469_0]
                                · have p3469_0 := h3469c.1
                                  have p3469_1 := h3469c.2.1
                                  have p3469_2 := h3469c.2.2.1
                                  have p3469_3 := h3469c.2.2.2
                                  linarith only [h0, h2650, hc01, hc12, hlam, hphi, p3469_1]
                                · have p3469_0 := h3469c.1
                                  have p3469_1 := h3469c.2.1
                                  have p3469_2 := h3469c.2.2.1
                                  have p3469_3 := h3469c.2.2.2
                                  linarith only [h0, h3270, h3351, h3457, h3460, h3467, hc01, hc12, hc34, hlam, hphi, ht45, p3469_1, u5elo1]
                                · have p3469_0 := h3469c.1
                                  have p3469_1 := h3469c.2.1
                                  have p3469_2 := h3469c.2.2.1
                                  have p3469_3 := h3469c.2.2.2
                                  linarith only [h0, h3351, hc01, hc12, hlam, hphi, p3469_1]
                                · have p3469_0 := h3469c.1
                                  have p3469_1 := h3469c.2.1
                                  have p3469_2 := h3469c.2.2.1
                                  have p3469_3 := h3469c.2.2.2
                                  linarith only [h0, h3458, hc01, hc12, hlam, hphi, p3469_1]
                                · have p3469_0 := h3469c.1
                                  have p3469_1 := h3469c.2.1
                                  have p3469_2 := h3469c.2.2.1
                                  have p3469_3 := h3469c.2.2.2
                                  linarith only [h3458, hlam, p3469_0]
                                · have p3469_0 := h3469c.1
                                  have p3469_1 := h3469c.2.1
                                  have p3469_2 := h3469c.2.2.1
                                  have p3469_3 := h3469c.2.2.2
                                  linarith only [hlam, p3469_0]
                                · have p3469_0 := h3469c.1
                                  have p3469_1 := h3469c.2.1
                                  have p3469_2 := h3469c.2.2.1
                                  have p3469_3 := h3469c.2.2.2
                                  linarith only [h0, h3270, h3351, h3457, h3458, h3460, h3467, hc01, hc12, hc34, hlam, hphi, ht45, p3469_1, u5elo1]
                                · have p3469_0 := h3469c.1
                                  have p3469_1 := h3469c.2.1
                                  have p3469_2 := h3469c.2.2.1
                                  have p3469_3 := h3469c.2.2.2
                                  linarith only [h0, h3351, h3458, hc01, hc12, hlam, hphi, p3469_1]
                                · have p3469_0 := h3469c.1
                                  have p3469_1 := h3469c.2.1
                                  have p3469_2 := h3469c.2.2.1
                                  have p3469_3 := h3469c.2.2.2
                                  linarith only [h0, h3459, hc01, hc12, hlam, hphi, p3469_1]
                                · have p3469_0 := h3469c.1
                                  have p3469_1 := h3469c.2.1
                                  have p3469_2 := h3469c.2.2.1
                                  have p3469_3 := h3469c.2.2.2
                                  linarith only [h3459, hlam, p3469_0]
                                · have p3469_0 := h3469c.1
                                  have p3469_1 := h3469c.2.1
                                  have p3469_2 := h3469c.2.2.1
                                  have p3469_3 := h3469c.2.2.2
                                  linarith only [h3464, hlam, p3469_1]
                                · have p3469_0 := h3469c.1
                                  have p3469_1 := h3469c.2.1
                                  have p3469_2 := h3469c.2.2.1
                                  have p3469_3 := h3469c.2.2.2
                                  linarith only [hlam, p3469_0]
                                · have p3469_0 := h3469c.1
                                  have p3469_1 := h3469c.2.1
                                  have p3469_2 := h3469c.2.2.1
                                  have p3469_3 := h3469c.2.2.2
                                  linarith only [h0, h3351, h3458, h3464, hc01, hc12, hlam, hphi, p3469_1]
                                · have p3469_0 := h3469c.1
                                  have p3469_1 := h3469c.2.1
                                  have p3469_2 := h3469c.2.2.1
                                  have p3469_3 := h3469c.2.2.2
                                  linarith only [h0, h3460, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p3469_1, u5elo1]
                                · have p3469_0 := h3469c.1
                                  have p3469_1 := h3469c.2.1
                                  have p3469_2 := h3469c.2.2.1
                                  have p3469_3 := h3469c.2.2.2
                                  linarith only [h3460, hlam, p3469_0]
                                · have p3469_0 := h3469c.1
                                  have p3469_1 := h3469c.2.1
                                  have p3469_2 := h3469c.2.2.1
                                  have p3469_3 := h3469c.2.2.2
                                  linarith only [h3465, hlam, p3469_1]
                                · have p3469_0 := h3469c.1
                                  have p3469_1 := h3469c.2.1
                                  have p3469_2 := h3469c.2.2.1
                                  have p3469_3 := h3469c.2.2.2
                                  linarith only [h3466, hlam, p3469_0]
                                · have p3469_0 := h3469c.1
                                  have p3469_1 := h3469c.2.1
                                  have p3469_2 := h3469c.2.2.1
                                  have p3469_3 := h3469c.2.2.2
                                  linarith only [hlam, p3469_0]
                            · linarith only [h3270, h3457, h3466, hlam]
                          · linarith only [h3270, h3457, h3464, h3465, hlam, hphi, u5ehi9, u5elo3]
                        · linarith only [h2650, h3455, h3464, hlam]
                      · linarith only [h2167, h3270, h3457, h3463, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h2650, h3456, h3458, h3462, hlam]
                  · linarith only [h2650, h3455, h3458, h3461, hlam]
                · linarith only [h2650, h3456, h3458, h3460, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
              · linarith only [h2650, h3455, h3457, h3458, h3459, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3509 | h3509
              · linarith only [h0, h3270, h3458, h3509, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3511 | h3511
                · linarith only [h0, h3351, h3458, h3511, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h3511, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3514 | h3514
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3515 | h3515
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3516 | h3516
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3517 | h3517
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3518 | h3518
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3519 | h3519
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3520 | h3520
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3521 | h3521
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3522 | h3522
                            · linarith only [h2167, h3457, h3515, h3522, hc01, hc12, hlam, hphi]
                            · linarith only [h0, h3270, h3519, h3522, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
                          · linarith only [h0, h2650, h3521, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                        · linarith only [h2650, h3455, h3457, h3519, h3520, hc03, hlam, hphi, ht34, ht45, u5elo1]
                      · linarith only [h2167, h3519, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                    · linarith only [h1750, h2650, h3456, h3518, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h2650, h3455, h3457, h3514, h3517, hc03, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h0, h3516, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h2650, h3456, h3514, h3515, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3532 | h3532
              · linarith only [h0, h3270, h3514, h3532, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3534 | h3534
                · linarith only [h0, h3351, h3514, h3534, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h3534, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
        · linarith only [h3455, h3456, hc34, hlam, hphi, ht45, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3538 | h3538
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3539 | h3539
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3540 | h3540
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3541 | h3541
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3542 | h3542
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3543 | h3543
                  · linarith only [h3455, h3538, h3543, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3545 | h3545
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3546 | h3546
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3547 | h3547
                        · linarith only [h3540, h3543, h3547, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3549 | h3549
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3550 | h3550
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3551 | h3551
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
                                  linarith only [h2650, hlam, p3552_0]
                                · have p3552_0 := h3552c.1
                                  have p3552_1 := h3552c.2.1
                                  have p3552_2 := h3552c.2.2.1
                                  have p3552_3 := h3552c.2.2.2
                                  linarith only [h3270, hlam, p3552_0]
                                · have p3552_0 := h3552c.1
                                  have p3552_1 := h3552c.2.1
                                  have p3552_2 := h3552c.2.2.1
                                  have p3552_3 := h3552c.2.2.2
                                  linarith only [h3351, hlam, p3552_0]
                                · have p3552_0 := h3552c.1
                                  have p3552_1 := h3552c.2.1
                                  have p3552_2 := h3552c.2.2.1
                                  have p3552_3 := h3552c.2.2.2
                                  rcases p3552_3 (m.d 0 2) (by simp) with h3558 | h3558
                                  · linarith only [h0, h3558, hlam]
                                  · rcases p3552_3 (m.d 1 2) (by simp) with h3560 | h3560
                                    · rcases p3552_3 (m.d 2 3) (by simp) with h3561 | h3561
                                      · linarith only [h3540, h3561, hlam]
                                      · linarith only [h2650, h3561, hlam]
                                    · linarith only [h0, h3560, hlam]
                                · have p3552_0 := h3552c.1
                                  have p3552_1 := h3552c.2.1
                                  have p3552_2 := h3552c.2.2.1
                                  have p3552_3 := h3552c.2.2.2
                                  linarith only [hlam, p3552_0]
                                · have p3552_0 := h3552c.1
                                  have p3552_1 := h3552c.2.1
                                  have p3552_2 := h3552c.2.2.1
                                  have p3552_3 := h3552c.2.2.2
                                  linarith only [h0, h2650, h3351, h3538, h3542, h3551, hc01, hc12, hlam, hphi, p3552_1, u5ehi9, u5elo1]
                                · have p3552_0 := h3552c.1
                                  have p3552_1 := h3552c.2.1
                                  have p3552_2 := h3552c.2.2.1
                                  have p3552_3 := h3552c.2.2.2
                                  linarith only [h0, h3270, h3351, h3455, h3538, h3542, h3551, hc01, hc12, hlam, hphi, p3552_1, u5ehi9, u5elo1]
                                · have p3552_0 := h3552c.1
                                  have p3552_1 := h3552c.2.1
                                  have p3552_2 := h3552c.2.2.1
                                  have p3552_3 := h3552c.2.2.2
                                  linarith only [h0, h3351, hc01, hc12, hlam, hphi, p3552_1]
                                · have p3552_0 := h3552c.1
                                  have p3552_1 := h3552c.2.1
                                  have p3552_2 := h3552c.2.2.1
                                  have p3552_3 := h3552c.2.2.2
                                  linarith only [h0, h3540, h3543, hc01, hc34, hlam, hphi, ht12, ht23, p3552_1]
                                · have p3552_0 := h3552c.1
                                  have p3552_1 := h3552c.2.1
                                  have p3552_2 := h3552c.2.2.1
                                  have p3552_3 := h3552c.2.2.2
                                  linarith only [h3540, hlam, p3552_0]
                                · have p3552_0 := h3552c.1
                                  have p3552_1 := h3552c.2.1
                                  have p3552_2 := h3552c.2.2.1
                                  have p3552_3 := h3552c.2.2.2
                                  linarith only [hlam, p3552_0]
                                · have p3552_0 := h3552c.1
                                  have p3552_1 := h3552c.2.1
                                  have p3552_2 := h3552c.2.2.1
                                  have p3552_3 := h3552c.2.2.2
                                  linarith only [h3547, hlam, p3552_0]
                                · have p3552_0 := h3552c.1
                                  have p3552_1 := h3552c.2.1
                                  have p3552_2 := h3552c.2.2.1
                                  have p3552_3 := h3552c.2.2.2
                                  linarith only [h3351, h3540, h3543, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3552_1, u5ehi5]
                                · have p3552_0 := h3552c.1
                                  have p3552_1 := h3552c.2.1
                                  have p3552_2 := h3552c.2.2.1
                                  have p3552_3 := h3552c.2.2.2
                                  linarith only [h0, h3541, hc01, hc12, hlam, hphi, p3552_1]
                                · have p3552_0 := h3552c.1
                                  have p3552_1 := h3552c.2.1
                                  have p3552_2 := h3552c.2.2.1
                                  have p3552_3 := h3552c.2.2.2
                                  linarith only [h3541, hlam, p3552_0]
                                · have p3552_0 := h3552c.1
                                  have p3552_1 := h3552c.2.1
                                  have p3552_2 := h3552c.2.2.1
                                  have p3552_3 := h3552c.2.2.2
                                  linarith only [h0, h2650, h3351, h3538, h3541, h3542, hc01, hc12, hlam, hphi, p3552_1, u5ehi8, u5elo1]
                                · have p3552_0 := h3552c.1
                                  have p3552_1 := h3552c.2.1
                                  have p3552_2 := h3552c.2.2.1
                                  have p3552_3 := h3552c.2.2.2
                                  linarith only [hlam, p3552_0]
                                · have p3552_0 := h3552c.1
                                  have p3552_1 := h3552c.2.1
                                  have p3552_2 := h3552c.2.2.1
                                  have p3552_3 := h3552c.2.2.2
                                  linarith only [h0, h3351, h3541, hc01, hc12, hlam, hphi, p3552_1]
                                · have p3552_0 := h3552c.1
                                  have p3552_1 := h3552c.2.1
                                  have p3552_2 := h3552c.2.2.1
                                  have p3552_3 := h3552c.2.2.2
                                  linarith only [h0, h2650, h3538, h3540, h3542, h3543, h3551, hc01, hc34, hlam, hphi, ht12, ht23, p3552_1, u5ehi9, u5elo1]
                                · have p3552_0 := h3552c.1
                                  have p3552_1 := h3552c.2.1
                                  have p3552_2 := h3552c.2.2.1
                                  have p3552_3 := h3552c.2.2.2
                                  linarith only [h3542, hlam, p3552_0]
                                · have p3552_0 := h3552c.1
                                  have p3552_1 := h3552c.2.1
                                  have p3552_2 := h3552c.2.2.1
                                  have p3552_3 := h3552c.2.2.2
                                  linarith only [h3549, hlam, p3552_1]
                                · have p3552_0 := h3552c.1
                                  have p3552_1 := h3552c.2.1
                                  have p3552_2 := h3552c.2.2.1
                                  have p3552_3 := h3552c.2.2.2
                                  linarith only [h3550, hlam, p3552_0]
                                · have p3552_0 := h3552c.1
                                  have p3552_1 := h3552c.2.1
                                  have p3552_2 := h3552c.2.2.1
                                  have p3552_3 := h3552c.2.2.2
                                  linarith only [hlam, p3552_0]
                              · linarith only [h2650, h3538, h3540, h3543, h3551, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi8]
                            · linarith only [h2337, h3270, h3539, h3550, hc02, hlam, hphi, ht23, ht34, ht45, u5elo1]
                          · linarith only [h2650, h3538, h3549, hlam]
                      · linarith only [h2167, h3270, h3539, h3541, h3546, hc01, hc12, hlam, hphi]
                    · linarith only [h2650, h3538, h3540, h3545, hlam]
                · linarith only [h3270, h3539, h3541, h3542, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
              · linarith only [h2650, h3538, h3540, h3541, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3591 | h3591
              · linarith only [h0, h3270, h3540, h3591, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3593 | h3593
                · linarith only [h0, h3351, h3540, h3593, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h3593, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
          · linarith only [h3455, h3538, h3539, hlam, hphi, u5ehi8, u5elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3597 | h3597
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3598 | h3598
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3599 | h3599
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3600 | h3600
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3601 | h3601
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3602 | h3602
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3603 | h3603
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3604 | h3604
                        · linarith only [h3455, h3597, h3598, h3604, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                        · linarith only [h0, h2650, h3601, h3604, hc01, hc13, hlam, hphi]
                      · linarith only [h3270, h3597, h3599, h3603, hlam]
                    · linarith only [h1750, h3602, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3609 | h3609
                    · linarith only [h2650, h3538, h3601, h3609, hc02, hc34, hlam, hphi, ht23]
                    · linarith only [h1750, h3609, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · linarith only [h0, h3600, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h2650, h3598, h3599, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3614 | h3614
              · linarith only [h0, h3270, h3598, h3614, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3616 | h3616
                · linarith only [h0, h3351, h3598, h3616, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h3616, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3619 | h3619
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3620 | h3620
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3621 | h3621
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3622 | h3622
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3623 | h3623
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3624 | h3624
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3625 | h3625
                        · linarith only [h0, h2650, h3455, h3619, h3625, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h2650, h3622, h3625, hc01, hc13, hlam, hphi]
                      · linarith only [h2167, h3624, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                    · linarith only [h1750, h3623, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3630 | h3630
                    · linarith only [h0, h2650, h3538, h3622, h3630, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h1750, h3630, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · linarith only [h0, h3621, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h2650, h3619, h3620, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3635 | h3635
              · linarith only [h0, h3270, h3619, h3635, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3637 | h3637
                · linarith only [h0, h3351, h3619, h3637, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h3637, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]

set_option maxHeartbeats 7280000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1750 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2167 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2337 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h2650 | h2650
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x1_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 h0 h1750 h2167 h2337 h2650
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x1_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 h0 h1750 h2167 h2337 h2650

set_option maxHeartbeats 7280000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1750 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2167 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2337 | h2337
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 h0 h1750 h2167 h2337
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 h0 h1750 h2167 h2337

set_option maxHeartbeats 7280000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1750 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2167 | h2167
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x1_x1_x0 m hb0 hb2 hb3 hb5 h0 h1750 h2167
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x1_x1_x1 m hb0 hb2 hb3 hb5 h0 h1750 h2167

set_option maxHeartbeats 7280000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc14 := m.hcor 1 4 (by decide)
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1750 | h1750
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x1_x0 m hb0 hb2 hb3 hb5 h0 h1750
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x1_x1 m hb0 hb2 hb3 hb5 h0 h1750

set_option maxHeartbeats 7280000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_LR (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x1 m hb0 hb2 hb3 hb5 h0

end R2N4
