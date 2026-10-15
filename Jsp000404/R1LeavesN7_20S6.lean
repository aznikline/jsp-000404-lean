import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_20S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7332000 in
set_option maxHeartbeats 7332000 in
theorem r1l7_22_14_H_I_L_I_s0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h2bigk := hb2.1
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
  · exact r1l7_22_14_H_I_L_I_s1 m hb2 hb4 h0 h1
  · rcases m.htr 0 2 3 (by decide) (by decide) with h3290 | h3290
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3291 | h3291
      · linarith only [h0, h1, h3291, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3293 | h3293
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3294 | h3294
          · linarith only [h0, h1, h3290, h3294, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3296 | h3296
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3297 | h3297
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3298 | h3298
                · linarith only [h0, h1, h3291, h3293, h3298, hc04, hc25, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3300 | h3300
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3301 | h3301
                    · linarith only [h0, h1, h3294, h3297, h3301, hlam]
                    · linarith only [h0, h1, h3297, h3301, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h1, h3293, h3297, h3298, h3300, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · linarith only [h3290, h3291, h3297, hc12, hc24, hlam, hphi]
            · linarith only [h0, h1, h3293, h3296, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3307 | h3307
          · linarith only [h0, h1, h3290, h3307, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3309 | h3309
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3310 | h3310
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3311 | h3311
                · linarith only [h0, h1, h3291, h3311, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3313 | h3313
                  · linarith only [h0, h3293, h3313, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3315 | h3315
                    · linarith only [h0, h1, h3307, h3310, h3315, hlam]
                    · linarith only [h0, h1, h3310, h3315, hc23, hc34, hlam, hphi]
              · linarith only [h3290, h3293, h3310, hc12, hc25, hlam, hphi]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3319 | h3319
              · linarith only [h0, h1, h3309, h3319, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h0, h1, h3290, h3309, h3319, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3322 | h3322
      · linarith only [h0, h1, h3322, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3324 | h3324
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3325 | h3325
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3326 | h3326
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3327 | h3327
              · linarith only [h0, h3290, h3324, h3327, hc01, hc25, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3329 | h3329
                · linarith only [h0, h1, h3322, h3329, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3331 | h3331
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3332 | h3332
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3333 | h3333
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3334 | h3334
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3335 | h3335
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3336 | h3336
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3337 | h3337
                              · rcases h2bigk with h3338c | h3338c | h3338c | h3338c | h3338c | h3338c | h3338c | h3338c | h3338c | h3338c | h3338c | h3338c | h3338c | h3338c | h3338c | h3338c | h3338c | h3338c | h3338c | h3338c | h3338c | h3338c | h3338c | h3338c | h3338c
                                · have p3338_0 := h3338c.1
                                  have p3338_1 := h3338c.2.1
                                  have p3338_2 := h3338c.2.2.1
                                  have p3338_3 := h3338c.2.2.2
                                  linarith only [hlam, p3338_0]
                                · have p3338_0 := h3338c.1
                                  have p3338_1 := h3338c.2.1
                                  have p3338_2 := h3338c.2.2.1
                                  have p3338_3 := h3338c.2.2.2
                                  linarith only [h3331, h3335, h3337, hc02, hc45, hlam, hphi, ht0b, ht5b, p3338_1]
                                · have p3338_0 := h3338c.1
                                  have p3338_1 := h3338c.2.1
                                  have p3338_2 := h3338c.2.2.1
                                  have p3338_3 := h3338c.2.2.2
                                  linarith only [h3290, hlam, p3338_0]
                                · have p3338_0 := h3338c.1
                                  have p3338_1 := h3338c.2.1
                                  have p3338_2 := h3338c.2.2.1
                                  have p3338_3 := h3338c.2.2.2
                                  linarith only [h3322, hlam, p3338_0]
                                · have p3338_0 := h3338c.1
                                  have p3338_1 := h3338c.2.1
                                  have p3338_2 := h3338c.2.2.1
                                  have p3338_3 := h3338c.2.2.2
                                  linarith only [h0, h1, h3332, h3335, h3337, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p3338_1]
                                · have p3338_0 := h3338c.1
                                  have p3338_1 := h3338c.2.1
                                  have p3338_2 := h3338c.2.2.1
                                  have p3338_3 := h3338c.2.2.2
                                  linarith only [h0, hlam, p3338_0]
                                · have p3338_0 := h3338c.1
                                  have p3338_1 := h3338c.2.1
                                  have p3338_2 := h3338c.2.2.1
                                  have p3338_3 := h3338c.2.2.2
                                  linarith only [hlam, p3338_0]
                                · have p3338_0 := h3338c.1
                                  have p3338_1 := h3338c.2.1
                                  have p3338_2 := h3338c.2.2.1
                                  have p3338_3 := h3338c.2.2.2
                                  linarith only [h3327, hlam, p3338_0]
                                · have p3338_0 := h3338c.1
                                  have p3338_1 := h3338c.2.1
                                  have p3338_2 := h3338c.2.2.1
                                  have p3338_3 := h3338c.2.2.2
                                  linarith only [h3329, hlam, p3338_0]
                                · have p3338_0 := h3338c.1
                                  have p3338_1 := h3338c.2.1
                                  have p3338_2 := h3338c.2.2.1
                                  have p3338_3 := h3338c.2.2.2
                                  linarith only [h0, h1, h3327, h3332, h3335, h3337, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3338_1]
                                · have p3338_0 := h3338c.1
                                  have p3338_1 := h3338c.2.1
                                  have p3338_2 := h3338c.2.2.1
                                  have p3338_3 := h3338c.2.2.2
                                  linarith only [hc02, hc23, hlam, hphi, p3338_1]
                                · have p3338_0 := h3338c.1
                                  have p3338_1 := h3338c.2.1
                                  have p3338_2 := h3338c.2.2.1
                                  have p3338_3 := h3338c.2.2.2
                                  linarith only [hc12, hc23, hlam, hphi, p3338_1]
                                · have p3338_0 := h3338c.1
                                  have p3338_1 := h3338c.2.1
                                  have p3338_2 := h3338c.2.2.1
                                  have p3338_3 := h3338c.2.2.2
                                  linarith only [hlam, p3338_0]
                                · have p3338_0 := h3338c.1
                                  have p3338_1 := h3338c.2.1
                                  have p3338_2 := h3338c.2.2.1
                                  have p3338_3 := h3338c.2.2.2
                                  linarith only [h1, h3329, hc01, hc23, hlam, hphi, ht12, p3338_1]
                                · have p3338_0 := h3338c.1
                                  have p3338_1 := h3338c.2.1
                                  have p3338_2 := h3338c.2.2.1
                                  have p3338_3 := h3338c.2.2.2
                                  rcases p3338_3 (m.d 0 2) (by simp) with h3353 | h3353
                                  · linarith only [h3290, h3353, hlam]
                                  · linarith only [h3324, h3353, hlam]
                                · have p3338_0 := h3338c.1
                                  have p3338_1 := h3338c.2.1
                                  have p3338_2 := h3338c.2.2.1
                                  have p3338_3 := h3338c.2.2.2
                                  linarith only [h0, h3331, h3335, h3337, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3338_1]
                                · have p3338_0 := h3338c.1
                                  have p3338_1 := h3338c.2.1
                                  have p3338_2 := h3338c.2.2.1
                                  have p3338_3 := h3338c.2.2.2
                                  linarith only [h3331, h3335, h3337, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3338_1]
                                · have p3338_0 := h3338c.1
                                  have p3338_1 := h3338c.2.1
                                  have p3338_2 := h3338c.2.2.1
                                  have p3338_3 := h3338c.2.2.2
                                  linarith only [h3334, hlam, p3338_1]
                                · have p3338_0 := h3338c.1
                                  have p3338_1 := h3338c.2.1
                                  have p3338_2 := h3338c.2.2.1
                                  have p3338_3 := h3338c.2.2.2
                                  linarith only [hlam, p3338_0]
                                · have p3338_0 := h3338c.1
                                  have p3338_1 := h3338c.2.1
                                  have p3338_2 := h3338c.2.2.1
                                  have p3338_3 := h3338c.2.2.2
                                  rcases p3338_3 (m.d 0 2) (by simp) with h3360 | h3360
                                  · linarith only [h3322, h3360, hlam]
                                  · linarith only [h3324, h3360, hlam]
                                · have p3338_0 := h3338c.1
                                  have p3338_1 := h3338c.2.1
                                  have p3338_2 := h3338c.2.2.1
                                  have p3338_3 := h3338c.2.2.2
                                  linarith only [h3324, hlam, p3338_0]
                                · have p3338_0 := h3338c.1
                                  have p3338_1 := h3338c.2.1
                                  have p3338_2 := h3338c.2.2.1
                                  have p3338_3 := h3338c.2.2.2
                                  linarith only [h3331, hlam, p3338_0]
                                · have p3338_0 := h3338c.1
                                  have p3338_1 := h3338c.2.1
                                  have p3338_2 := h3338c.2.2.1
                                  have p3338_3 := h3338c.2.2.2
                                  linarith only [h3335, hlam, p3338_1]
                                · have p3338_0 := h3338c.1
                                  have p3338_1 := h3338c.2.1
                                  have p3338_2 := h3338c.2.2.1
                                  have p3338_3 := h3338c.2.2.2
                                  linarith only [h3336, hlam, p3338_0]
                                · have p3338_0 := h3338c.1
                                  have p3338_1 := h3338c.2.1
                                  have p3338_2 := h3338c.2.2.1
                                  have p3338_3 := h3338c.2.2.2
                                  linarith only [hlam, p3338_0]
                              · linarith only [h0, h1, h3329, h3331, h3334, h3336, h3337, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h1, h3329, h3336, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h0, h1, h3329, h3331, h3334, h3335, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h0, h1, h3327, h3331, h3332, h3334, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h0, h1, h3326, h3331, h3333, hc05, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h1, h3290, h3325, h3331, h3332, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h0, h1, h3324, h3329, h3331, hc12, hc24, hlam, hphi]
            · linarith only [h0, h1, h3324, h3326, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3376 | h3376
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3377 | h3377
              · linarith only [h0, h1, h3290, h3377, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3379 | h3379
                · linarith only [h0, h3322, h3379, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3381 | h3381
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3382 | h3382
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3383 | h3383
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3384 | h3384
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3385 | h3385
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3386 | h3386
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3387 | h3387
                              · rcases h2bigk with h3388c | h3388c | h3388c | h3388c | h3388c | h3388c | h3388c | h3388c | h3388c | h3388c | h3388c | h3388c | h3388c | h3388c | h3388c | h3388c | h3388c | h3388c | h3388c | h3388c | h3388c | h3388c | h3388c | h3388c | h3388c
                                · have p3388_0 := h3388c.1
                                  have p3388_1 := h3388c.2.1
                                  have p3388_2 := h3388c.2.2.1
                                  have p3388_3 := h3388c.2.2.2
                                  linarith only [hlam, p3388_0]
                                · have p3388_0 := h3388c.1
                                  have p3388_1 := h3388c.2.1
                                  have p3388_2 := h3388c.2.2.1
                                  have p3388_3 := h3388c.2.2.2
                                  linarith only [h3381, h3385, h3387, hc02, hc45, hlam, hphi, ht0b, ht5b, p3388_1]
                                · have p3388_0 := h3388c.1
                                  have p3388_1 := h3388c.2.1
                                  have p3388_2 := h3388c.2.2.1
                                  have p3388_3 := h3388c.2.2.2
                                  linarith only [h3290, hlam, p3388_0]
                                · have p3388_0 := h3388c.1
                                  have p3388_1 := h3388c.2.1
                                  have p3388_2 := h3388c.2.2.1
                                  have p3388_3 := h3388c.2.2.2
                                  linarith only [h3322, hlam, p3388_0]
                                · have p3388_0 := h3388c.1
                                  have p3388_1 := h3388c.2.1
                                  have p3388_2 := h3388c.2.2.1
                                  have p3388_3 := h3388c.2.2.2
                                  linarith only [h3290, h3325, h3377, h3382, h3385, h3387, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3388_1]
                                · have p3388_0 := h3388c.1
                                  have p3388_1 := h3388c.2.1
                                  have p3388_2 := h3388c.2.2.1
                                  have p3388_3 := h3388c.2.2.2
                                  linarith only [h0, hlam, p3388_0]
                                · have p3388_0 := h3388c.1
                                  have p3388_1 := h3388c.2.1
                                  have p3388_2 := h3388c.2.2.1
                                  have p3388_3 := h3388c.2.2.2
                                  linarith only [hlam, p3388_0]
                                · have p3388_0 := h3388c.1
                                  have p3388_1 := h3388c.2.1
                                  have p3388_2 := h3388c.2.2.1
                                  have p3388_3 := h3388c.2.2.2
                                  linarith only [h3377, hlam, p3388_0]
                                · have p3388_0 := h3388c.1
                                  have p3388_1 := h3388c.2.1
                                  have p3388_2 := h3388c.2.2.1
                                  have p3388_3 := h3388c.2.2.2
                                  linarith only [h3379, hlam, p3388_0]
                                · have p3388_0 := h3388c.1
                                  have p3388_1 := h3388c.2.1
                                  have p3388_2 := h3388c.2.2.1
                                  have p3388_3 := h3388c.2.2.2
                                  linarith only [h0, h1, h3325, h3377, h3382, h3385, h3387, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3388_1]
                                · have p3388_0 := h3388c.1
                                  have p3388_1 := h3388c.2.1
                                  have p3388_2 := h3388c.2.2.1
                                  have p3388_3 := h3388c.2.2.2
                                  linarith only [hc02, hc23, hlam, hphi, p3388_1]
                                · have p3388_0 := h3388c.1
                                  have p3388_1 := h3388c.2.1
                                  have p3388_2 := h3388c.2.2.1
                                  have p3388_3 := h3388c.2.2.2
                                  linarith only [hc12, hc23, hlam, hphi, p3388_1]
                                · have p3388_0 := h3388c.1
                                  have p3388_1 := h3388c.2.1
                                  have p3388_2 := h3388c.2.2.1
                                  have p3388_3 := h3388c.2.2.2
                                  linarith only [hlam, p3388_0]
                                · have p3388_0 := h3388c.1
                                  have p3388_1 := h3388c.2.1
                                  have p3388_2 := h3388c.2.2.1
                                  have p3388_3 := h3388c.2.2.2
                                  linarith only [h0, h3322, hc12, hc23, hlam, hphi, p3388_1]
                                · have p3388_0 := h3388c.1
                                  have p3388_1 := h3388c.2.1
                                  have p3388_2 := h3388c.2.2.1
                                  have p3388_3 := h3388c.2.2.2
                                  rcases p3388_3 (m.d 0 2) (by simp) with h3403 | h3403
                                  · linarith only [h3290, h3403, hlam]
                                  · linarith only [h3324, h3403, hlam]
                                · have p3388_0 := h3388c.1
                                  have p3388_1 := h3388c.2.1
                                  have p3388_2 := h3388c.2.2.1
                                  have p3388_3 := h3388c.2.2.2
                                  linarith only [h0, h3381, h3385, h3387, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3388_1]
                                · have p3388_0 := h3388c.1
                                  have p3388_1 := h3388c.2.1
                                  have p3388_2 := h3388c.2.2.1
                                  have p3388_3 := h3388c.2.2.2
                                  linarith only [h3381, h3385, h3387, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3388_1]
                                · have p3388_0 := h3388c.1
                                  have p3388_1 := h3388c.2.1
                                  have p3388_2 := h3388c.2.2.1
                                  have p3388_3 := h3388c.2.2.2
                                  linarith only [h3384, hlam, p3388_1]
                                · have p3388_0 := h3388c.1
                                  have p3388_1 := h3388c.2.1
                                  have p3388_2 := h3388c.2.2.1
                                  have p3388_3 := h3388c.2.2.2
                                  linarith only [hlam, p3388_0]
                                · have p3388_0 := h3388c.1
                                  have p3388_1 := h3388c.2.1
                                  have p3388_2 := h3388c.2.2.1
                                  have p3388_3 := h3388c.2.2.2
                                  rcases p3388_3 (m.d 0 2) (by simp) with h3410 | h3410
                                  · linarith only [h3322, h3410, hlam]
                                  · linarith only [h3324, h3410, hlam]
                                · have p3388_0 := h3388c.1
                                  have p3388_1 := h3388c.2.1
                                  have p3388_2 := h3388c.2.2.1
                                  have p3388_3 := h3388c.2.2.2
                                  linarith only [h3324, hlam, p3388_0]
                                · have p3388_0 := h3388c.1
                                  have p3388_1 := h3388c.2.1
                                  have p3388_2 := h3388c.2.2.1
                                  have p3388_3 := h3388c.2.2.2
                                  linarith only [h3381, hlam, p3388_0]
                                · have p3388_0 := h3388c.1
                                  have p3388_1 := h3388c.2.1
                                  have p3388_2 := h3388c.2.2.1
                                  have p3388_3 := h3388c.2.2.2
                                  linarith only [h3385, hlam, p3388_1]
                                · have p3388_0 := h3388c.1
                                  have p3388_1 := h3388c.2.1
                                  have p3388_2 := h3388c.2.2.1
                                  have p3388_3 := h3388c.2.2.2
                                  linarith only [h3386, hlam, p3388_0]
                                · have p3388_0 := h3388c.1
                                  have p3388_1 := h3388c.2.1
                                  have p3388_2 := h3388c.2.2.1
                                  have p3388_3 := h3388c.2.2.2
                                  linarith only [hlam, p3388_0]
                              · linarith only [h3325, h3376, h3387, hlam]
                            · linarith only [h0, h3322, h3381, h3383, h3386, hlam]
                          · linarith only [h0, h1, h3325, h3377, h3381, h3382, h3385, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h3377, h3382, h3384, hlam]
                      · linarith only [h0, h1, h3381, h3383, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3423 | h3423
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3424 | h3424
                        · linarith only [h0, h1, h3381, h3382, h3424, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3426 | h3426
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3427 | h3427
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3428 | h3428
                              · rcases h2bigk with h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c | h3429c
                                · have p3429_0 := h3429c.1
                                  have p3429_1 := h3429c.2.1
                                  have p3429_2 := h3429c.2.2.1
                                  have p3429_3 := h3429c.2.2.2
                                  linarith only [hlam, p3429_0]
                                · have p3429_0 := h3429c.1
                                  have p3429_1 := h3429c.2.1
                                  have p3429_2 := h3429c.2.2.1
                                  have p3429_3 := h3429c.2.2.2
                                  linarith only [h3381, h3426, h3428, hc02, hc45, hlam, hphi, ht0b, ht5b, p3429_1]
                                · have p3429_0 := h3429c.1
                                  have p3429_1 := h3429c.2.1
                                  have p3429_2 := h3429c.2.2.1
                                  have p3429_3 := h3429c.2.2.2
                                  linarith only [h3290, hlam, p3429_0]
                                · have p3429_0 := h3429c.1
                                  have p3429_1 := h3429c.2.1
                                  have p3429_2 := h3429c.2.2.1
                                  have p3429_3 := h3429c.2.2.2
                                  linarith only [h3322, hlam, p3429_0]
                                · have p3429_0 := h3429c.1
                                  have p3429_1 := h3429c.2.1
                                  have p3429_2 := h3429c.2.2.1
                                  have p3429_3 := h3429c.2.2.2
                                  linarith only [h3290, h3424, h3426, h3428, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3429_1]
                                · have p3429_0 := h3429c.1
                                  have p3429_1 := h3429c.2.1
                                  have p3429_2 := h3429c.2.2.1
                                  have p3429_3 := h3429c.2.2.2
                                  linarith only [h0, hlam, p3429_0]
                                · have p3429_0 := h3429c.1
                                  have p3429_1 := h3429c.2.1
                                  have p3429_2 := h3429c.2.2.1
                                  have p3429_3 := h3429c.2.2.2
                                  linarith only [hlam, p3429_0]
                                · have p3429_0 := h3429c.1
                                  have p3429_1 := h3429c.2.1
                                  have p3429_2 := h3429c.2.2.1
                                  have p3429_3 := h3429c.2.2.2
                                  linarith only [h3377, hlam, p3429_0]
                                · have p3429_0 := h3429c.1
                                  have p3429_1 := h3429c.2.1
                                  have p3429_2 := h3429c.2.2.1
                                  have p3429_3 := h3429c.2.2.2
                                  linarith only [h3379, hlam, p3429_0]
                                · have p3429_0 := h3429c.1
                                  have p3429_1 := h3429c.2.1
                                  have p3429_2 := h3429c.2.2.1
                                  have p3429_3 := h3429c.2.2.2
                                  linarith only [h0, h3426, h3428, hc01, hc45, hlam, hphi, ht0b, ht5b, p3429_1]
                                · have p3429_0 := h3429c.1
                                  have p3429_1 := h3429c.2.1
                                  have p3429_2 := h3429c.2.2.1
                                  have p3429_3 := h3429c.2.2.2
                                  linarith only [h3424, hc02, hc34, hlam, hphi, ht23, p3429_1]
                                · have p3429_0 := h3429c.1
                                  have p3429_1 := h3429c.2.1
                                  have p3429_2 := h3429c.2.2.1
                                  have p3429_3 := h3429c.2.2.2
                                  linarith only [h3424, hc12, hc34, hlam, hphi, ht23, p3429_1]
                                · have p3429_0 := h3429c.1
                                  have p3429_1 := h3429c.2.1
                                  have p3429_2 := h3429c.2.2.1
                                  have p3429_3 := h3429c.2.2.2
                                  linarith only [hlam, p3429_0]
                                · have p3429_0 := h3429c.1
                                  have p3429_1 := h3429c.2.1
                                  have p3429_2 := h3429c.2.2.1
                                  have p3429_3 := h3429c.2.2.2
                                  linarith only [h3424, hlam, p3429_0]
                                · have p3429_0 := h3429c.1
                                  have p3429_1 := h3429c.2.1
                                  have p3429_2 := h3429c.2.2.1
                                  have p3429_3 := h3429c.2.2.2
                                  linarith only [h3424, h3426, h3428, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3429_1]
                                · have p3429_0 := h3429c.1
                                  have p3429_1 := h3429c.2.1
                                  have p3429_2 := h3429c.2.2.1
                                  have p3429_3 := h3429c.2.2.2
                                  linarith only [h3424, hc02, hc34, hlam, hphi, ht23, p3429_1]
                                · have p3429_0 := h3429c.1
                                  have p3429_1 := h3429c.2.1
                                  have p3429_2 := h3429c.2.2.1
                                  have p3429_3 := h3429c.2.2.2
                                  linarith only [h3381, h3424, h3426, h3428, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3429_1]
                                · have p3429_0 := h3429c.1
                                  have p3429_1 := h3429c.2.1
                                  have p3429_2 := h3429c.2.2.1
                                  have p3429_3 := h3429c.2.2.2
                                  linarith only [h3290, h3424, hc03, hc34, hlam, hphi, p3429_1]
                                · have p3429_0 := h3429c.1
                                  have p3429_1 := h3429c.2.1
                                  have p3429_2 := h3429c.2.2.1
                                  have p3429_3 := h3429c.2.2.2
                                  linarith only [hlam, p3429_0]
                                · have p3429_0 := h3429c.1
                                  have p3429_1 := h3429c.2.1
                                  have p3429_2 := h3429c.2.2.1
                                  have p3429_3 := h3429c.2.2.2
                                  rcases p3429_3 (m.d 0 2) (by simp) with h3449 | h3449
                                  · linarith only [h3322, h3449, hlam]
                                  · linarith only [h3324, h3449, hlam]
                                · have p3429_0 := h3429c.1
                                  have p3429_1 := h3429c.2.1
                                  have p3429_2 := h3429c.2.2.1
                                  have p3429_3 := h3429c.2.2.2
                                  linarith only [h3324, hlam, p3429_0]
                                · have p3429_0 := h3429c.1
                                  have p3429_1 := h3429c.2.1
                                  have p3429_2 := h3429c.2.2.1
                                  have p3429_3 := h3429c.2.2.2
                                  linarith only [h3381, hlam, p3429_0]
                                · have p3429_0 := h3429c.1
                                  have p3429_1 := h3429c.2.1
                                  have p3429_2 := h3429c.2.2.1
                                  have p3429_3 := h3429c.2.2.2
                                  linarith only [h3426, hlam, p3429_1]
                                · have p3429_0 := h3429c.1
                                  have p3429_1 := h3429c.2.1
                                  have p3429_2 := h3429c.2.2.1
                                  have p3429_3 := h3429c.2.2.2
                                  linarith only [h3427, hlam, p3429_0]
                                · have p3429_0 := h3429c.1
                                  have p3429_1 := h3429c.2.1
                                  have p3429_2 := h3429c.2.2.1
                                  have p3429_3 := h3429c.2.2.2
                                  linarith only [hlam, p3429_0]
                              · linarith only [h0, h1, h3379, h3381, h3424, h3426, h3428, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                            · linarith only [h0, h1, h3379, h3381, h3423, h3427, hlam]
                          · linarith only [h0, h1, h3290, h3381, h3426, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · linarith only [h1, h3290, h3324, h3376, h3423, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h3290, h3324, h3325, h3381, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h0, h1, h3324, h3376, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3463 | h3463
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3464 | h3464
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3465 | h3465
              · linarith only [h0, h3290, h3465, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3467 | h3467
                · linarith only [h0, h1, h3290, h3322, h3463, h3467, hc02, hc23, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3469 | h3469
                  · linarith only [h0, h3324, h3469, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3471 | h3471
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3472 | h3472
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3473 | h3473
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3474 | h3474
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3475 | h3475
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3476 | h3476
                              · rcases h2bigk with h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c | h3477c
                                · have p3477_0 := h3477c.1
                                  have p3477_1 := h3477c.2.1
                                  have p3477_2 := h3477c.2.2.1
                                  have p3477_3 := h3477c.2.2.2
                                  linarith only [hlam, p3477_0]
                                · have p3477_0 := h3477c.1
                                  have p3477_1 := h3477c.2.1
                                  have p3477_2 := h3477c.2.2.1
                                  have p3477_3 := h3477c.2.2.2
                                  linarith only [h3324, hc12, hc25, hlam, hphi, p3477_1]
                                · have p3477_0 := h3477c.1
                                  have p3477_1 := h3477c.2.1
                                  have p3477_2 := h3477c.2.2.1
                                  have p3477_3 := h3477c.2.2.2
                                  linarith only [h3290, hlam, p3477_0]
                                · have p3477_0 := h3477c.1
                                  have p3477_1 := h3477c.2.1
                                  have p3477_2 := h3477c.2.2.1
                                  have p3477_3 := h3477c.2.2.2
                                  linarith only [h3322, hlam, p3477_0]
                                · have p3477_0 := h3477c.1
                                  have p3477_1 := h3477c.2.1
                                  have p3477_2 := h3477c.2.2.1
                                  have p3477_3 := h3477c.2.2.2
                                  linarith only [h3324, hlam, p3477_0]
                                · have p3477_0 := h3477c.1
                                  have p3477_1 := h3477c.2.1
                                  have p3477_2 := h3477c.2.2.1
                                  have p3477_3 := h3477c.2.2.2
                                  linarith only [h0, hlam, p3477_0]
                                · have p3477_0 := h3477c.1
                                  have p3477_1 := h3477c.2.1
                                  have p3477_2 := h3477c.2.2.1
                                  have p3477_3 := h3477c.2.2.2
                                  linarith only [hlam, p3477_0]
                                · have p3477_0 := h3477c.1
                                  have p3477_1 := h3477c.2.1
                                  have p3477_2 := h3477c.2.2.1
                                  have p3477_3 := h3477c.2.2.2
                                  linarith only [h3465, hlam, p3477_0]
                                · have p3477_0 := h3477c.1
                                  have p3477_1 := h3477c.2.1
                                  have p3477_2 := h3477c.2.2.1
                                  have p3477_3 := h3477c.2.2.2
                                  linarith only [h3467, hlam, p3477_0]
                                · have p3477_0 := h3477c.1
                                  have p3477_1 := h3477c.2.1
                                  have p3477_2 := h3477c.2.2.1
                                  have p3477_3 := h3477c.2.2.2
                                  linarith only [h3469, hlam, p3477_0]
                                · have p3477_0 := h3477c.1
                                  have p3477_1 := h3477c.2.1
                                  have p3477_2 := h3477c.2.2.1
                                  have p3477_3 := h3477c.2.2.2
                                  linarith only [hc02, hc23, hlam, hphi, p3477_1]
                                · have p3477_0 := h3477c.1
                                  have p3477_1 := h3477c.2.1
                                  have p3477_2 := h3477c.2.2.1
                                  have p3477_3 := h3477c.2.2.2
                                  linarith only [hc12, hc23, hlam, hphi, p3477_1]
                                · have p3477_0 := h3477c.1
                                  have p3477_1 := h3477c.2.1
                                  have p3477_2 := h3477c.2.2.1
                                  have p3477_3 := h3477c.2.2.2
                                  linarith only [hlam, p3477_0]
                                · have p3477_0 := h3477c.1
                                  have p3477_1 := h3477c.2.1
                                  have p3477_2 := h3477c.2.2.1
                                  have p3477_3 := h3477c.2.2.2
                                  linarith only [h0, h3322, hc12, hc23, hlam, hphi, p3477_1]
                                · have p3477_0 := h3477c.1
                                  have p3477_1 := h3477c.2.1
                                  have p3477_2 := h3477c.2.2.1
                                  have p3477_3 := h3477c.2.2.2
                                  linarith only [h0, h3324, hc12, hc23, hlam, hphi, p3477_1]
                                · have p3477_0 := h3477c.1
                                  have p3477_1 := h3477c.2.1
                                  have p3477_2 := h3477c.2.2.1
                                  have p3477_3 := h3477c.2.2.2
                                  linarith only [h0, hc12, hc24, hlam, hphi, p3477_1]
                                · have p3477_0 := h3477c.1
                                  have p3477_1 := h3477c.2.1
                                  have p3477_2 := h3477c.2.2.1
                                  have p3477_3 := h3477c.2.2.2
                                  linarith only [hc12, hc24, hlam, hphi, p3477_1]
                                · have p3477_0 := h3477c.1
                                  have p3477_1 := h3477c.2.1
                                  have p3477_2 := h3477c.2.2.1
                                  have p3477_3 := h3477c.2.2.2
                                  linarith only [h3473, hlam, p3477_1]
                                · have p3477_0 := h3477c.1
                                  have p3477_1 := h3477c.2.1
                                  have p3477_2 := h3477c.2.2.1
                                  have p3477_3 := h3477c.2.2.2
                                  linarith only [hlam, p3477_0]
                                · have p3477_0 := h3477c.1
                                  have p3477_1 := h3477c.2.1
                                  have p3477_2 := h3477c.2.2.1
                                  have p3477_3 := h3477c.2.2.2
                                  linarith only [h0, h3324, h3473, hc12, hc23, hlam, hphi, p3477_1]
                                · have p3477_0 := h3477c.1
                                  have p3477_1 := h3477c.2.1
                                  have p3477_2 := h3477c.2.2.1
                                  have p3477_3 := h3477c.2.2.2
                                  linarith only [h0, hc12, hc25, hlam, hphi, p3477_1]
                                · have p3477_0 := h3477c.1
                                  have p3477_1 := h3477c.2.1
                                  have p3477_2 := h3477c.2.2.1
                                  have p3477_3 := h3477c.2.2.2
                                  linarith only [hc12, hc25, hlam, hphi, p3477_1]
                                · have p3477_0 := h3477c.1
                                  have p3477_1 := h3477c.2.1
                                  have p3477_2 := h3477c.2.2.1
                                  have p3477_3 := h3477c.2.2.2
                                  linarith only [h3474, hlam, p3477_1]
                                · have p3477_0 := h3477c.1
                                  have p3477_1 := h3477c.2.1
                                  have p3477_2 := h3477c.2.2.1
                                  have p3477_3 := h3477c.2.2.2
                                  linarith only [h3475, hlam, p3477_0]
                                · have p3477_0 := h3477c.1
                                  have p3477_1 := h3477c.2.1
                                  have p3477_2 := h3477c.2.2.1
                                  have p3477_3 := h3477c.2.2.2
                                  linarith only [hlam, p3477_0]
                              · rcases h2bigk with h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c
                                · have p3503_0 := h3503c.1
                                  have p3503_1 := h3503c.2.1
                                  have p3503_2 := h3503c.2.2.1
                                  have p3503_3 := h3503c.2.2.2
                                  linarith only [hlam, p3503_0]
                                · have p3503_0 := h3503c.1
                                  have p3503_1 := h3503c.2.1
                                  have p3503_2 := h3503c.2.2.1
                                  have p3503_3 := h3503c.2.2.2
                                  linarith only [h0, h1, h3465, h3471, hc12, hc23, hlam, hphi, p3503_1]
                                · have p3503_0 := h3503c.1
                                  have p3503_1 := h3503c.2.1
                                  have p3503_2 := h3503c.2.2.1
                                  have p3503_3 := h3503c.2.2.2
                                  linarith only [h3290, hlam, p3503_0]
                                · have p3503_0 := h3503c.1
                                  have p3503_1 := h3503c.2.1
                                  have p3503_2 := h3503c.2.2.1
                                  have p3503_3 := h3503c.2.2.2
                                  linarith only [h3322, hlam, p3503_0]
                                · have p3503_0 := h3503c.1
                                  have p3503_1 := h3503c.2.1
                                  have p3503_2 := h3503c.2.2.1
                                  have p3503_3 := h3503c.2.2.2
                                  linarith only [h3324, hlam, p3503_0]
                                · have p3503_0 := h3503c.1
                                  have p3503_1 := h3503c.2.1
                                  have p3503_2 := h3503c.2.2.1
                                  have p3503_3 := h3503c.2.2.2
                                  linarith only [h0, hlam, p3503_0]
                                · have p3503_0 := h3503c.1
                                  have p3503_1 := h3503c.2.1
                                  have p3503_2 := h3503c.2.2.1
                                  have p3503_3 := h3503c.2.2.2
                                  linarith only [hlam, p3503_0]
                                · have p3503_0 := h3503c.1
                                  have p3503_1 := h3503c.2.1
                                  have p3503_2 := h3503c.2.2.1
                                  have p3503_3 := h3503c.2.2.2
                                  linarith only [h3465, hlam, p3503_0]
                                · have p3503_0 := h3503c.1
                                  have p3503_1 := h3503c.2.1
                                  have p3503_2 := h3503c.2.2.1
                                  have p3503_3 := h3503c.2.2.2
                                  linarith only [h3467, hlam, p3503_0]
                                · have p3503_0 := h3503c.1
                                  have p3503_1 := h3503c.2.1
                                  have p3503_2 := h3503c.2.2.1
                                  have p3503_3 := h3503c.2.2.2
                                  linarith only [h3469, hlam, p3503_0]
                                · have p3503_0 := h3503c.1
                                  have p3503_1 := h3503c.2.1
                                  have p3503_2 := h3503c.2.2.1
                                  have p3503_3 := h3503c.2.2.2
                                  linarith only [hc02, hc23, hlam, hphi, p3503_1]
                                · have p3503_0 := h3503c.1
                                  have p3503_1 := h3503c.2.1
                                  have p3503_2 := h3503c.2.2.1
                                  have p3503_3 := h3503c.2.2.2
                                  linarith only [hc12, hc23, hlam, hphi, p3503_1]
                                · have p3503_0 := h3503c.1
                                  have p3503_1 := h3503c.2.1
                                  have p3503_2 := h3503c.2.2.1
                                  have p3503_3 := h3503c.2.2.2
                                  linarith only [hlam, p3503_0]
                                · have p3503_0 := h3503c.1
                                  have p3503_1 := h3503c.2.1
                                  have p3503_2 := h3503c.2.2.1
                                  have p3503_3 := h3503c.2.2.2
                                  linarith only [h0, h3322, hc12, hc23, hlam, hphi, p3503_1]
                                · have p3503_0 := h3503c.1
                                  have p3503_1 := h3503c.2.1
                                  have p3503_2 := h3503c.2.2.1
                                  have p3503_3 := h3503c.2.2.2
                                  linarith only [h0, h3324, hc12, hc23, hlam, hphi, p3503_1]
                                · have p3503_0 := h3503c.1
                                  have p3503_1 := h3503c.2.1
                                  have p3503_2 := h3503c.2.2.1
                                  have p3503_3 := h3503c.2.2.2
                                  linarith only [h0, hc12, hc24, hlam, hphi, p3503_1]
                                · have p3503_0 := h3503c.1
                                  have p3503_1 := h3503c.2.1
                                  have p3503_2 := h3503c.2.2.1
                                  have p3503_3 := h3503c.2.2.2
                                  linarith only [hc12, hc24, hlam, hphi, p3503_1]
                                · have p3503_0 := h3503c.1
                                  have p3503_1 := h3503c.2.1
                                  have p3503_2 := h3503c.2.2.1
                                  have p3503_3 := h3503c.2.2.2
                                  linarith only [h3473, hlam, p3503_1]
                                · have p3503_0 := h3503c.1
                                  have p3503_1 := h3503c.2.1
                                  have p3503_2 := h3503c.2.2.1
                                  have p3503_3 := h3503c.2.2.2
                                  linarith only [hlam, p3503_0]
                                · have p3503_0 := h3503c.1
                                  have p3503_1 := h3503c.2.1
                                  have p3503_2 := h3503c.2.2.1
                                  have p3503_3 := h3503c.2.2.2
                                  linarith only [h0, h3324, h3473, hc12, hc23, hlam, hphi, p3503_1]
                                · have p3503_0 := h3503c.1
                                  have p3503_1 := h3503c.2.1
                                  have p3503_2 := h3503c.2.2.1
                                  have p3503_3 := h3503c.2.2.2
                                  linarith only [h0, hc12, hc25, hlam, hphi, p3503_1]
                                · have p3503_0 := h3503c.1
                                  have p3503_1 := h3503c.2.1
                                  have p3503_2 := h3503c.2.2.1
                                  have p3503_3 := h3503c.2.2.2
                                  linarith only [hc12, hc25, hlam, hphi, p3503_1]
                                · have p3503_0 := h3503c.1
                                  have p3503_1 := h3503c.2.1
                                  have p3503_2 := h3503c.2.2.1
                                  have p3503_3 := h3503c.2.2.2
                                  linarith only [h3474, hlam, p3503_1]
                                · have p3503_0 := h3503c.1
                                  have p3503_1 := h3503c.2.1
                                  have p3503_2 := h3503c.2.2.1
                                  have p3503_3 := h3503c.2.2.2
                                  linarith only [h3475, hlam, p3503_0]
                                · have p3503_0 := h3503c.1
                                  have p3503_1 := h3503c.2.1
                                  have p3503_2 := h3503c.2.2.1
                                  have p3503_3 := h3503c.2.2.2
                                  linarith only [hlam, p3503_0]
                            · linarith only [h3322, h3464, h3475, hlam]
                          · linarith only [h0, h1, h3465, h3471, h3474, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h3465, h3471, h3473, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h1, h3464, h3472, hlam]
                    · linarith only [h0, h1, h3290, h3463, h3471, hc12, hc23, hlam, hphi]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3534 | h3534
              · linarith only [h0, h1, h3290, h3464, h3534, hc03, hc45, hlam, hphi, ht34]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3536 | h3536
                · linarith only [h0, h1, h3322, h3464, h3536, hc02, hc45, hlam, hphi, ht23, ht34]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3538 | h3538
                  · linarith only [h0, h1, h3324, h3464, h3538, hc02, hc45, hlam, hphi, ht23, ht34]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3540 | h3540
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3541 | h3541
                      · linarith only [h0, h1, h3464, h3534, h3540, h3541, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h3541, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h1, h3463, h3540, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3545 | h3545
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3546 | h3546
              · linarith only [h0, h3290, h3546, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3548 | h3548
                · linarith only [h0, h1, h3322, h3545, h3548, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3550 | h3550
                  · linarith only [h0, h3324, h3550, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3552 | h3552
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3553 | h3553
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3554 | h3554
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3555 | h3555
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3556 | h3556
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3557 | h3557
                              · rcases h2bigk with h3558c | h3558c | h3558c | h3558c | h3558c | h3558c | h3558c | h3558c | h3558c | h3558c | h3558c | h3558c | h3558c | h3558c | h3558c | h3558c | h3558c | h3558c | h3558c | h3558c | h3558c | h3558c | h3558c | h3558c | h3558c
                                · have p3558_0 := h3558c.1
                                  have p3558_1 := h3558c.2.1
                                  have p3558_2 := h3558c.2.2.1
                                  have p3558_3 := h3558c.2.2.2
                                  linarith only [hlam, p3558_0]
                                · have p3558_0 := h3558c.1
                                  have p3558_1 := h3558c.2.1
                                  have p3558_2 := h3558c.2.2.1
                                  have p3558_3 := h3558c.2.2.2
                                  linarith only [h3324, hc12, hc25, hlam, hphi, p3558_1]
                                · have p3558_0 := h3558c.1
                                  have p3558_1 := h3558c.2.1
                                  have p3558_2 := h3558c.2.2.1
                                  have p3558_3 := h3558c.2.2.2
                                  linarith only [h3290, hlam, p3558_0]
                                · have p3558_0 := h3558c.1
                                  have p3558_1 := h3558c.2.1
                                  have p3558_2 := h3558c.2.2.1
                                  have p3558_3 := h3558c.2.2.2
                                  linarith only [h3322, hlam, p3558_0]
                                · have p3558_0 := h3558c.1
                                  have p3558_1 := h3558c.2.1
                                  have p3558_2 := h3558c.2.2.1
                                  have p3558_3 := h3558c.2.2.2
                                  linarith only [h3324, hlam, p3558_0]
                                · have p3558_0 := h3558c.1
                                  have p3558_1 := h3558c.2.1
                                  have p3558_2 := h3558c.2.2.1
                                  have p3558_3 := h3558c.2.2.2
                                  linarith only [h0, hlam, p3558_0]
                                · have p3558_0 := h3558c.1
                                  have p3558_1 := h3558c.2.1
                                  have p3558_2 := h3558c.2.2.1
                                  have p3558_3 := h3558c.2.2.2
                                  linarith only [hlam, p3558_0]
                                · have p3558_0 := h3558c.1
                                  have p3558_1 := h3558c.2.1
                                  have p3558_2 := h3558c.2.2.1
                                  have p3558_3 := h3558c.2.2.2
                                  linarith only [h3546, hlam, p3558_0]
                                · have p3558_0 := h3558c.1
                                  have p3558_1 := h3558c.2.1
                                  have p3558_2 := h3558c.2.2.1
                                  have p3558_3 := h3558c.2.2.2
                                  linarith only [h3548, hlam, p3558_0]
                                · have p3558_0 := h3558c.1
                                  have p3558_1 := h3558c.2.1
                                  have p3558_2 := h3558c.2.2.1
                                  have p3558_3 := h3558c.2.2.2
                                  linarith only [h3550, hlam, p3558_0]
                                · have p3558_0 := h3558c.1
                                  have p3558_1 := h3558c.2.1
                                  have p3558_2 := h3558c.2.2.1
                                  have p3558_3 := h3558c.2.2.2
                                  linarith only [hc02, hc23, hlam, hphi, p3558_1]
                                · have p3558_0 := h3558c.1
                                  have p3558_1 := h3558c.2.1
                                  have p3558_2 := h3558c.2.2.1
                                  have p3558_3 := h3558c.2.2.2
                                  linarith only [hc12, hc23, hlam, hphi, p3558_1]
                                · have p3558_0 := h3558c.1
                                  have p3558_1 := h3558c.2.1
                                  have p3558_2 := h3558c.2.2.1
                                  have p3558_3 := h3558c.2.2.2
                                  linarith only [hlam, p3558_0]
                                · have p3558_0 := h3558c.1
                                  have p3558_1 := h3558c.2.1
                                  have p3558_2 := h3558c.2.2.1
                                  have p3558_3 := h3558c.2.2.2
                                  linarith only [h0, h3322, hc12, hc23, hlam, hphi, p3558_1]
                                · have p3558_0 := h3558c.1
                                  have p3558_1 := h3558c.2.1
                                  have p3558_2 := h3558c.2.2.1
                                  have p3558_3 := h3558c.2.2.2
                                  linarith only [h0, h3324, hc12, hc23, hlam, hphi, p3558_1]
                                · have p3558_0 := h3558c.1
                                  have p3558_1 := h3558c.2.1
                                  have p3558_2 := h3558c.2.2.1
                                  have p3558_3 := h3558c.2.2.2
                                  linarith only [h0, hc12, hc24, hlam, hphi, p3558_1]
                                · have p3558_0 := h3558c.1
                                  have p3558_1 := h3558c.2.1
                                  have p3558_2 := h3558c.2.2.1
                                  have p3558_3 := h3558c.2.2.2
                                  linarith only [hc12, hc24, hlam, hphi, p3558_1]
                                · have p3558_0 := h3558c.1
                                  have p3558_1 := h3558c.2.1
                                  have p3558_2 := h3558c.2.2.1
                                  have p3558_3 := h3558c.2.2.2
                                  linarith only [h3554, hlam, p3558_1]
                                · have p3558_0 := h3558c.1
                                  have p3558_1 := h3558c.2.1
                                  have p3558_2 := h3558c.2.2.1
                                  have p3558_3 := h3558c.2.2.2
                                  linarith only [hlam, p3558_0]
                                · have p3558_0 := h3558c.1
                                  have p3558_1 := h3558c.2.1
                                  have p3558_2 := h3558c.2.2.1
                                  have p3558_3 := h3558c.2.2.2
                                  linarith only [h0, h3324, h3554, hc12, hc23, hlam, hphi, p3558_1]
                                · have p3558_0 := h3558c.1
                                  have p3558_1 := h3558c.2.1
                                  have p3558_2 := h3558c.2.2.1
                                  have p3558_3 := h3558c.2.2.2
                                  linarith only [h0, hc12, hc25, hlam, hphi, p3558_1]
                                · have p3558_0 := h3558c.1
                                  have p3558_1 := h3558c.2.1
                                  have p3558_2 := h3558c.2.2.1
                                  have p3558_3 := h3558c.2.2.2
                                  linarith only [hc12, hc25, hlam, hphi, p3558_1]
                                · have p3558_0 := h3558c.1
                                  have p3558_1 := h3558c.2.1
                                  have p3558_2 := h3558c.2.2.1
                                  have p3558_3 := h3558c.2.2.2
                                  linarith only [h3555, hlam, p3558_1]
                                · have p3558_0 := h3558c.1
                                  have p3558_1 := h3558c.2.1
                                  have p3558_2 := h3558c.2.2.1
                                  have p3558_3 := h3558c.2.2.2
                                  linarith only [h3556, hlam, p3558_0]
                                · have p3558_0 := h3558c.1
                                  have p3558_1 := h3558c.2.1
                                  have p3558_2 := h3558c.2.2.1
                                  have p3558_3 := h3558c.2.2.2
                                  linarith only [hlam, p3558_0]
                              · linarith only [h0, h1, h3290, h3463, h3545, h3546, h3552, h3557, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h3322, h3463, h3545, h3546, h3552, h3556, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h3463, h3546, h3552, h3555, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h3546, h3552, h3554, hlam]
                      · linarith only [h0, h1, h3545, h3553, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3589 | h3589
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3590 | h3590
                        · linarith only [h0, h1, h3552, h3590, hc12, hc23, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3592 | h3592
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3593 | h3593
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3594 | h3594
                              · rcases h2bigk with h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c
                                · have p3595_0 := h3595c.1
                                  have p3595_1 := h3595c.2.1
                                  have p3595_2 := h3595c.2.2.1
                                  have p3595_3 := h3595c.2.2.2
                                  linarith only [hlam, p3595_0]
                                · have p3595_0 := h3595c.1
                                  have p3595_1 := h3595c.2.1
                                  have p3595_2 := h3595c.2.2.1
                                  have p3595_3 := h3595c.2.2.2
                                  linarith only [h0, h1, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3595_1]
                                · have p3595_0 := h3595c.1
                                  have p3595_1 := h3595c.2.1
                                  have p3595_2 := h3595c.2.2.1
                                  have p3595_3 := h3595c.2.2.2
                                  linarith only [h3290, hlam, p3595_0]
                                · have p3595_0 := h3595c.1
                                  have p3595_1 := h3595c.2.1
                                  have p3595_2 := h3595c.2.2.1
                                  have p3595_3 := h3595c.2.2.2
                                  linarith only [h3322, hlam, p3595_0]
                                · have p3595_0 := h3595c.1
                                  have p3595_1 := h3595c.2.1
                                  have p3595_2 := h3595c.2.2.1
                                  have p3595_3 := h3595c.2.2.2
                                  linarith only [h3324, hlam, p3595_0]
                                · have p3595_0 := h3595c.1
                                  have p3595_1 := h3595c.2.1
                                  have p3595_2 := h3595c.2.2.1
                                  have p3595_3 := h3595c.2.2.2
                                  linarith only [h0, hlam, p3595_0]
                                · have p3595_0 := h3595c.1
                                  have p3595_1 := h3595c.2.1
                                  have p3595_2 := h3595c.2.2.1
                                  have p3595_3 := h3595c.2.2.2
                                  linarith only [hlam, p3595_0]
                                · have p3595_0 := h3595c.1
                                  have p3595_1 := h3595c.2.1
                                  have p3595_2 := h3595c.2.2.1
                                  have p3595_3 := h3595c.2.2.2
                                  linarith only [h3546, hlam, p3595_0]
                                · have p3595_0 := h3595c.1
                                  have p3595_1 := h3595c.2.1
                                  have p3595_2 := h3595c.2.2.1
                                  have p3595_3 := h3595c.2.2.2
                                  linarith only [h3548, hlam, p3595_0]
                                · have p3595_0 := h3595c.1
                                  have p3595_1 := h3595c.2.1
                                  have p3595_2 := h3595c.2.2.1
                                  have p3595_3 := h3595c.2.2.2
                                  linarith only [h3550, hlam, p3595_0]
                                · have p3595_0 := h3595c.1
                                  have p3595_1 := h3595c.2.1
                                  have p3595_2 := h3595c.2.2.1
                                  have p3595_3 := h3595c.2.2.2
                                  linarith only [h3590, hc02, hc34, hlam, hphi, ht23, p3595_1]
                                · have p3595_0 := h3595c.1
                                  have p3595_1 := h3595c.2.1
                                  have p3595_2 := h3595c.2.2.1
                                  have p3595_3 := h3595c.2.2.2
                                  linarith only [h3590, hc12, hc34, hlam, hphi, ht23, p3595_1]
                                · have p3595_0 := h3595c.1
                                  have p3595_1 := h3595c.2.1
                                  have p3595_2 := h3595c.2.2.1
                                  have p3595_3 := h3595c.2.2.2
                                  linarith only [hlam, p3595_0]
                                · have p3595_0 := h3595c.1
                                  have p3595_1 := h3595c.2.1
                                  have p3595_2 := h3595c.2.2.1
                                  have p3595_3 := h3595c.2.2.2
                                  linarith only [h3590, hlam, p3595_0]
                                · have p3595_0 := h3595c.1
                                  have p3595_1 := h3595c.2.1
                                  have p3595_2 := h3595c.2.2.1
                                  have p3595_3 := h3595c.2.2.2
                                  linarith only [h3324, h3590, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3595_1]
                                · have p3595_0 := h3595c.1
                                  have p3595_1 := h3595c.2.1
                                  have p3595_2 := h3595c.2.2.1
                                  have p3595_3 := h3595c.2.2.2
                                  linarith only [h0, h3590, hc12, hc34, hlam, hphi, ht23, p3595_1]
                                · have p3595_0 := h3595c.1
                                  have p3595_1 := h3595c.2.1
                                  have p3595_2 := h3595c.2.2.1
                                  have p3595_3 := h3595c.2.2.2
                                  linarith only [h3590, hc12, hc34, hlam, hphi, ht23, p3595_1]
                                · have p3595_0 := h3595c.1
                                  have p3595_1 := h3595c.2.1
                                  have p3595_2 := h3595c.2.2.1
                                  have p3595_3 := h3595c.2.2.2
                                  linarith only [h3546, h3590, hc13, hc34, hlam, hphi, p3595_1]
                                · have p3595_0 := h3595c.1
                                  have p3595_1 := h3595c.2.1
                                  have p3595_2 := h3595c.2.2.1
                                  have p3595_3 := h3595c.2.2.2
                                  linarith only [hlam, p3595_0]
                                · have p3595_0 := h3595c.1
                                  have p3595_1 := h3595c.2.1
                                  have p3595_2 := h3595c.2.2.1
                                  have p3595_3 := h3595c.2.2.2
                                  linarith only [h0, h3324, h3590, hc12, hc34, hlam, hphi, ht23, p3595_1]
                                · have p3595_0 := h3595c.1
                                  have p3595_1 := h3595c.2.1
                                  have p3595_2 := h3595c.2.2.1
                                  have p3595_3 := h3595c.2.2.2
                                  linarith only [h0, h3592, hc12, hc23, hlam, hphi, p3595_1]
                                · have p3595_0 := h3595c.1
                                  have p3595_1 := h3595c.2.1
                                  have p3595_2 := h3595c.2.2.1
                                  have p3595_3 := h3595c.2.2.2
                                  linarith only [h3592, hc12, hc23, hlam, hphi, p3595_1]
                                · have p3595_0 := h3595c.1
                                  have p3595_1 := h3595c.2.1
                                  have p3595_2 := h3595c.2.2.1
                                  have p3595_3 := h3595c.2.2.2
                                  linarith only [h3592, hlam, p3595_1]
                                · have p3595_0 := h3595c.1
                                  have p3595_1 := h3595c.2.1
                                  have p3595_2 := h3595c.2.2.1
                                  have p3595_3 := h3595c.2.2.2
                                  linarith only [h3593, hlam, p3595_0]
                                · have p3595_0 := h3595c.1
                                  have p3595_1 := h3595c.2.1
                                  have p3595_2 := h3595c.2.2.1
                                  have p3595_3 := h3595c.2.2.2
                                  linarith only [hlam, p3595_0]
                              · linarith only [h0, h1, h3548, h3590, h3594, hc12, hc45, hlam, hphi, ht23, ht34]
                            · linarith only [h1, h3545, h3548, h3593, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3623 | h3623
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3624 | h3624
                              · rcases h2bigk with h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c | h3625c
                                · have p3625_0 := h3625c.1
                                  have p3625_1 := h3625c.2.1
                                  have p3625_2 := h3625c.2.2.1
                                  have p3625_3 := h3625c.2.2.2
                                  linarith only [hlam, p3625_0]
                                · have p3625_0 := h3625c.1
                                  have p3625_1 := h3625c.2.1
                                  have p3625_2 := h3625c.2.2.1
                                  have p3625_3 := h3625c.2.2.2
                                  linarith only [h0, h1, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3625_1]
                                · have p3625_0 := h3625c.1
                                  have p3625_1 := h3625c.2.1
                                  have p3625_2 := h3625c.2.2.1
                                  have p3625_3 := h3625c.2.2.2
                                  linarith only [h3290, hlam, p3625_0]
                                · have p3625_0 := h3625c.1
                                  have p3625_1 := h3625c.2.1
                                  have p3625_2 := h3625c.2.2.1
                                  have p3625_3 := h3625c.2.2.2
                                  linarith only [h3322, hlam, p3625_0]
                                · have p3625_0 := h3625c.1
                                  have p3625_1 := h3625c.2.1
                                  have p3625_2 := h3625c.2.2.1
                                  have p3625_3 := h3625c.2.2.2
                                  linarith only [h3324, hlam, p3625_0]
                                · have p3625_0 := h3625c.1
                                  have p3625_1 := h3625c.2.1
                                  have p3625_2 := h3625c.2.2.1
                                  have p3625_3 := h3625c.2.2.2
                                  linarith only [h0, hlam, p3625_0]
                                · have p3625_0 := h3625c.1
                                  have p3625_1 := h3625c.2.1
                                  have p3625_2 := h3625c.2.2.1
                                  have p3625_3 := h3625c.2.2.2
                                  linarith only [hlam, p3625_0]
                                · have p3625_0 := h3625c.1
                                  have p3625_1 := h3625c.2.1
                                  have p3625_2 := h3625c.2.2.1
                                  have p3625_3 := h3625c.2.2.2
                                  linarith only [h3546, hlam, p3625_0]
                                · have p3625_0 := h3625c.1
                                  have p3625_1 := h3625c.2.1
                                  have p3625_2 := h3625c.2.2.1
                                  have p3625_3 := h3625c.2.2.2
                                  linarith only [h3548, hlam, p3625_0]
                                · have p3625_0 := h3625c.1
                                  have p3625_1 := h3625c.2.1
                                  have p3625_2 := h3625c.2.2.1
                                  have p3625_3 := h3625c.2.2.2
                                  linarith only [h3550, hlam, p3625_0]
                                · have p3625_0 := h3625c.1
                                  have p3625_1 := h3625c.2.1
                                  have p3625_2 := h3625c.2.2.1
                                  have p3625_3 := h3625c.2.2.2
                                  linarith only [h3592, h3624, hc02, hc34, hlam, hphi, ht23, p3625_1]
                                · have p3625_0 := h3625c.1
                                  have p3625_1 := h3625c.2.1
                                  have p3625_2 := h3625c.2.2.1
                                  have p3625_3 := h3625c.2.2.2
                                  linarith only [h3592, h3624, hc12, hc34, hlam, hphi, ht23, p3625_1]
                                · have p3625_0 := h3625c.1
                                  have p3625_1 := h3625c.2.1
                                  have p3625_2 := h3625c.2.2.1
                                  have p3625_3 := h3625c.2.2.2
                                  linarith only [hlam, p3625_0]
                                · have p3625_0 := h3625c.1
                                  have p3625_1 := h3625c.2.1
                                  have p3625_2 := h3625c.2.2.1
                                  have p3625_3 := h3625c.2.2.2
                                  linarith only [h3590, hlam, p3625_0]
                                · have p3625_0 := h3625c.1
                                  have p3625_1 := h3625c.2.1
                                  have p3625_2 := h3625c.2.2.1
                                  have p3625_3 := h3625c.2.2.2
                                  linarith only [h3592, hlam, p3625_0]
                                · have p3625_0 := h3625c.1
                                  have p3625_1 := h3625c.2.1
                                  have p3625_2 := h3625c.2.2.1
                                  have p3625_3 := h3625c.2.2.2
                                  linarith only [h0, h3590, hc12, hc34, hlam, hphi, ht23, p3625_1]
                                · have p3625_0 := h3625c.1
                                  have p3625_1 := h3625c.2.1
                                  have p3625_2 := h3625c.2.2.1
                                  have p3625_3 := h3625c.2.2.2
                                  linarith only [h3590, hc12, hc34, hlam, hphi, ht23, p3625_1]
                                · have p3625_0 := h3625c.1
                                  have p3625_1 := h3625c.2.1
                                  have p3625_2 := h3625c.2.2.1
                                  have p3625_3 := h3625c.2.2.2
                                  linarith only [h3590, hc23, hc34, hlam, hphi, p3625_1]
                                · have p3625_0 := h3625c.1
                                  have p3625_1 := h3625c.2.1
                                  have p3625_2 := h3625c.2.2.1
                                  have p3625_3 := h3625c.2.2.2
                                  linarith only [hlam, p3625_0]
                                · have p3625_0 := h3625c.1
                                  have p3625_1 := h3625c.2.1
                                  have p3625_2 := h3625c.2.2.1
                                  have p3625_3 := h3625c.2.2.2
                                  linarith only [h0, h3324, h3590, hc12, hc34, hlam, hphi, ht23, p3625_1]
                                · have p3625_0 := h3625c.1
                                  have p3625_1 := h3625c.2.1
                                  have p3625_2 := h3625c.2.2.1
                                  have p3625_3 := h3625c.2.2.2
                                  linarith only [h0, hc12, hc25, hlam, hphi, p3625_1]
                                · have p3625_0 := h3625c.1
                                  have p3625_1 := h3625c.2.1
                                  have p3625_2 := h3625c.2.2.1
                                  have p3625_3 := h3625c.2.2.2
                                  linarith only [hc12, hc25, hlam, hphi, p3625_1]
                                · have p3625_0 := h3625c.1
                                  have p3625_1 := h3625c.2.1
                                  have p3625_2 := h3625c.2.2.1
                                  have p3625_3 := h3625c.2.2.2
                                  linarith only [h0, h3290, h3592, h3624, hc12, hc34, hlam, hphi, ht23, p3625_1]
                                · have p3625_0 := h3625c.1
                                  have p3625_1 := h3625c.2.1
                                  have p3625_2 := h3625c.2.2.1
                                  have p3625_3 := h3625c.2.2.2
                                  linarith only [h3623, hlam, p3625_0]
                                · have p3625_0 := h3625c.1
                                  have p3625_1 := h3625c.2.1
                                  have p3625_2 := h3625c.2.2.1
                                  have p3625_3 := h3625c.2.2.2
                                  linarith only [hlam, p3625_0]
                              · linarith only [h1, h3545, h3548, h3590, h3624, hlam]
                            · linarith only [h1, h3545, h3548, h3623, hlam]
                      · linarith only [h1, h3545, h3589, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3654 | h3654
              · linarith only [h0, h3290, h3654, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3656 | h3656
                · linarith only [h0, h1, h3545, h3656, hc24, hc45, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3658 | h3658
                  · linarith only [h0, h3324, h3658, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3660 | h3660
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3661 | h3661
                      · linarith only [h0, h1, h3545, h3656, h3661, hc12, hc24, hlam, hphi]
                      · linarith only [h0, h1, h3661, hc12, hc45, hlam, hphi, ht23, ht34]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3664 | h3664
                      · linarith only [h0, h1, h3545, h3660, h3664, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h1, h3664, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
