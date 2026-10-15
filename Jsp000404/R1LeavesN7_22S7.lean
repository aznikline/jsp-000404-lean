import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_22S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7216000 in
set_option maxHeartbeats 7216000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s1 m hb0 hb2 hb3 hb5 h0 h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h3295 | h3295
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3296 | h3296
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3297 | h3297
        · linarith only [h0, h1, h3297, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h3299 | h3299
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3300 | h3300
            · rcases m.htr 0 3 4 (by decide) (by decide) with h3301 | h3301
              · rcases m.htr 0 3 5 (by decide) (by decide) with h3302 | h3302
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3303 | h3303
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3304 | h3304
                    · linarith only [h0, h1, h3297, h3304, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3306 | h3306
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h3307 | h3307
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h3308 | h3308
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h3309 | h3309
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h3310 | h3310
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h3311 | h3311
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h3312 | h3312
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3313 | h3313
                                    · linarith only [h0, h1, h3304, h3306, h3313, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                    · linarith only [h3313, hc24, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h0, h1, h3304, h3312, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h0, h1, h3304, h3306, h3310, h3311, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h3310, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h0, h1, h3306, h3309, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1, h3306, h3308, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h3306, h3307, hc24, hlam, hphi, ht45, u5elo2]
                      · linarith only [h0, h1, h3299, h3304, h3306, hc12, hc23, hlam, hphi]
                  · linarith only [h3303, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h1, h3302, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · linarith only [h1, h3295, h3301, hlam]
            · linarith only [h3299, h3300, hc24, hlam, hphi, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3327 | h3327
            · rcases m.htr 0 3 4 (by decide) (by decide) with h3328 | h3328
              · rcases m.htr 0 3 5 (by decide) (by decide) with h3329 | h3329
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3330 | h3330
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3331 | h3331
                    · linarith only [h0, h1, h3297, h3331, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3333 | h3333
                      · linarith only [h0, h1, h3299, h3327, h3331, h3333, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h3335 | h3335
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h3336 | h3336
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h3337 | h3337
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h3338 | h3338
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h3339 | h3339
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h3340 | h3340
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3341 | h3341
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3342 | h3342
                                      · rcases h0bigk with h3343c | h3343c | h3343c | h3343c | h3343c | h3343c | h3343c | h3343c | h3343c | h3343c | h3343c | h3343c | h3343c | h3343c | h3343c | h3343c | h3343c | h3343c | h3343c | h3343c | h3343c | h3343c | h3343c | h3343c | h3343c
                                        · have p3343_0 := h3343c.1
                                          have p3343_1 := h3343c.2.1
                                          have p3343_2 := h3343c.2.2.1
                                          have p3343_3 := h3343c.2.2.2
                                          linarith only [hlam, p3343_0]
                                        · have p3343_0 := h3343c.1
                                          have p3343_1 := h3343c.2.1
                                          have p3343_2 := h3343c.2.2.1
                                          have p3343_3 := h3343c.2.2.2
                                          linarith only [h0, h1, h3331, h3335, h3340, h3342, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3343_1]
                                        · have p3343_0 := h3343c.1
                                          have p3343_1 := h3343c.2.1
                                          have p3343_2 := h3343c.2.2.1
                                          have p3343_3 := h3343c.2.2.2
                                          linarith only [h1, hlam, p3343_0]
                                        · have p3343_0 := h3343c.1
                                          have p3343_1 := h3343c.2.1
                                          have p3343_2 := h3343c.2.2.1
                                          have p3343_3 := h3343c.2.2.2
                                          linarith only [h0, h1, h3299, h3331, h3335, h3340, h3342, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3343_1]
                                        · have p3343_0 := h3343c.1
                                          have p3343_1 := h3343c.2.1
                                          have p3343_2 := h3343c.2.2.1
                                          have p3343_3 := h3343c.2.2.2
                                          rcases p3343_3 (m.d 0 1) (by simp) with h3348 | h3348
                                          · rcases p3343_3 (m.d 0 2) (by simp) with h3349 | h3349
                                            · linarith only [h0, h3349, hlam]
                                            · linarith only [h3327, h3349, hlam]
                                          · linarith only [h3296, h3348, hlam]
                                        · have p3343_0 := h3343c.1
                                          have p3343_1 := h3343c.2.1
                                          have p3343_2 := h3343c.2.2.1
                                          have p3343_3 := h3343c.2.2.2
                                          linarith only [h0, hlam, p3343_0]
                                        · have p3343_0 := h3343c.1
                                          have p3343_1 := h3343c.2.1
                                          have p3343_2 := h3343c.2.2.1
                                          have p3343_3 := h3343c.2.2.2
                                          linarith only [hlam, p3343_0]
                                        · have p3343_0 := h3343c.1
                                          have p3343_1 := h3343c.2.1
                                          have p3343_2 := h3343c.2.2.1
                                          have p3343_3 := h3343c.2.2.2
                                          linarith only [h3297, hlam, p3343_0]
                                        · have p3343_0 := h3343c.1
                                          have p3343_1 := h3343c.2.1
                                          have p3343_2 := h3343c.2.2.1
                                          have p3343_3 := h3343c.2.2.2
                                          linarith only [h3299, hlam, p3343_1]
                                        · have p3343_0 := h3343c.1
                                          have p3343_1 := h3343c.2.1
                                          have p3343_2 := h3343c.2.2.1
                                          have p3343_3 := h3343c.2.2.2
                                          rcases p3343_3 (m.d 0 1) (by simp) with h3357 | h3357
                                          · rcases p3343_3 (m.d 0 2) (by simp) with h3358 | h3358
                                            · rcases p3343_3 (m.d 0 3) (by simp) with h3359 | h3359
                                              · rcases p3343_3 (m.d 0 4) (by simp) with h3360 | h3360
                                                · rcases p3343_3 (m.d 0 5) (by simp) with h3361 | h3361
                                                  · linarith only [h3327, h3361, hlam]
                                                  · rcases h0emin with h3363 | h3363 | h3363 | h3363 | h3363
                                                    · linarith only [h1, h3331, h3363, hc23, hlam, ht01, ht12]
                                                    · linarith only [h3299, h3363, hc24, hlam, ht01, ht12]
                                                    · rcases h2bigk with h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c | h3366c
                                                      · have p3366_0 := h3366c.1
                                                        have p3366_1 := h3366c.2.1
                                                        have p3366_2 := h3366c.2.2.1
                                                        have p3366_3 := h3366c.2.2.2
                                                        linarith only [hlam, p3366_0]
                                                      · have p3366_0 := h3366c.1
                                                        have p3366_1 := h3366c.2.1
                                                        have p3366_2 := h3366c.2.2.1
                                                        have p3366_3 := h3366c.2.2.2
                                                        linarith only [h1, h3295, h3299, h3331, h3335, h3340, h3342, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3366_1]
                                                      · have p3366_0 := h3366c.1
                                                        have p3366_1 := h3366c.2.1
                                                        have p3366_2 := h3366c.2.2.1
                                                        have p3366_3 := h3366c.2.2.2
                                                        linarith only [h3297, hlam, p3366_0]
                                                      · have p3366_0 := h3366c.1
                                                        have p3366_1 := h3366c.2.1
                                                        have p3366_2 := h3366c.2.2.1
                                                        have p3366_3 := h3366c.2.2.2
                                                        linarith only [h3299, hlam, p3366_0]
                                                      · have p3366_0 := h3366c.1
                                                        have p3366_1 := h3366c.2.1
                                                        have p3366_2 := h3366c.2.2.1
                                                        have p3366_3 := h3366c.2.2.2
                                                        rcases p3366_3 (m.d 0 2) (by simp) with h3371 | h3371
                                                        · rcases p3366_3 (m.d 1 2) (by simp) with h3372 | h3372
                                                          · linarith only [h0, h3372, hlam]
                                                          · linarith only [h3335, h3372, hlam]
                                                        · linarith only [h3371, hlam, p3366_0]
                                                      · have p3366_0 := h3366c.1
                                                        have p3366_1 := h3366c.2.1
                                                        have p3366_2 := h3366c.2.2.1
                                                        have p3366_3 := h3366c.2.2.2
                                                        linarith only [h0, hlam, p3366_0]
                                                      · have p3366_0 := h3366c.1
                                                        have p3366_1 := h3366c.2.1
                                                        have p3366_2 := h3366c.2.2.1
                                                        have p3366_3 := h3366c.2.2.2
                                                        linarith only [hlam, p3366_0]
                                                      · have p3366_0 := h3366c.1
                                                        have p3366_1 := h3366c.2.1
                                                        have p3366_2 := h3366c.2.2.1
                                                        have p3366_3 := h3366c.2.2.2
                                                        linarith only [h3331, hlam, p3366_0]
                                                      · have p3366_0 := h3366c.1
                                                        have p3366_1 := h3366c.2.1
                                                        have p3366_2 := h3366c.2.2.1
                                                        have p3366_3 := h3366c.2.2.2
                                                        linarith only [h3333, hlam, p3366_0]
                                                      · have p3366_0 := h3366c.1
                                                        have p3366_1 := h3366c.2.1
                                                        have p3366_2 := h3366c.2.2.1
                                                        have p3366_3 := h3366c.2.2.2
                                                        linarith only [h0, h1, h3331, h3340, h3342, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3366_1]
                                                      · have p3366_0 := h3366c.1
                                                        have p3366_1 := h3366c.2.1
                                                        have p3366_2 := h3366c.2.2.1
                                                        have p3366_3 := h3366c.2.2.2
                                                        linarith only [h3296, h3335, h3340, h3342, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3343_1, p3366_1]
                                                      · have p3366_0 := h3366c.1
                                                        have p3366_1 := h3366c.2.1
                                                        have p3366_2 := h3366c.2.2.1
                                                        have p3366_3 := h3366c.2.2.2
                                                        rcases p3366_3 (m.d 0 2) (by simp) with h3382 | h3382
                                                        · linarith only [h3297, h3382, hlam]
                                                        · linarith only [h0, h3382, hlam]
                                                      · have p3366_0 := h3366c.1
                                                        have p3366_1 := h3366c.2.1
                                                        have p3366_2 := h3366c.2.2.1
                                                        have p3366_3 := h3366c.2.2.2
                                                        linarith only [hlam, p3366_0]
                                                      · have p3366_0 := h3366c.1
                                                        have p3366_1 := h3366c.2.1
                                                        have p3366_2 := h3366c.2.2.1
                                                        have p3366_3 := h3366c.2.2.2
                                                        linarith only [h3296, h3299, h3335, h3340, h3342, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3343_1, p3366_1]
                                                      · have p3366_0 := h3366c.1
                                                        have p3366_1 := h3366c.2.1
                                                        have p3366_2 := h3366c.2.2.1
                                                        have p3366_3 := h3366c.2.2.2
                                                        linarith only [h0, h1, h3296, h3331, h3335, hlam, p3343_1, p3366_2]
                                                      · have p3366_0 := h3366c.1
                                                        have p3366_1 := h3366c.2.1
                                                        have p3366_2 := h3366c.2.2.1
                                                        have p3366_3 := h3366c.2.2.2
                                                        linarith only [hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p3343_1, p3366_1]
                                                      · have p3366_0 := h3366c.1
                                                        have p3366_1 := h3366c.2.1
                                                        have p3366_2 := h3366c.2.2.1
                                                        have p3366_3 := h3366c.2.2.2
                                                        rcases p3366_3 (m.d 0 2) (by simp) with h3389 | h3389
                                                        · linarith only [h3299, h3389, hlam]
                                                        · linarith only [h0, h3389, hlam]
                                                      · have p3366_0 := h3366c.1
                                                        have p3366_1 := h3366c.2.1
                                                        have p3366_2 := h3366c.2.2.1
                                                        have p3366_3 := h3366c.2.2.2
                                                        linarith only [h3339, hlam, p3366_1]
                                                      · have p3366_0 := h3366c.1
                                                        have p3366_1 := h3366c.2.1
                                                        have p3366_2 := h3366c.2.2.1
                                                        have p3366_3 := h3366c.2.2.2
                                                        linarith only [hlam, p3366_0]
                                                      · have p3366_0 := h3366c.1
                                                        have p3366_1 := h3366c.2.1
                                                        have p3366_2 := h3366c.2.2.1
                                                        have p3366_3 := h3366c.2.2.2
                                                        linarith only [h3296, h3299, h3335, hlam, p3343_1, p3366_2]
                                                      · have p3366_0 := h3366c.1
                                                        have p3366_1 := h3366c.2.1
                                                        have p3366_2 := h3366c.2.2.1
                                                        have p3366_3 := h3366c.2.2.2
                                                        linarith only [h3327, hlam, p3366_0]
                                                      · have p3366_0 := h3366c.1
                                                        have p3366_1 := h3366c.2.1
                                                        have p3366_2 := h3366c.2.2.1
                                                        have p3366_3 := h3366c.2.2.2
                                                        linarith only [h3335, hlam, p3366_0]
                                                      · have p3366_0 := h3366c.1
                                                        have p3366_1 := h3366c.2.1
                                                        have p3366_2 := h3366c.2.2.1
                                                        have p3366_3 := h3366c.2.2.2
                                                        linarith only [h3340, hlam, p3366_1]
                                                      · have p3366_0 := h3366c.1
                                                        have p3366_1 := h3366c.2.1
                                                        have p3366_2 := h3366c.2.2.1
                                                        have p3366_3 := h3366c.2.2.2
                                                        linarith only [h3341, hlam, p3366_0]
                                                      · have p3366_0 := h3366c.1
                                                        have p3366_1 := h3366c.2.1
                                                        have p3366_2 := h3366c.2.2.1
                                                        have p3366_3 := h3366c.2.2.2
                                                        linarith only [hlam, p3366_0]
                                                    · linarith only [h1, h3295, h3363, hc13, hlam, ht01]
                                                    · linarith only [h3295, h3299, h3363, hc01, hlam, p3343_1]
                                                · linarith only [h3330, h3360, hlam]
                                              · linarith only [h3329, h3359, hlam]
                                            · linarith only [h3327, h3358, hlam]
                                          · linarith only [h3296, h3357, hlam]
                                        · have p3343_0 := h3343c.1
                                          have p3343_1 := h3343c.2.1
                                          have p3343_2 := h3343c.2.2.1
                                          have p3343_3 := h3343c.2.2.2
                                          linarith only [h1, h3295, h3331, h3333, hc12, hc23, hlam, hphi, p3343_1]
                                        · have p3343_0 := h3343c.1
                                          have p3343_1 := h3343c.2.1
                                          have p3343_2 := h3343c.2.2.1
                                          have p3343_3 := h3343c.2.2.2
                                          rcases p3343_3 (m.d 0 1) (by simp) with h3407 | h3407
                                          · linarith only [h1, h3407, hlam]
                                          · linarith only [h0, h3407, hlam]
                                        · have p3343_0 := h3343c.1
                                          have p3343_1 := h3343c.2.1
                                          have p3343_2 := h3343c.2.2.1
                                          have p3343_3 := h3343c.2.2.2
                                          linarith only [hlam, p3343_0]
                                        · have p3343_0 := h3343c.1
                                          have p3343_1 := h3343c.2.1
                                          have p3343_2 := h3343c.2.2.1
                                          have p3343_3 := h3343c.2.2.2
                                          rcases p3343_3 (m.d 0 1) (by simp) with h3411 | h3411
                                          · linarith only [h1, h3411, hlam]
                                          · linarith only [h3295, h3411, hlam]
                                        · have p3343_0 := h3343c.1
                                          have p3343_1 := h3343c.2.1
                                          have p3343_2 := h3343c.2.2.1
                                          have p3343_3 := h3343c.2.2.2
                                          rcases p3343_3 (m.d 0 1) (by simp) with h3414 | h3414
                                          · linarith only [h1, h3414, hlam]
                                          · linarith only [h3296, h3414, hlam]
                                        · have p3343_0 := h3343c.1
                                          have p3343_1 := h3343c.2.1
                                          have p3343_2 := h3343c.2.2.1
                                          have p3343_3 := h3343c.2.2.2
                                          linarith only [h3295, hlam, p3343_0]
                                        · have p3343_0 := h3343c.1
                                          have p3343_1 := h3343c.2.1
                                          have p3343_2 := h3343c.2.2.1
                                          have p3343_3 := h3343c.2.2.2
                                          linarith only [h0, h1, h3295, h3331, h3335, h3340, h3342, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3343_1]
                                        · have p3343_0 := h3343c.1
                                          have p3343_1 := h3343c.2.1
                                          have p3343_2 := h3343c.2.2.1
                                          have p3343_3 := h3343c.2.2.2
                                          linarith only [h3328, hlam, p3343_0]
                                        · have p3343_0 := h3343c.1
                                          have p3343_1 := h3343c.2.1
                                          have p3343_2 := h3343c.2.2.1
                                          have p3343_3 := h3343c.2.2.2
                                          linarith only [hlam, p3343_0]
                                        · have p3343_0 := h3343c.1
                                          have p3343_1 := h3343c.2.1
                                          have p3343_2 := h3343c.2.2.1
                                          have p3343_3 := h3343c.2.2.2
                                          rcases p3343_3 (m.d 0 1) (by simp) with h3421 | h3421
                                          · rcases p3343_3 (m.d 0 2) (by simp) with h3422 | h3422
                                            · linarith only [h3299, h3422, hlam]
                                            · linarith only [h3327, h3422, hlam]
                                          · linarith only [h3296, h3421, hlam]
                                        · have p3343_0 := h3343c.1
                                          have p3343_1 := h3343c.2.1
                                          have p3343_2 := h3343c.2.2.1
                                          have p3343_3 := h3343c.2.2.2
                                          linarith only [h3296, hlam, p3343_0]
                                        · have p3343_0 := h3343c.1
                                          have p3343_1 := h3343c.2.1
                                          have p3343_2 := h3343c.2.2.1
                                          have p3343_3 := h3343c.2.2.2
                                          linarith only [h3327, hlam, p3343_1]
                                        · have p3343_0 := h3343c.1
                                          have p3343_1 := h3343c.2.1
                                          have p3343_2 := h3343c.2.2.1
                                          have p3343_3 := h3343c.2.2.2
                                          linarith only [h3329, hlam, p3343_0]
                                        · have p3343_0 := h3343c.1
                                          have p3343_1 := h3343c.2.1
                                          have p3343_2 := h3343c.2.2.1
                                          have p3343_3 := h3343c.2.2.2
                                          linarith only [h3330, hlam, p3343_1]
                                        · have p3343_0 := h3343c.1
                                          have p3343_1 := h3343c.2.1
                                          have p3343_2 := h3343c.2.2.1
                                          have p3343_3 := h3343c.2.2.2
                                          linarith only [hlam, p3343_0]
                                      · linarith only [h3342, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h1, h3295, h3331, h3338, h3341, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · linarith only [h1, h3295, h3331, h3333, h3340, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h1, h3295, h3331, h3333, h3335, h3339, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h3333, h3335, h3338, hc25, hlam, hphi, u5elo4]
                            · linarith only [h1, h3295, h3333, h3335, h3337, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h1, h3295, h3333, h3335, h3336, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h3335, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h3330, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h3329, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h1, h3295, h3328, hlam]
            · linarith only [h3327, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
      · linarith only [h0, h3296, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3444 | h3444
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3445 | h3445
        · linarith only [h0, h1, h3445, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h3447 | h3447
          · linarith only [h0, h3295, h3447, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3449 | h3449
            · rcases m.htr 0 3 4 (by decide) (by decide) with h3450 | h3450
              · rcases m.htr 0 3 5 (by decide) (by decide) with h3451 | h3451
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3452 | h3452
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3453 | h3453
                    · linarith only [h0, h1, h3445, h3453, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3455 | h3455
                      · linarith only [h0, h3295, h3447, h3455, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h3457 | h3457
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h3458 | h3458
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h3459 | h3459
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h3460 | h3460
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h3461 | h3461
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h3462 | h3462
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3463 | h3463
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3464 | h3464
                                      · rcases h0bigk with h3465c | h3465c | h3465c | h3465c | h3465c | h3465c | h3465c | h3465c | h3465c | h3465c | h3465c | h3465c | h3465c | h3465c | h3465c | h3465c | h3465c | h3465c | h3465c | h3465c | h3465c | h3465c | h3465c | h3465c | h3465c
                                        · have p3465_0 := h3465c.1
                                          have p3465_1 := h3465c.2.1
                                          have p3465_2 := h3465c.2.2.1
                                          have p3465_3 := h3465c.2.2.2
                                          linarith only [hlam, p3465_0]
                                        · have p3465_0 := h3465c.1
                                          have p3465_1 := h3465c.2.1
                                          have p3465_2 := h3465c.2.2.1
                                          have p3465_3 := h3465c.2.2.2
                                          linarith only [h3295, h3453, h3458, hc02, hc23, hlam, hphi, p3465_1]
                                        · have p3465_0 := h3465c.1
                                          have p3465_1 := h3465c.2.1
                                          have p3465_2 := h3465c.2.2.1
                                          have p3465_3 := h3465c.2.2.2
                                          linarith only [h1, hlam, p3465_0]
                                        · have p3465_0 := h3465c.1
                                          have p3465_1 := h3465c.2.1
                                          have p3465_2 := h3465c.2.2.1
                                          have p3465_3 := h3465c.2.2.2
                                          linarith only [h3295, hlam, p3465_1]
                                        · have p3465_0 := h3465c.1
                                          have p3465_1 := h3465c.2.1
                                          have p3465_2 := h3465c.2.2.1
                                          have p3465_3 := h3465c.2.2.2
                                          rcases p3465_3 (m.d 0 1) (by simp) with h3470 | h3470
                                          · rcases p3465_3 (m.d 0 2) (by simp) with h3471 | h3471
                                            · linarith only [h0, h3471, hlam]
                                            · linarith only [h3449, h3471, hlam]
                                          · linarith only [h3444, h3470, hlam]
                                        · have p3465_0 := h3465c.1
                                          have p3465_1 := h3465c.2.1
                                          have p3465_2 := h3465c.2.2.1
                                          have p3465_3 := h3465c.2.2.2
                                          linarith only [h0, hlam, p3465_0]
                                        · have p3465_0 := h3465c.1
                                          have p3465_1 := h3465c.2.1
                                          have p3465_2 := h3465c.2.2.1
                                          have p3465_3 := h3465c.2.2.2
                                          linarith only [hlam, p3465_0]
                                        · have p3465_0 := h3465c.1
                                          have p3465_1 := h3465c.2.1
                                          have p3465_2 := h3465c.2.2.1
                                          have p3465_3 := h3465c.2.2.2
                                          linarith only [h3445, hlam, p3465_0]
                                        · have p3465_0 := h3465c.1
                                          have p3465_1 := h3465c.2.1
                                          have p3465_2 := h3465c.2.2.1
                                          have p3465_3 := h3465c.2.2.2
                                          linarith only [h3447, hlam, p3465_1]
                                        · have p3465_0 := h3465c.1
                                          have p3465_1 := h3465c.2.1
                                          have p3465_2 := h3465c.2.2.1
                                          have p3465_3 := h3465c.2.2.2
                                          rcases p3465_3 (m.d 0 1) (by simp) with h3479 | h3479
                                          · rcases p3465_3 (m.d 0 2) (by simp) with h3480 | h3480
                                            · rcases p3465_3 (m.d 0 3) (by simp) with h3481 | h3481
                                              · rcases p3465_3 (m.d 0 4) (by simp) with h3482 | h3482
                                                · rcases p3465_3 (m.d 0 5) (by simp) with h3483 | h3483
                                                  · linarith only [h3449, h3483, hlam]
                                                  · rcases h0emin with h3485 | h3485 | h3485 | h3485 | h3485
                                                    · linarith only [h3295, h3453, h3458, h3485, hc23, hlam, ht01, ht12]
                                                    · linarith only [h0, h3295, h3453, h3458, h3485, hc23, hlam, ht01, ht12]
                                                    · rcases h2bigk with h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c | h3488c
                                                      · have p3488_0 := h3488c.1
                                                        have p3488_1 := h3488c.2.1
                                                        have p3488_2 := h3488c.2.2.1
                                                        have p3488_3 := h3488c.2.2.2
                                                        linarith only [hlam, p3488_0]
                                                      · have p3488_0 := h3488c.1
                                                        have p3488_1 := h3488c.2.1
                                                        have p3488_2 := h3488c.2.2.1
                                                        have p3488_3 := h3488c.2.2.2
                                                        linarith only [h0, h3295, h3453, h3458, hc12, hc23, hlam, hphi, p3488_1]
                                                      · have p3488_0 := h3488c.1
                                                        have p3488_1 := h3488c.2.1
                                                        have p3488_2 := h3488c.2.2.1
                                                        have p3488_3 := h3488c.2.2.2
                                                        linarith only [h3445, hlam, p3488_0]
                                                      · have p3488_0 := h3488c.1
                                                        have p3488_1 := h3488c.2.1
                                                        have p3488_2 := h3488c.2.2.1
                                                        have p3488_3 := h3488c.2.2.2
                                                        linarith only [h3447, hlam, p3488_0]
                                                      · have p3488_0 := h3488c.1
                                                        have p3488_1 := h3488c.2.1
                                                        have p3488_2 := h3488c.2.2.1
                                                        have p3488_3 := h3488c.2.2.2
                                                        rcases p3488_3 (m.d 0 2) (by simp) with h3493 | h3493
                                                        · rcases p3488_3 (m.d 1 2) (by simp) with h3494 | h3494
                                                          · linarith only [h0, h3494, hlam]
                                                          · linarith only [h3457, h3494, hlam]
                                                        · linarith only [h3493, hlam, p3488_0]
                                                      · have p3488_0 := h3488c.1
                                                        have p3488_1 := h3488c.2.1
                                                        have p3488_2 := h3488c.2.2.1
                                                        have p3488_3 := h3488c.2.2.2
                                                        linarith only [h0, hlam, p3488_0]
                                                      · have p3488_0 := h3488c.1
                                                        have p3488_1 := h3488c.2.1
                                                        have p3488_2 := h3488c.2.2.1
                                                        have p3488_3 := h3488c.2.2.2
                                                        linarith only [hlam, p3488_0]
                                                      · have p3488_0 := h3488c.1
                                                        have p3488_1 := h3488c.2.1
                                                        have p3488_2 := h3488c.2.2.1
                                                        have p3488_3 := h3488c.2.2.2
                                                        linarith only [h3453, hlam, p3488_0]
                                                      · have p3488_0 := h3488c.1
                                                        have p3488_1 := h3488c.2.1
                                                        have p3488_2 := h3488c.2.2.1
                                                        have p3488_3 := h3488c.2.2.2
                                                        linarith only [h3455, hlam, p3488_0]
                                                      · have p3488_0 := h3488c.1
                                                        have p3488_1 := h3488c.2.1
                                                        have p3488_2 := h3488c.2.2.1
                                                        have p3488_3 := h3488c.2.2.2
                                                        linarith only [h0, h3295, h3453, h3458, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p3488_1]
                                                      · have p3488_0 := h3488c.1
                                                        have p3488_1 := h3488c.2.1
                                                        have p3488_2 := h3488c.2.2.1
                                                        have p3488_3 := h3488c.2.2.2
                                                        linarith only [hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3465_1, p3488_1]
                                                      · have p3488_0 := h3488c.1
                                                        have p3488_1 := h3488c.2.1
                                                        have p3488_2 := h3488c.2.2.1
                                                        have p3488_3 := h3488c.2.2.2
                                                        rcases p3488_3 (m.d 0 2) (by simp) with h3504 | h3504
                                                        · linarith only [h3445, h3504, hlam]
                                                        · linarith only [h0, h3504, hlam]
                                                      · have p3488_0 := h3488c.1
                                                        have p3488_1 := h3488c.2.1
                                                        have p3488_2 := h3488c.2.2.1
                                                        have p3488_3 := h3488c.2.2.2
                                                        linarith only [hlam, p3488_0]
                                                      · have p3488_0 := h3488c.1
                                                        have p3488_1 := h3488c.2.1
                                                        have p3488_2 := h3488c.2.2.1
                                                        have p3488_3 := h3488c.2.2.2
                                                        linarith only [h3295, h3455, hc01, hc23, hlam, hphi, ht12, p3488_1]
                                                      · have p3488_0 := h3488c.1
                                                        have p3488_1 := h3488c.2.1
                                                        have p3488_2 := h3488c.2.2.1
                                                        have p3488_3 := h3488c.2.2.2
                                                        linarith only [h0, h3295, h3444, h3453, h3457, h3458, hlam, p3465_1, p3488_2]
                                                      · have p3488_0 := h3488c.1
                                                        have p3488_1 := h3488c.2.1
                                                        have p3488_2 := h3488c.2.2.1
                                                        have p3488_3 := h3488c.2.2.2
                                                        linarith only [h3444, h3457, h3462, h3464, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3465_1, p3488_1]
                                                      · have p3488_0 := h3488c.1
                                                        have p3488_1 := h3488c.2.1
                                                        have p3488_2 := h3488c.2.2.1
                                                        have p3488_3 := h3488c.2.2.2
                                                        rcases p3488_3 (m.d 0 2) (by simp) with h3511 | h3511
                                                        · linarith only [h3447, h3511, hlam]
                                                        · linarith only [h0, h3511, hlam]
                                                      · have p3488_0 := h3488c.1
                                                        have p3488_1 := h3488c.2.1
                                                        have p3488_2 := h3488c.2.2.1
                                                        have p3488_3 := h3488c.2.2.2
                                                        linarith only [h3461, hlam, p3488_1]
                                                      · have p3488_0 := h3488c.1
                                                        have p3488_1 := h3488c.2.1
                                                        have p3488_2 := h3488c.2.2.1
                                                        have p3488_3 := h3488c.2.2.2
                                                        linarith only [hlam, p3488_0]
                                                      · have p3488_0 := h3488c.1
                                                        have p3488_1 := h3488c.2.1
                                                        have p3488_2 := h3488c.2.2.1
                                                        have p3488_3 := h3488c.2.2.2
                                                        linarith only [h3444, h3447, h3457, hlam, p3465_1, p3488_2]
                                                      · have p3488_0 := h3488c.1
                                                        have p3488_1 := h3488c.2.1
                                                        have p3488_2 := h3488c.2.2.1
                                                        have p3488_3 := h3488c.2.2.2
                                                        linarith only [h3449, hlam, p3488_0]
                                                      · have p3488_0 := h3488c.1
                                                        have p3488_1 := h3488c.2.1
                                                        have p3488_2 := h3488c.2.2.1
                                                        have p3488_3 := h3488c.2.2.2
                                                        linarith only [h3457, hlam, p3488_0]
                                                      · have p3488_0 := h3488c.1
                                                        have p3488_1 := h3488c.2.1
                                                        have p3488_2 := h3488c.2.2.1
                                                        have p3488_3 := h3488c.2.2.2
                                                        linarith only [h3462, hlam, p3488_1]
                                                      · have p3488_0 := h3488c.1
                                                        have p3488_1 := h3488c.2.1
                                                        have p3488_2 := h3488c.2.2.1
                                                        have p3488_3 := h3488c.2.2.2
                                                        linarith only [h3463, hlam, p3488_0]
                                                      · have p3488_0 := h3488c.1
                                                        have p3488_1 := h3488c.2.1
                                                        have p3488_2 := h3488c.2.2.1
                                                        have p3488_3 := h3488c.2.2.2
                                                        linarith only [hlam, p3488_0]
                                                    · rcases h2bigk with h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c
                                                      · have p3522_0 := h3522c.1
                                                        have p3522_1 := h3522c.2.1
                                                        have p3522_2 := h3522c.2.2.1
                                                        have p3522_3 := h3522c.2.2.2
                                                        linarith only [hlam, p3522_0]
                                                      · have p3522_0 := h3522c.1
                                                        have p3522_1 := h3522c.2.1
                                                        have p3522_2 := h3522c.2.2.1
                                                        have p3522_3 := h3522c.2.2.2
                                                        linarith only [h0, h3295, h3457, h3458, h3462, h3464, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p3522_1]
                                                      · have p3522_0 := h3522c.1
                                                        have p3522_1 := h3522c.2.1
                                                        have p3522_2 := h3522c.2.2.1
                                                        have p3522_3 := h3522c.2.2.2
                                                        linarith only [h3445, hlam, p3522_0]
                                                      · have p3522_0 := h3522c.1
                                                        have p3522_1 := h3522c.2.1
                                                        have p3522_2 := h3522c.2.2.1
                                                        have p3522_3 := h3522c.2.2.2
                                                        linarith only [h3447, hlam, p3522_0]
                                                      · have p3522_0 := h3522c.1
                                                        have p3522_1 := h3522c.2.1
                                                        have p3522_2 := h3522c.2.2.1
                                                        have p3522_3 := h3522c.2.2.2
                                                        rcases p3522_3 (m.d 0 2) (by simp) with h3527 | h3527
                                                        · rcases p3522_3 (m.d 1 2) (by simp) with h3528 | h3528
                                                          · linarith only [h0, h3528, hlam]
                                                          · linarith only [h3457, h3528, hlam]
                                                        · linarith only [h3527, hlam, p3522_0]
                                                      · have p3522_0 := h3522c.1
                                                        have p3522_1 := h3522c.2.1
                                                        have p3522_2 := h3522c.2.2.1
                                                        have p3522_3 := h3522c.2.2.2
                                                        linarith only [h0, hlam, p3522_0]
                                                      · have p3522_0 := h3522c.1
                                                        have p3522_1 := h3522c.2.1
                                                        have p3522_2 := h3522c.2.2.1
                                                        have p3522_3 := h3522c.2.2.2
                                                        linarith only [hlam, p3522_0]
                                                      · have p3522_0 := h3522c.1
                                                        have p3522_1 := h3522c.2.1
                                                        have p3522_2 := h3522c.2.2.1
                                                        have p3522_3 := h3522c.2.2.2
                                                        linarith only [h3453, hlam, p3522_0]
                                                      · have p3522_0 := h3522c.1
                                                        have p3522_1 := h3522c.2.1
                                                        have p3522_2 := h3522c.2.2.1
                                                        have p3522_3 := h3522c.2.2.2
                                                        linarith only [h3455, hlam, p3522_0]
                                                      · have p3522_0 := h3522c.1
                                                        have p3522_1 := h3522c.2.1
                                                        have p3522_2 := h3522c.2.2.1
                                                        have p3522_3 := h3522c.2.2.2
                                                        linarith only [h0, h3295, h3453, h3458, h3462, h3464, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3522_1]
                                                      · have p3522_0 := h3522c.1
                                                        have p3522_1 := h3522c.2.1
                                                        have p3522_2 := h3522c.2.2.1
                                                        have p3522_3 := h3522c.2.2.2
                                                        linarith only [h3444, h3457, h3462, h3464, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3465_1, p3522_1]
                                                      · have p3522_0 := h3522c.1
                                                        have p3522_1 := h3522c.2.1
                                                        have p3522_2 := h3522c.2.2.1
                                                        have p3522_3 := h3522c.2.2.2
                                                        rcases p3522_3 (m.d 0 2) (by simp) with h3538 | h3538
                                                        · linarith only [h3445, h3538, hlam]
                                                        · linarith only [h0, h3538, hlam]
                                                      · have p3522_0 := h3522c.1
                                                        have p3522_1 := h3522c.2.1
                                                        have p3522_2 := h3522c.2.2.1
                                                        have p3522_3 := h3522c.2.2.2
                                                        linarith only [hlam, p3522_0]
                                                      · have p3522_0 := h3522c.1
                                                        have p3522_1 := h3522c.2.1
                                                        have p3522_2 := h3522c.2.2.1
                                                        have p3522_3 := h3522c.2.2.2
                                                        linarith only [h3295, h3455, hc01, hc23, hlam, hphi, ht12, p3522_1]
                                                      · have p3522_0 := h3522c.1
                                                        have p3522_1 := h3522c.2.1
                                                        have p3522_2 := h3522c.2.2.1
                                                        have p3522_3 := h3522c.2.2.2
                                                        linarith only [h0, h3295, h3444, h3453, h3457, h3458, hlam, p3465_1, p3522_2]
                                                      · have p3522_0 := h3522c.1
                                                        have p3522_1 := h3522c.2.1
                                                        have p3522_2 := h3522c.2.2.1
                                                        have p3522_3 := h3522c.2.2.2
                                                        linarith only [h3444, h3457, h3462, h3464, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3465_1, p3522_1]
                                                      · have p3522_0 := h3522c.1
                                                        have p3522_1 := h3522c.2.1
                                                        have p3522_2 := h3522c.2.2.1
                                                        have p3522_3 := h3522c.2.2.2
                                                        rcases p3522_3 (m.d 0 2) (by simp) with h3545 | h3545
                                                        · linarith only [h3447, h3545, hlam]
                                                        · linarith only [h0, h3545, hlam]
                                                      · have p3522_0 := h3522c.1
                                                        have p3522_1 := h3522c.2.1
                                                        have p3522_2 := h3522c.2.2.1
                                                        have p3522_3 := h3522c.2.2.2
                                                        linarith only [h3461, hlam, p3522_1]
                                                      · have p3522_0 := h3522c.1
                                                        have p3522_1 := h3522c.2.1
                                                        have p3522_2 := h3522c.2.2.1
                                                        have p3522_3 := h3522c.2.2.2
                                                        linarith only [hlam, p3522_0]
                                                      · have p3522_0 := h3522c.1
                                                        have p3522_1 := h3522c.2.1
                                                        have p3522_2 := h3522c.2.2.1
                                                        have p3522_3 := h3522c.2.2.2
                                                        linarith only [h3444, h3447, h3457, hlam, p3465_1, p3522_2]
                                                      · have p3522_0 := h3522c.1
                                                        have p3522_1 := h3522c.2.1
                                                        have p3522_2 := h3522c.2.2.1
                                                        have p3522_3 := h3522c.2.2.2
                                                        linarith only [h3449, hlam, p3522_0]
                                                      · have p3522_0 := h3522c.1
                                                        have p3522_1 := h3522c.2.1
                                                        have p3522_2 := h3522c.2.2.1
                                                        have p3522_3 := h3522c.2.2.2
                                                        linarith only [h3457, hlam, p3522_0]
                                                      · have p3522_0 := h3522c.1
                                                        have p3522_1 := h3522c.2.1
                                                        have p3522_2 := h3522c.2.2.1
                                                        have p3522_3 := h3522c.2.2.2
                                                        linarith only [h3462, hlam, p3522_1]
                                                      · have p3522_0 := h3522c.1
                                                        have p3522_1 := h3522c.2.1
                                                        have p3522_2 := h3522c.2.2.1
                                                        have p3522_3 := h3522c.2.2.2
                                                        linarith only [h3463, hlam, p3522_0]
                                                      · have p3522_0 := h3522c.1
                                                        have p3522_1 := h3522c.2.1
                                                        have p3522_2 := h3522c.2.2.1
                                                        have p3522_3 := h3522c.2.2.2
                                                        linarith only [hlam, p3522_0]
                                                    · linarith only [h0, h3485, hc01, hlam, p3465_1]
                                                · linarith only [h3452, h3482, hlam]
                                              · linarith only [h3451, h3481, hlam]
                                            · linarith only [h3449, h3480, hlam]
                                          · linarith only [h3444, h3479, hlam]
                                        · have p3465_0 := h3465c.1
                                          have p3465_1 := h3465c.2.1
                                          have p3465_2 := h3465c.2.2.1
                                          have p3465_3 := h3465c.2.2.2
                                          linarith only [h0, h3457, h3462, h3464, hc03, hc45, hlam, hphi, ht0b, ht5b, p3465_1]
                                        · have p3465_0 := h3465c.1
                                          have p3465_1 := h3465c.2.1
                                          have p3465_2 := h3465c.2.2.1
                                          have p3465_3 := h3465c.2.2.2
                                          rcases p3465_3 (m.d 0 1) (by simp) with h3562 | h3562
                                          · linarith only [h1, h3562, hlam]
                                          · linarith only [h0, h3562, hlam]
                                        · have p3465_0 := h3465c.1
                                          have p3465_1 := h3465c.2.1
                                          have p3465_2 := h3465c.2.2.1
                                          have p3465_3 := h3465c.2.2.2
                                          linarith only [hlam, p3465_0]
                                        · have p3465_0 := h3465c.1
                                          have p3465_1 := h3465c.2.1
                                          have p3465_2 := h3465c.2.2.1
                                          have p3465_3 := h3465c.2.2.2
                                          linarith only [h0, h1, h3295, h3453, h3457, h3462, h3464, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3465_1]
                                        · have p3465_0 := h3465c.1
                                          have p3465_1 := h3465c.2.1
                                          have p3465_2 := h3465c.2.2.1
                                          have p3465_3 := h3465c.2.2.2
                                          rcases p3465_3 (m.d 0 1) (by simp) with h3567 | h3567
                                          · linarith only [h1, h3567, hlam]
                                          · linarith only [h3444, h3567, hlam]
                                        · have p3465_0 := h3465c.1
                                          have p3465_1 := h3465c.2.1
                                          have p3465_2 := h3465c.2.2.1
                                          have p3465_3 := h3465c.2.2.2
                                          linarith only [h0, h3457, h3462, h3464, hc04, hc45, hlam, hphi, ht0b, ht5b, p3465_1]
                                        · have p3465_0 := h3465c.1
                                          have p3465_1 := h3465c.2.1
                                          have p3465_2 := h3465c.2.2.1
                                          have p3465_3 := h3465c.2.2.2
                                          rcases p3465_3 (m.d 0 1) (by simp) with h3571 | h3571
                                          · linarith only [h3295, h3571, hlam]
                                          · linarith only [h0, h3571, hlam]
                                        · have p3465_0 := h3465c.1
                                          have p3465_1 := h3465c.2.1
                                          have p3465_2 := h3465c.2.2.1
                                          have p3465_3 := h3465c.2.2.2
                                          linarith only [h3450, hlam, p3465_0]
                                        · have p3465_0 := h3465c.1
                                          have p3465_1 := h3465c.2.1
                                          have p3465_2 := h3465c.2.2.1
                                          have p3465_3 := h3465c.2.2.2
                                          linarith only [hlam, p3465_0]
                                        · have p3465_0 := h3465c.1
                                          have p3465_1 := h3465c.2.1
                                          have p3465_2 := h3465c.2.2.1
                                          have p3465_3 := h3465c.2.2.2
                                          rcases p3465_3 (m.d 0 1) (by simp) with h3576 | h3576
                                          · linarith only [h3295, h3576, hlam]
                                          · linarith only [h3444, h3576, hlam]
                                        · have p3465_0 := h3465c.1
                                          have p3465_1 := h3465c.2.1
                                          have p3465_2 := h3465c.2.2.1
                                          have p3465_3 := h3465c.2.2.2
                                          linarith only [h3444, hlam, p3465_0]
                                        · have p3465_0 := h3465c.1
                                          have p3465_1 := h3465c.2.1
                                          have p3465_2 := h3465c.2.2.1
                                          have p3465_3 := h3465c.2.2.2
                                          linarith only [h3449, hlam, p3465_1]
                                        · have p3465_0 := h3465c.1
                                          have p3465_1 := h3465c.2.1
                                          have p3465_2 := h3465c.2.2.1
                                          have p3465_3 := h3465c.2.2.2
                                          linarith only [h3451, hlam, p3465_0]
                                        · have p3465_0 := h3465c.1
                                          have p3465_1 := h3465c.2.1
                                          have p3465_2 := h3465c.2.2.1
                                          have p3465_3 := h3465c.2.2.2
                                          linarith only [h3452, hlam, p3465_1]
                                        · have p3465_0 := h3465c.1
                                          have p3465_1 := h3465c.2.1
                                          have p3465_2 := h3465c.2.2.1
                                          have p3465_3 := h3465c.2.2.2
                                          linarith only [hlam, p3465_0]
                                      · linarith only [h3464, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h3295, h3444, h3455, h3460, h3463, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
                                  · linarith only [h0, h3295, h3455, h3457, h3461, h3462, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                · linarith only [h0, h1, h3453, h3457, h3461, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h0, h3295, h3457, h3460, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                            · linarith only [h0, h3295, h3457, h3458, h3459, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h1, h3450, h3458, hlam]
                        · linarith only [h3457, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h3452, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h0, h3295, h3450, h3451, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h3594 | h3594
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3595 | h3595
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3596 | h3596
                    · linarith only [h0, h3445, h3449, h3596, hc01, hc25, hlam, hphi, ht0b, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3598 | h3598
                      · linarith only [h0, h3447, h3598, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h3600 | h3600
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h3601 | h3601
                          · linarith only [h0, h1, h3450, h3596, h3601, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h3600, h3601, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h3600, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h3595, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h0, h1, h3594, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
            · linarith only [h3449, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
      · linarith only [h0, h3444, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]

end R2N4
