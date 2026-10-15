import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5024000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s6_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg1304 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg1819 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1947 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h3197 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h3313 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h1304 := hg1304
  have h1819 := hg1819
  rcases m.htr 1 2 3 (by decide) (by decide) with h3314 | h3314
  · linarith only [h0, h3314, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h3316 | h3316
    · linarith only [h0, h1304, h3313, h3316, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h3318 | h3318
      · linarith only [h0, h1819, h3318, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3320 | h3320
        · linarith only [h1, h1947, h3320, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h3322 | h3322
          · linarith only [h1, h3197, h3322, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3324 | h3324
            · rcases m.htr 2 3 4 (by decide) (by decide) with h3325 | h3325
              · rcases m.htr 2 3 5 (by decide) (by decide) with h3326 | h3326
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3327 | h3327
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3328 | h3328
                    · rcases h0bigk with h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c | h3329c
                      · have p3329_0 := h3329c.1
                        have p3329_1 := h3329c.2.1
                        have p3329_2 := h3329c.2.2.1
                        have p3329_3 := h3329c.2.2.2
                        linarith only [hlam, p3329_0]
                      · have p3329_0 := h3329c.1
                        have p3329_1 := h3329c.2.1
                        have p3329_2 := h3329c.2.2.1
                        have p3329_3 := h3329c.2.2.2
                        rcases p3329_3 (m.d 0 1) (by simp) with h3331 | h3331
                        · rcases p3329_3 (m.d 0 2) (by simp) with h3332 | h3332
                          · linarith only [h0, h3332, hlam]
                          · rcases p3329_3 (m.d 0 3) (by simp) with h3334 | h3334
                            · linarith only [h1, h3334, hlam]
                            · linarith only [h3334, h4, hlam]
                        · linarith only [h0, h3331, hlam]
                      · have p3329_0 := h3329c.1
                        have p3329_1 := h3329c.2.1
                        have p3329_2 := h3329c.2.2.1
                        have p3329_3 := h3329c.2.2.2
                        rcases p3329_3 (m.d 0 1) (by simp) with h3338 | h3338
                        · rcases p3329_3 (m.d 0 2) (by simp) with h3339 | h3339
                          · linarith only [h0, h3339, hlam]
                          · rcases p3329_3 (m.d 0 3) (by simp) with h3341 | h3341
                            · linarith only [h1, h3341, hlam]
                            · rcases p3329_3 (m.d 0 4) (by simp) with h3343 | h3343
                              · linarith only [h2, h3343, hlam]
                              · linarith only [h1947, h3343, hlam]
                        · linarith only [h1, h3338, hlam]
                      · have p3329_0 := h3329c.1
                        have p3329_1 := h3329c.2.1
                        have p3329_2 := h3329c.2.2.1
                        have p3329_3 := h3329c.2.2.2
                        linarith only [h2, h3324, hc45, hlam, hphi, ht0b, ht5b, p3329_1, u0elo0]
                      · have p3329_0 := h3329c.1
                        have p3329_1 := h3329c.2.1
                        have p3329_2 := h3329c.2.2.1
                        have p3329_3 := h3329c.2.2.2
                        rcases p3329_3 (m.d 0 1) (by simp) with h3348 | h3348
                        · rcases p3329_3 (m.d 0 2) (by simp) with h3349 | h3349
                          · linarith only [h0, h3349, hlam]
                          · rcases p3329_3 (m.d 0 3) (by simp) with h3351 | h3351
                            · linarith only [h1, h3351, hlam]
                            · rcases p3329_3 (m.d 0 4) (by simp) with h3353 | h3353
                              · linarith only [h2, h3353, hlam]
                              · linarith only [h3313, h3353, hlam]
                        · linarith only [h3, h3348, hlam]
                      · have p3329_0 := h3329c.1
                        have p3329_1 := h3329c.2.1
                        have p3329_2 := h3329c.2.2.1
                        have p3329_3 := h3329c.2.2.2
                        linarith only [h0, hlam, p3329_0]
                      · have p3329_0 := h3329c.1
                        have p3329_1 := h3329c.2.1
                        have p3329_2 := h3329c.2.2.1
                        have p3329_3 := h3329c.2.2.2
                        linarith only [hlam, p3329_0]
                      · have p3329_0 := h3329c.1
                        have p3329_1 := h3329c.2.1
                        have p3329_2 := h3329c.2.2.1
                        have p3329_3 := h3329c.2.2.2
                        linarith only [h4, hlam, p3329_0]
                      · have p3329_0 := h3329c.1
                        have p3329_1 := h3329c.2.1
                        have p3329_2 := h3329c.2.2.1
                        have p3329_3 := h3329c.2.2.2
                        linarith only [h1304, hlam, p3329_1]
                      · have p3329_0 := h3329c.1
                        have p3329_1 := h3329c.2.1
                        have p3329_2 := h3329c.2.2.1
                        have p3329_3 := h3329c.2.2.2
                        linarith only [h1819, hlam, p3329_0]
                      · have p3329_0 := h3329c.1
                        have p3329_1 := h3329c.2.1
                        have p3329_2 := h3329c.2.2.1
                        have p3329_3 := h3329c.2.2.2
                        linarith only [h1, hlam, p3329_1]
                      · have p3329_0 := h3329c.1
                        have p3329_1 := h3329c.2.1
                        have p3329_2 := h3329c.2.2.1
                        have p3329_3 := h3329c.2.2.2
                        linarith only [h0, h3197, h3325, h3328, hc12, hc23, hlam, hphi, p3329_1]
                      · have p3329_0 := h3329c.1
                        have p3329_1 := h3329c.2.1
                        have p3329_2 := h3329c.2.2.1
                        have p3329_3 := h3329c.2.2.2
                        linarith only [hlam, p3329_0]
                      · have p3329_0 := h3329c.1
                        have p3329_1 := h3329c.2.1
                        have p3329_2 := h3329c.2.2.1
                        have p3329_3 := h3329c.2.2.2
                        linarith only [h1947, hlam, p3329_1]
                      · have p3329_0 := h3329c.1
                        have p3329_1 := h3329c.2.1
                        have p3329_2 := h3329c.2.2.1
                        have p3329_3 := h3329c.2.2.2
                        linarith only [h3197, hlam, p3329_1]
                      · have p3329_0 := h3329c.1
                        have p3329_1 := h3329c.2.1
                        have p3329_2 := h3329c.2.2.1
                        have p3329_3 := h3329c.2.2.2
                        linarith only [h2, hlam, p3329_0]
                      · have p3329_0 := h3329c.1
                        have p3329_1 := h3329c.2.1
                        have p3329_2 := h3329c.2.2.1
                        have p3329_3 := h3329c.2.2.2
                        linarith only [h0, h1947, h3325, hc12, hc23, hlam, hphi, p3329_1]
                      · have p3329_0 := h3329c.1
                        have p3329_1 := h3329c.2.1
                        have p3329_2 := h3329c.2.2.1
                        have p3329_3 := h3329c.2.2.2
                        linarith only [h0, h1947, h3325, h4, hc12, hc23, hlam, hphi, p3329_1]
                      · have p3329_0 := h3329c.1
                        have p3329_1 := h3329c.2.1
                        have p3329_2 := h3329c.2.2.1
                        have p3329_3 := h3329c.2.2.2
                        linarith only [hlam, p3329_0]
                      · have p3329_0 := h3329c.1
                        have p3329_1 := h3329c.2.1
                        have p3329_2 := h3329c.2.2.1
                        have p3329_3 := h3329c.2.2.2
                        linarith only [h0, h1947, h3197, h3325, h4, hc12, hc23, hlam, hphi, p3329_1]
                      · have p3329_0 := h3329c.1
                        have p3329_1 := h3329c.2.1
                        have p3329_2 := h3329c.2.2.1
                        have p3329_3 := h3329c.2.2.2
                        linarith only [h3, hlam, p3329_0]
                      · have p3329_0 := h3329c.1
                        have p3329_1 := h3329c.2.1
                        have p3329_2 := h3329c.2.2.1
                        have p3329_3 := h3329c.2.2.2
                        linarith only [h0, h3197, h3325, h3328, hc12, hc23, hlam, hphi, p3329_1]
                      · have p3329_0 := h3329c.1
                        have p3329_1 := h3329c.2.1
                        have p3329_2 := h3329c.2.2.1
                        have p3329_3 := h3329c.2.2.2
                        linarith only [h0, h3197, h3325, h3328, h4, hc12, hc23, hlam, hphi, p3329_1]
                      · have p3329_0 := h3329c.1
                        have p3329_1 := h3329c.2.1
                        have p3329_2 := h3329c.2.2.1
                        have p3329_3 := h3329c.2.2.2
                        linarith only [h3313, hlam, p3329_1]
                      · have p3329_0 := h3329c.1
                        have p3329_1 := h3329c.2.1
                        have p3329_2 := h3329c.2.2.1
                        have p3329_3 := h3329c.2.2.2
                        linarith only [hlam, p3329_0]
                    · linarith only [h1947, h2, h3324, h3328, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h1947, h2, h3324, h3325, h3327, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · linarith only [h0, h1947, h3325, h3326, h4, hc12, hc35, hlam, hphi, ht23]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h3380 | h3380
                · linarith only [h0, h3197, h3325, h3380, h4, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3382 | h3382
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3383 | h3383
                    · rcases h0bigk with h3384c | h3384c | h3384c | h3384c | h3384c | h3384c | h3384c | h3384c | h3384c | h3384c | h3384c | h3384c | h3384c | h3384c | h3384c | h3384c | h3384c | h3384c | h3384c | h3384c | h3384c | h3384c | h3384c | h3384c | h3384c
                      · have p3384_0 := h3384c.1
                        have p3384_1 := h3384c.2.1
                        have p3384_2 := h3384c.2.2.1
                        have p3384_3 := h3384c.2.2.2
                        linarith only [hlam, p3384_0]
                      · have p3384_0 := h3384c.1
                        have p3384_1 := h3384c.2.1
                        have p3384_2 := h3384c.2.2.1
                        have p3384_3 := h3384c.2.2.2
                        rcases p3384_3 (m.d 0 1) (by simp) with h3386 | h3386
                        · rcases p3384_3 (m.d 0 2) (by simp) with h3387 | h3387
                          · linarith only [h0, h3387, hlam]
                          · rcases p3384_3 (m.d 0 3) (by simp) with h3389 | h3389
                            · linarith only [h1, h3389, hlam]
                            · linarith only [h3389, h4, hlam]
                        · linarith only [h0, h3386, hlam]
                      · have p3384_0 := h3384c.1
                        have p3384_1 := h3384c.2.1
                        have p3384_2 := h3384c.2.2.1
                        have p3384_3 := h3384c.2.2.2
                        rcases p3384_3 (m.d 0 1) (by simp) with h3393 | h3393
                        · rcases p3384_3 (m.d 0 2) (by simp) with h3394 | h3394
                          · linarith only [h0, h3394, hlam]
                          · rcases p3384_3 (m.d 0 3) (by simp) with h3396 | h3396
                            · linarith only [h1, h3396, hlam]
                            · rcases p3384_3 (m.d 0 4) (by simp) with h3398 | h3398
                              · linarith only [h2, h3398, hlam]
                              · linarith only [h1947, h3398, hlam]
                        · linarith only [h1, h3393, hlam]
                      · have p3384_0 := h3384c.1
                        have p3384_1 := h3384c.2.1
                        have p3384_2 := h3384c.2.2.1
                        have p3384_3 := h3384c.2.2.2
                        linarith only [h2, h3324, hc45, hlam, hphi, ht0b, ht5b, p3384_1, u0elo0]
                      · have p3384_0 := h3384c.1
                        have p3384_1 := h3384c.2.1
                        have p3384_2 := h3384c.2.2.1
                        have p3384_3 := h3384c.2.2.2
                        rcases p3384_3 (m.d 0 1) (by simp) with h3403 | h3403
                        · rcases p3384_3 (m.d 0 2) (by simp) with h3404 | h3404
                          · linarith only [h0, h3404, hlam]
                          · rcases p3384_3 (m.d 0 3) (by simp) with h3406 | h3406
                            · linarith only [h1, h3406, hlam]
                            · rcases p3384_3 (m.d 0 4) (by simp) with h3408 | h3408
                              · linarith only [h2, h3408, hlam]
                              · linarith only [h3313, h3408, hlam]
                        · linarith only [h3, h3403, hlam]
                      · have p3384_0 := h3384c.1
                        have p3384_1 := h3384c.2.1
                        have p3384_2 := h3384c.2.2.1
                        have p3384_3 := h3384c.2.2.2
                        linarith only [h0, hlam, p3384_0]
                      · have p3384_0 := h3384c.1
                        have p3384_1 := h3384c.2.1
                        have p3384_2 := h3384c.2.2.1
                        have p3384_3 := h3384c.2.2.2
                        linarith only [hlam, p3384_0]
                      · have p3384_0 := h3384c.1
                        have p3384_1 := h3384c.2.1
                        have p3384_2 := h3384c.2.2.1
                        have p3384_3 := h3384c.2.2.2
                        linarith only [h4, hlam, p3384_0]
                      · have p3384_0 := h3384c.1
                        have p3384_1 := h3384c.2.1
                        have p3384_2 := h3384c.2.2.1
                        have p3384_3 := h3384c.2.2.2
                        linarith only [h1304, hlam, p3384_1]
                      · have p3384_0 := h3384c.1
                        have p3384_1 := h3384c.2.1
                        have p3384_2 := h3384c.2.2.1
                        have p3384_3 := h3384c.2.2.2
                        linarith only [h1819, hlam, p3384_0]
                      · have p3384_0 := h3384c.1
                        have p3384_1 := h3384c.2.1
                        have p3384_2 := h3384c.2.2.1
                        have p3384_3 := h3384c.2.2.2
                        linarith only [h1, hlam, p3384_1]
                      · have p3384_0 := h3384c.1
                        have p3384_1 := h3384c.2.1
                        have p3384_2 := h3384c.2.2.1
                        have p3384_3 := h3384c.2.2.2
                        linarith only [h0, h3380, h3383, h4, hc12, hc34, hlam, hphi, ht23, p3384_1]
                      · have p3384_0 := h3384c.1
                        have p3384_1 := h3384c.2.1
                        have p3384_2 := h3384c.2.2.1
                        have p3384_3 := h3384c.2.2.2
                        linarith only [hlam, p3384_0]
                      · have p3384_0 := h3384c.1
                        have p3384_1 := h3384c.2.1
                        have p3384_2 := h3384c.2.2.1
                        have p3384_3 := h3384c.2.2.2
                        linarith only [h1947, hlam, p3384_1]
                      · have p3384_0 := h3384c.1
                        have p3384_1 := h3384c.2.1
                        have p3384_2 := h3384c.2.2.1
                        have p3384_3 := h3384c.2.2.2
                        linarith only [h3197, hlam, p3384_1]
                      · have p3384_0 := h3384c.1
                        have p3384_1 := h3384c.2.1
                        have p3384_2 := h3384c.2.2.1
                        have p3384_3 := h3384c.2.2.2
                        linarith only [h2, hlam, p3384_0]
                      · have p3384_0 := h3384c.1
                        have p3384_1 := h3384c.2.1
                        have p3384_2 := h3384c.2.2.1
                        have p3384_3 := h3384c.2.2.2
                        rcases p3384_3 (m.d 0 1) (by simp) with h3423 | h3423
                        · rcases p3384_3 (m.d 0 2) (by simp) with h3424 | h3424
                          · linarith only [h1304, h3424, hlam]
                          · rcases p3384_3 (m.d 0 3) (by simp) with h3426 | h3426
                            · linarith only [h1947, h3426, hlam]
                            · linarith only [h3426, h4, hlam]
                        · linarith only [h0, h3423, hlam]
                      · have p3384_0 := h3384c.1
                        have p3384_1 := h3384c.2.1
                        have p3384_2 := h3384c.2.2.1
                        have p3384_3 := h3384c.2.2.2
                        rcases p3384_3 (m.d 0 1) (by simp) with h3430 | h3430
                        · rcases p3384_3 (m.d 0 2) (by simp) with h3431 | h3431
                          · linarith only [h1304, h3431, hlam]
                          · rcases p3384_3 (m.d 0 3) (by simp) with h3433 | h3433
                            · linarith only [h1947, h3433, hlam]
                            · rcases p3384_3 (m.d 0 4) (by simp) with h3435 | h3435
                              · rcases p3384_3 (m.d 0 5) (by simp) with h3436 | h3436
                                · linarith only [h3313, h3436, hlam]
                                · linarith only [h3197, h3436, hlam]
                              · linarith only [h1947, h3435, hlam]
                        · linarith only [h1, h3430, hlam]
                      · have p3384_0 := h3384c.1
                        have p3384_1 := h3384c.2.1
                        have p3384_2 := h3384c.2.2.1
                        have p3384_3 := h3384c.2.2.2
                        linarith only [hlam, p3384_0]
                      · have p3384_0 := h3384c.1
                        have p3384_1 := h3384c.2.1
                        have p3384_2 := h3384c.2.2.1
                        have p3384_3 := h3384c.2.2.2
                        rcases p3384_3 (m.d 0 1) (by simp) with h3442 | h3442
                        · rcases p3384_3 (m.d 0 2) (by simp) with h3443 | h3443
                          · linarith only [h1304, h3443, hlam]
                          · rcases p3384_3 (m.d 0 3) (by simp) with h3445 | h3445
                            · linarith only [h1947, h3445, hlam]
                            · rcases p3384_3 (m.d 0 4) (by simp) with h3447 | h3447
                              · rcases p3384_3 (m.d 0 5) (by simp) with h3448 | h3448
                                · linarith only [h3313, h3448, hlam]
                                · rcases h0emin with h3450 | h3450 | h3450 | h3450 | h3450
                                  · rcases h1bigk with h3451c | h3451c | h3451c | h3451c | h3451c | h3451c | h3451c | h3451c | h3451c | h3451c | h3451c | h3451c | h3451c | h3451c | h3451c | h3451c | h3451c | h3451c | h3451c | h3451c | h3451c | h3451c | h3451c | h3451c | h3451c
                                    · have p3451_0 := h3451c.1
                                      have p3451_1 := h3451c.2.1
                                      have p3451_2 := h3451c.2.2.1
                                      have p3451_3 := h3451c.2.2.2
                                      linarith only [hlam, p3451_0]
                                    · have p3451_0 := h3451c.1
                                      have p3451_1 := h3451c.2.1
                                      have p3451_2 := h3451c.2.2.1
                                      have p3451_3 := h3451c.2.2.2
                                      rcases p3451_3 (m.d 0 1) (by simp) with h3453 | h3453
                                      · rcases p3451_3 (m.d 1 2) (by simp) with h3454 | h3454
                                        · linarith only [h3454, hlam, p3451_0]
                                        · rcases p3451_3 (m.d 1 3) (by simp) with h3456 | h3456
                                          · linarith only [h1, h3456, hlam]
                                          · linarith only [h3314, h3456, hlam]
                                      · linarith only [h3453, hlam, p3451_0]
                                    · have p3451_0 := h3451c.1
                                      have p3451_1 := h3451c.2.1
                                      have p3451_2 := h3451c.2.2.1
                                      have p3451_3 := h3451c.2.2.2
                                      rcases p3451_3 (m.d 0 1) (by simp) with h3460 | h3460
                                      · rcases p3451_3 (m.d 1 2) (by simp) with h3461 | h3461
                                        · linarith only [h0, h3461, hlam]
                                        · rcases p3451_3 (m.d 1 3) (by simp) with h3463 | h3463
                                          · linarith only [h3463, hlam, p3451_0]
                                          · rcases p3451_3 (m.d 1 4) (by simp) with h3465 | h3465
                                            · linarith only [h2, h3465, hlam]
                                            · linarith only [h3320, h3465, hlam]
                                      · linarith only [h3460, hlam, p3451_0]
                                    · have p3451_0 := h3451c.1
                                      have p3451_1 := h3451c.2.1
                                      have p3451_2 := h3451c.2.2.1
                                      have p3451_3 := h3451c.2.2.2
                                      linarith only [h3324, hc45, hlam, hphi, ht0b, ht5b, p3451_1, u0elo0]
                                    · have p3451_0 := h3451c.1
                                      have p3451_1 := h3451c.2.1
                                      have p3451_2 := h3451c.2.2.1
                                      have p3451_3 := h3451c.2.2.2
                                      rcases p3451_3 (m.d 0 1) (by simp) with h3470 | h3470
                                      · rcases p3451_3 (m.d 1 2) (by simp) with h3471 | h3471
                                        · linarith only [h0, h3471, hlam]
                                        · rcases p3451_3 (m.d 1 3) (by simp) with h3473 | h3473
                                          · linarith only [h1, h3473, hlam]
                                          · rcases p3451_3 (m.d 1 4) (by simp) with h3475 | h3475
                                            · linarith only [h2, h3475, hlam]
                                            · linarith only [h3324, h3475, hlam]
                                      · linarith only [h3470, hlam, p3451_0]
                                    · have p3451_0 := h3451c.1
                                      have p3451_1 := h3451c.2.1
                                      have p3451_2 := h3451c.2.2.1
                                      have p3451_3 := h3451c.2.2.2
                                      linarith only [h0, hlam, p3451_0]
                                    · have p3451_0 := h3451c.1
                                      have p3451_1 := h3451c.2.1
                                      have p3451_2 := h3451c.2.2.1
                                      have p3451_3 := h3451c.2.2.2
                                      linarith only [hlam, p3451_0]
                                    · have p3451_0 := h3451c.1
                                      have p3451_1 := h3451c.2.1
                                      have p3451_2 := h3451c.2.2.1
                                      have p3451_3 := h3451c.2.2.2
                                      linarith only [h3314, hlam, p3451_0]
                                    · have p3451_0 := h3451c.1
                                      have p3451_1 := h3451c.2.1
                                      have p3451_2 := h3451c.2.2.1
                                      have p3451_3 := h3451c.2.2.2
                                      linarith only [h3316, hlam, p3451_0]
                                    · have p3451_0 := h3451c.1
                                      have p3451_1 := h3451c.2.1
                                      have p3451_2 := h3451c.2.2.1
                                      have p3451_3 := h3451c.2.2.2
                                      linarith only [h3318, hlam, p3451_0]
                                    · have p3451_0 := h3451c.1
                                      have p3451_1 := h3451c.2.1
                                      have p3451_2 := h3451c.2.2.1
                                      have p3451_3 := h3451c.2.2.2
                                      linarith only [h1, hlam, p3451_0]
                                    · have p3451_0 := h3451c.1
                                      have p3451_1 := h3451c.2.1
                                      have p3451_2 := h3451c.2.2.1
                                      have p3451_3 := h3451c.2.2.2
                                      linarith only [h1, h3197, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3384_1, p3451_1, u0elo3]
                                    · have p3451_0 := h3451c.1
                                      have p3451_1 := h3451c.2.1
                                      have p3451_2 := h3451c.2.2.1
                                      have p3451_3 := h3451c.2.2.2
                                      linarith only [hlam, p3451_0]
                                    · have p3451_0 := h3451c.1
                                      have p3451_1 := h3451c.2.1
                                      have p3451_2 := h3451c.2.2.1
                                      have p3451_3 := h3451c.2.2.2
                                      linarith only [h3320, hlam, p3451_1]
                                    · have p3451_0 := h3451c.1
                                      have p3451_1 := h3451c.2.1
                                      have p3451_2 := h3451c.2.2.1
                                      have p3451_3 := h3451c.2.2.2
                                      linarith only [h3322, hlam, p3451_1]
                                    · have p3451_0 := h3451c.1
                                      have p3451_1 := h3451c.2.1
                                      have p3451_2 := h3451c.2.2.1
                                      have p3451_3 := h3451c.2.2.2
                                      linarith only [h2, hlam, p3451_0]
                                    · have p3451_0 := h3451c.1
                                      have p3451_1 := h3451c.2.1
                                      have p3451_2 := h3451c.2.2.1
                                      have p3451_3 := h3451c.2.2.2
                                      linarith only [h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3451_1, u0elo0]
                                    · have p3451_0 := h3451c.1
                                      have p3451_1 := h3451c.2.1
                                      have p3451_2 := h3451c.2.2.1
                                      have p3451_3 := h3451c.2.2.2
                                      linarith only [h2, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3451_1, u0elo0]
                                    · have p3451_0 := h3451c.1
                                      have p3451_1 := h3451c.2.1
                                      have p3451_2 := h3451c.2.2.1
                                      have p3451_3 := h3451c.2.2.2
                                      linarith only [hlam, p3451_0]
                                    · have p3451_0 := h3451c.1
                                      have p3451_1 := h3451c.2.1
                                      have p3451_2 := h3451c.2.2.1
                                      have p3451_3 := h3451c.2.2.2
                                      linarith only [h2, hc15, hlam, hphi, ht0b, ht5b, p3451_1, u0elo0]
                                    · have p3451_0 := h3451c.1
                                      have p3451_1 := h3451c.2.1
                                      have p3451_2 := h3451c.2.2.1
                                      have p3451_3 := h3451c.2.2.2
                                      linarith only [h3, hlam, p3451_0]
                                    · have p3451_0 := h3451c.1
                                      have p3451_1 := h3451c.2.1
                                      have p3451_2 := h3451c.2.2.1
                                      have p3451_3 := h3451c.2.2.2
                                      linarith only [h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3451_1, u0elo0]
                                    · have p3451_0 := h3451c.1
                                      have p3451_1 := h3451c.2.1
                                      have p3451_2 := h3451c.2.2.1
                                      have p3451_3 := h3451c.2.2.2
                                      linarith only [h2, h3, h3314, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3384_1, p3451_1, u0elo0]
                                    · have p3451_0 := h3451c.1
                                      have p3451_1 := h3451c.2.1
                                      have p3451_2 := h3451c.2.2.1
                                      have p3451_3 := h3451c.2.2.2
                                      linarith only [h3324, hlam, p3451_0]
                                    · have p3451_0 := h3451c.1
                                      have p3451_1 := h3451c.2.1
                                      have p3451_2 := h3451c.2.2.1
                                      have p3451_3 := h3451c.2.2.2
                                      linarith only [hlam, p3451_0]
                                  · linarith only [h3380, h3383, h3450, h4, hc34, hlam, ht01, ht12, ht23]
                                  · linarith only [h2, h3197, h3450, hlam, p3384_1, u0elo0]
                                  · rcases h1bigk with h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c | h3501c
                                    · have p3501_0 := h3501c.1
                                      have p3501_1 := h3501c.2.1
                                      have p3501_2 := h3501c.2.2.1
                                      have p3501_3 := h3501c.2.2.2
                                      linarith only [hlam, p3501_0]
                                    · have p3501_0 := h3501c.1
                                      have p3501_1 := h3501c.2.1
                                      have p3501_2 := h3501c.2.2.1
                                      have p3501_3 := h3501c.2.2.2
                                      rcases p3501_3 (m.d 0 1) (by simp) with h3503 | h3503
                                      · rcases p3501_3 (m.d 1 2) (by simp) with h3504 | h3504
                                        · linarith only [h3504, hlam, p3501_0]
                                        · rcases p3501_3 (m.d 1 3) (by simp) with h3506 | h3506
                                          · linarith only [h1, h3506, hlam]
                                          · linarith only [h3314, h3506, hlam]
                                      · linarith only [h3503, hlam, p3501_0]
                                    · have p3501_0 := h3501c.1
                                      have p3501_1 := h3501c.2.1
                                      have p3501_2 := h3501c.2.2.1
                                      have p3501_3 := h3501c.2.2.2
                                      rcases p3501_3 (m.d 0 1) (by simp) with h3510 | h3510
                                      · rcases p3501_3 (m.d 1 2) (by simp) with h3511 | h3511
                                        · linarith only [h0, h3511, hlam]
                                        · rcases p3501_3 (m.d 1 3) (by simp) with h3513 | h3513
                                          · linarith only [h3513, hlam, p3501_0]
                                          · rcases p3501_3 (m.d 1 4) (by simp) with h3515 | h3515
                                            · linarith only [h2, h3515, hlam]
                                            · linarith only [h3320, h3515, hlam]
                                      · linarith only [h3510, hlam, p3501_0]
                                    · have p3501_0 := h3501c.1
                                      have p3501_1 := h3501c.2.1
                                      have p3501_2 := h3501c.2.2.1
                                      have p3501_3 := h3501c.2.2.2
                                      linarith only [h3324, hc45, hlam, hphi, ht0b, ht5b, p3501_1, u0elo0]
                                    · have p3501_0 := h3501c.1
                                      have p3501_1 := h3501c.2.1
                                      have p3501_2 := h3501c.2.2.1
                                      have p3501_3 := h3501c.2.2.2
                                      rcases p3501_3 (m.d 0 1) (by simp) with h3520 | h3520
                                      · rcases p3501_3 (m.d 1 2) (by simp) with h3521 | h3521
                                        · linarith only [h0, h3521, hlam]
                                        · rcases p3501_3 (m.d 1 3) (by simp) with h3523 | h3523
                                          · linarith only [h1, h3523, hlam]
                                          · rcases p3501_3 (m.d 1 4) (by simp) with h3525 | h3525
                                            · linarith only [h2, h3525, hlam]
                                            · linarith only [h3324, h3525, hlam]
                                      · linarith only [h3520, hlam, p3501_0]
                                    · have p3501_0 := h3501c.1
                                      have p3501_1 := h3501c.2.1
                                      have p3501_2 := h3501c.2.2.1
                                      have p3501_3 := h3501c.2.2.2
                                      linarith only [h0, hlam, p3501_0]
                                    · have p3501_0 := h3501c.1
                                      have p3501_1 := h3501c.2.1
                                      have p3501_2 := h3501c.2.2.1
                                      have p3501_3 := h3501c.2.2.2
                                      linarith only [hlam, p3501_0]
                                    · have p3501_0 := h3501c.1
                                      have p3501_1 := h3501c.2.1
                                      have p3501_2 := h3501c.2.2.1
                                      have p3501_3 := h3501c.2.2.2
                                      linarith only [h3314, hlam, p3501_0]
                                    · have p3501_0 := h3501c.1
                                      have p3501_1 := h3501c.2.1
                                      have p3501_2 := h3501c.2.2.1
                                      have p3501_3 := h3501c.2.2.2
                                      linarith only [h3316, hlam, p3501_0]
                                    · have p3501_0 := h3501c.1
                                      have p3501_1 := h3501c.2.1
                                      have p3501_2 := h3501c.2.2.1
                                      have p3501_3 := h3501c.2.2.2
                                      linarith only [h3318, hlam, p3501_0]
                                    · have p3501_0 := h3501c.1
                                      have p3501_1 := h3501c.2.1
                                      have p3501_2 := h3501c.2.2.1
                                      have p3501_3 := h3501c.2.2.2
                                      linarith only [h1, hlam, p3501_0]
                                    · have p3501_0 := h3501c.1
                                      have p3501_1 := h3501c.2.1
                                      have p3501_2 := h3501c.2.2.1
                                      have p3501_3 := h3501c.2.2.2
                                      linarith only [h1, h2, h3197, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3384_1, p3501_1, u0elo0]
                                    · have p3501_0 := h3501c.1
                                      have p3501_1 := h3501c.2.1
                                      have p3501_2 := h3501c.2.2.1
                                      have p3501_3 := h3501c.2.2.2
                                      linarith only [hlam, p3501_0]
                                    · have p3501_0 := h3501c.1
                                      have p3501_1 := h3501c.2.1
                                      have p3501_2 := h3501c.2.2.1
                                      have p3501_3 := h3501c.2.2.2
                                      linarith only [h3320, hlam, p3501_1]
                                    · have p3501_0 := h3501c.1
                                      have p3501_1 := h3501c.2.1
                                      have p3501_2 := h3501c.2.2.1
                                      have p3501_3 := h3501c.2.2.2
                                      linarith only [h3322, hlam, p3501_1]
                                    · have p3501_0 := h3501c.1
                                      have p3501_1 := h3501c.2.1
                                      have p3501_2 := h3501c.2.2.1
                                      have p3501_3 := h3501c.2.2.2
                                      linarith only [h2, hlam, p3501_0]
                                    · have p3501_0 := h3501c.1
                                      have p3501_1 := h3501c.2.1
                                      have p3501_2 := h3501c.2.2.1
                                      have p3501_3 := h3501c.2.2.2
                                      linarith only [h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3501_1, u0elo0]
                                    · have p3501_0 := h3501c.1
                                      have p3501_1 := h3501c.2.1
                                      have p3501_2 := h3501c.2.2.1
                                      have p3501_3 := h3501c.2.2.2
                                      linarith only [h2, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3501_1, u0elo0]
                                    · have p3501_0 := h3501c.1
                                      have p3501_1 := h3501c.2.1
                                      have p3501_2 := h3501c.2.2.1
                                      have p3501_3 := h3501c.2.2.2
                                      linarith only [hlam, p3501_0]
                                    · have p3501_0 := h3501c.1
                                      have p3501_1 := h3501c.2.1
                                      have p3501_2 := h3501c.2.2.1
                                      have p3501_3 := h3501c.2.2.2
                                      linarith only [h2, hc15, hlam, hphi, ht0b, ht5b, p3501_1, u0elo0]
                                    · have p3501_0 := h3501c.1
                                      have p3501_1 := h3501c.2.1
                                      have p3501_2 := h3501c.2.2.1
                                      have p3501_3 := h3501c.2.2.2
                                      linarith only [h3, hlam, p3501_0]
                                    · have p3501_0 := h3501c.1
                                      have p3501_1 := h3501c.2.1
                                      have p3501_2 := h3501c.2.2.1
                                      have p3501_3 := h3501c.2.2.2
                                      linarith only [h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3501_1, u0elo0]
                                    · have p3501_0 := h3501c.1
                                      have p3501_1 := h3501c.2.1
                                      have p3501_2 := h3501c.2.2.1
                                      have p3501_3 := h3501c.2.2.2
                                      linarith only [h2, h3, h3314, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3384_1, p3501_1, u0elo0]
                                    · have p3501_0 := h3501c.1
                                      have p3501_1 := h3501c.2.1
                                      have p3501_2 := h3501c.2.2.1
                                      have p3501_3 := h3501c.2.2.2
                                      linarith only [h3324, hlam, p3501_0]
                                    · have p3501_0 := h3501c.1
                                      have p3501_1 := h3501c.2.1
                                      have p3501_2 := h3501c.2.2.1
                                      have p3501_3 := h3501c.2.2.2
                                      linarith only [hlam, p3501_0]
                                  · linarith only [h2, h3450, hlam, p3384_1, u0elo0]
                              · linarith only [h3313, h3447, hlam]
                        · linarith only [h3, h3442, hlam]
                      · have p3384_0 := h3384c.1
                        have p3384_1 := h3384c.2.1
                        have p3384_2 := h3384c.2.2.1
                        have p3384_3 := h3384c.2.2.2
                        linarith only [h3, hlam, p3384_0]
                      · have p3384_0 := h3384c.1
                        have p3384_1 := h3384c.2.1
                        have p3384_2 := h3384c.2.2.1
                        have p3384_3 := h3384c.2.2.2
                        rcases p3384_3 (m.d 0 1) (by simp) with h3553 | h3553
                        · rcases p3384_3 (m.d 0 2) (by simp) with h3554 | h3554
                          · linarith only [h1819, h3554, hlam]
                          · rcases p3384_3 (m.d 0 3) (by simp) with h3556 | h3556
                            · linarith only [h3197, h3556, hlam]
                            · linarith only [h3556, h4, hlam]
                        · linarith only [h0, h3553, hlam]
                      · have p3384_0 := h3384c.1
                        have p3384_1 := h3384c.2.1
                        have p3384_2 := h3384c.2.2.1
                        have p3384_3 := h3384c.2.2.2
                        rcases p3384_3 (m.d 0 1) (by simp) with h3560 | h3560
                        · rcases p3384_3 (m.d 0 2) (by simp) with h3561 | h3561
                          · linarith only [h1819, h3561, hlam]
                          · rcases p3384_3 (m.d 0 3) (by simp) with h3563 | h3563
                            · linarith only [h3197, h3563, hlam]
                            · rcases p3384_3 (m.d 0 4) (by simp) with h3565 | h3565
                              · rcases p3384_3 (m.d 0 5) (by simp) with h3566 | h3566
                                · rcases h0emin with h3567 | h3567 | h3567 | h3567 | h3567
                                  · rcases h1bigk with h3568c | h3568c | h3568c | h3568c | h3568c | h3568c | h3568c | h3568c | h3568c | h3568c | h3568c | h3568c | h3568c | h3568c | h3568c | h3568c | h3568c | h3568c | h3568c | h3568c | h3568c | h3568c | h3568c | h3568c | h3568c
                                    · have p3568_0 := h3568c.1
                                      have p3568_1 := h3568c.2.1
                                      have p3568_2 := h3568c.2.2.1
                                      have p3568_3 := h3568c.2.2.2
                                      linarith only [hlam, p3568_0]
                                    · have p3568_0 := h3568c.1
                                      have p3568_1 := h3568c.2.1
                                      have p3568_2 := h3568c.2.2.1
                                      have p3568_3 := h3568c.2.2.2
                                      rcases p3568_3 (m.d 0 1) (by simp) with h3570 | h3570
                                      · rcases p3568_3 (m.d 1 2) (by simp) with h3571 | h3571
                                        · linarith only [h3571, hlam, p3568_0]
                                        · rcases p3568_3 (m.d 1 3) (by simp) with h3573 | h3573
                                          · linarith only [h1, h3573, hlam]
                                          · linarith only [h3314, h3573, hlam]
                                      · linarith only [h3570, hlam, p3568_0]
                                    · have p3568_0 := h3568c.1
                                      have p3568_1 := h3568c.2.1
                                      have p3568_2 := h3568c.2.2.1
                                      have p3568_3 := h3568c.2.2.2
                                      rcases p3568_3 (m.d 0 1) (by simp) with h3577 | h3577
                                      · rcases p3568_3 (m.d 1 2) (by simp) with h3578 | h3578
                                        · linarith only [h0, h3578, hlam]
                                        · rcases p3568_3 (m.d 1 3) (by simp) with h3580 | h3580
                                          · linarith only [h3580, hlam, p3568_0]
                                          · rcases p3568_3 (m.d 1 4) (by simp) with h3582 | h3582
                                            · linarith only [h2, h3582, hlam]
                                            · linarith only [h3320, h3582, hlam]
                                      · linarith only [h3577, hlam, p3568_0]
                                    · have p3568_0 := h3568c.1
                                      have p3568_1 := h3568c.2.1
                                      have p3568_2 := h3568c.2.2.1
                                      have p3568_3 := h3568c.2.2.2
                                      linarith only [h3324, hc45, hlam, hphi, ht0b, ht5b, p3568_1, u0elo0]
                                    · have p3568_0 := h3568c.1
                                      have p3568_1 := h3568c.2.1
                                      have p3568_2 := h3568c.2.2.1
                                      have p3568_3 := h3568c.2.2.2
                                      rcases p3568_3 (m.d 0 1) (by simp) with h3587 | h3587
                                      · rcases p3568_3 (m.d 1 2) (by simp) with h3588 | h3588
                                        · linarith only [h0, h3588, hlam]
                                        · rcases p3568_3 (m.d 1 3) (by simp) with h3590 | h3590
                                          · linarith only [h1, h3590, hlam]
                                          · rcases p3568_3 (m.d 1 4) (by simp) with h3592 | h3592
                                            · linarith only [h2, h3592, hlam]
                                            · linarith only [h3324, h3592, hlam]
                                      · linarith only [h3587, hlam, p3568_0]
                                    · have p3568_0 := h3568c.1
                                      have p3568_1 := h3568c.2.1
                                      have p3568_2 := h3568c.2.2.1
                                      have p3568_3 := h3568c.2.2.2
                                      linarith only [h0, hlam, p3568_0]
                                    · have p3568_0 := h3568c.1
                                      have p3568_1 := h3568c.2.1
                                      have p3568_2 := h3568c.2.2.1
                                      have p3568_3 := h3568c.2.2.2
                                      linarith only [hlam, p3568_0]
                                    · have p3568_0 := h3568c.1
                                      have p3568_1 := h3568c.2.1
                                      have p3568_2 := h3568c.2.2.1
                                      have p3568_3 := h3568c.2.2.2
                                      linarith only [h3314, hlam, p3568_0]
                                    · have p3568_0 := h3568c.1
                                      have p3568_1 := h3568c.2.1
                                      have p3568_2 := h3568c.2.2.1
                                      have p3568_3 := h3568c.2.2.2
                                      linarith only [h3316, hlam, p3568_0]
                                    · have p3568_0 := h3568c.1
                                      have p3568_1 := h3568c.2.1
                                      have p3568_2 := h3568c.2.2.1
                                      have p3568_3 := h3568c.2.2.2
                                      linarith only [h3318, hlam, p3568_0]
                                    · have p3568_0 := h3568c.1
                                      have p3568_1 := h3568c.2.1
                                      have p3568_2 := h3568c.2.2.1
                                      have p3568_3 := h3568c.2.2.2
                                      linarith only [h1, hlam, p3568_0]
                                    · have p3568_0 := h3568c.1
                                      have p3568_1 := h3568c.2.1
                                      have p3568_2 := h3568c.2.2.1
                                      have p3568_3 := h3568c.2.2.2
                                      linarith only [h1, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3384_1, p3568_1, u0elo4]
                                    · have p3568_0 := h3568c.1
                                      have p3568_1 := h3568c.2.1
                                      have p3568_2 := h3568c.2.2.1
                                      have p3568_3 := h3568c.2.2.2
                                      linarith only [hlam, p3568_0]
                                    · have p3568_0 := h3568c.1
                                      have p3568_1 := h3568c.2.1
                                      have p3568_2 := h3568c.2.2.1
                                      have p3568_3 := h3568c.2.2.2
                                      linarith only [h3320, hlam, p3568_1]
                                    · have p3568_0 := h3568c.1
                                      have p3568_1 := h3568c.2.1
                                      have p3568_2 := h3568c.2.2.1
                                      have p3568_3 := h3568c.2.2.2
                                      linarith only [h3322, hlam, p3568_1]
                                    · have p3568_0 := h3568c.1
                                      have p3568_1 := h3568c.2.1
                                      have p3568_2 := h3568c.2.2.1
                                      have p3568_3 := h3568c.2.2.2
                                      linarith only [h2, hlam, p3568_0]
                                    · have p3568_0 := h3568c.1
                                      have p3568_1 := h3568c.2.1
                                      have p3568_2 := h3568c.2.2.1
                                      have p3568_3 := h3568c.2.2.2
                                      linarith only [h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3568_1, u0elo0]
                                    · have p3568_0 := h3568c.1
                                      have p3568_1 := h3568c.2.1
                                      have p3568_2 := h3568c.2.2.1
                                      have p3568_3 := h3568c.2.2.2
                                      linarith only [h2, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3568_1, u0elo0]
                                    · have p3568_0 := h3568c.1
                                      have p3568_1 := h3568c.2.1
                                      have p3568_2 := h3568c.2.2.1
                                      have p3568_3 := h3568c.2.2.2
                                      linarith only [hlam, p3568_0]
                                    · have p3568_0 := h3568c.1
                                      have p3568_1 := h3568c.2.1
                                      have p3568_2 := h3568c.2.2.1
                                      have p3568_3 := h3568c.2.2.2
                                      linarith only [h2, hc15, hlam, hphi, ht0b, ht5b, p3568_1, u0elo0]
                                    · have p3568_0 := h3568c.1
                                      have p3568_1 := h3568c.2.1
                                      have p3568_2 := h3568c.2.2.1
                                      have p3568_3 := h3568c.2.2.2
                                      linarith only [h3, hlam, p3568_0]
                                    · have p3568_0 := h3568c.1
                                      have p3568_1 := h3568c.2.1
                                      have p3568_2 := h3568c.2.2.1
                                      have p3568_3 := h3568c.2.2.2
                                      linarith only [h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3568_1, u0elo0]
                                    · have p3568_0 := h3568c.1
                                      have p3568_1 := h3568c.2.1
                                      have p3568_2 := h3568c.2.2.1
                                      have p3568_3 := h3568c.2.2.2
                                      linarith only [h3, h3314, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3568_1, u0elo0]
                                    · have p3568_0 := h3568c.1
                                      have p3568_1 := h3568c.2.1
                                      have p3568_2 := h3568c.2.2.1
                                      have p3568_3 := h3568c.2.2.2
                                      linarith only [h3324, hlam, p3568_0]
                                    · have p3568_0 := h3568c.1
                                      have p3568_1 := h3568c.2.1
                                      have p3568_2 := h3568c.2.2.1
                                      have p3568_3 := h3568c.2.2.2
                                      linarith only [hlam, p3568_0]
                                  · linarith only [h3380, h3383, h3567, h4, hc34, hlam, ht01, ht12, ht23]
                                  · linarith only [h2, h3313, h3567, hlam, p3384_1, u0elo0]
                                  · rcases h1bigk with h3618c | h3618c | h3618c | h3618c | h3618c | h3618c | h3618c | h3618c | h3618c | h3618c | h3618c | h3618c | h3618c | h3618c | h3618c | h3618c | h3618c | h3618c | h3618c | h3618c | h3618c | h3618c | h3618c | h3618c | h3618c
                                    · have p3618_0 := h3618c.1
                                      have p3618_1 := h3618c.2.1
                                      have p3618_2 := h3618c.2.2.1
                                      have p3618_3 := h3618c.2.2.2
                                      linarith only [hlam, p3618_0]
                                    · have p3618_0 := h3618c.1
                                      have p3618_1 := h3618c.2.1
                                      have p3618_2 := h3618c.2.2.1
                                      have p3618_3 := h3618c.2.2.2
                                      rcases p3618_3 (m.d 0 1) (by simp) with h3620 | h3620
                                      · rcases p3618_3 (m.d 1 2) (by simp) with h3621 | h3621
                                        · linarith only [h3621, hlam, p3618_0]
                                        · rcases p3618_3 (m.d 1 3) (by simp) with h3623 | h3623
                                          · linarith only [h1, h3623, hlam]
                                          · linarith only [h3314, h3623, hlam]
                                      · linarith only [h3620, hlam, p3618_0]
                                    · have p3618_0 := h3618c.1
                                      have p3618_1 := h3618c.2.1
                                      have p3618_2 := h3618c.2.2.1
                                      have p3618_3 := h3618c.2.2.2
                                      rcases p3618_3 (m.d 0 1) (by simp) with h3627 | h3627
                                      · rcases p3618_3 (m.d 1 2) (by simp) with h3628 | h3628
                                        · linarith only [h0, h3628, hlam]
                                        · rcases p3618_3 (m.d 1 3) (by simp) with h3630 | h3630
                                          · linarith only [h3630, hlam, p3618_0]
                                          · rcases p3618_3 (m.d 1 4) (by simp) with h3632 | h3632
                                            · linarith only [h2, h3632, hlam]
                                            · linarith only [h3320, h3632, hlam]
                                      · linarith only [h3627, hlam, p3618_0]
                                    · have p3618_0 := h3618c.1
                                      have p3618_1 := h3618c.2.1
                                      have p3618_2 := h3618c.2.2.1
                                      have p3618_3 := h3618c.2.2.2
                                      linarith only [h3324, hc45, hlam, hphi, ht0b, ht5b, p3618_1, u0elo0]
                                    · have p3618_0 := h3618c.1
                                      have p3618_1 := h3618c.2.1
                                      have p3618_2 := h3618c.2.2.1
                                      have p3618_3 := h3618c.2.2.2
                                      rcases p3618_3 (m.d 0 1) (by simp) with h3637 | h3637
                                      · rcases p3618_3 (m.d 1 2) (by simp) with h3638 | h3638
                                        · linarith only [h0, h3638, hlam]
                                        · rcases p3618_3 (m.d 1 3) (by simp) with h3640 | h3640
                                          · linarith only [h1, h3640, hlam]
                                          · rcases p3618_3 (m.d 1 4) (by simp) with h3642 | h3642
                                            · linarith only [h2, h3642, hlam]
                                            · linarith only [h3324, h3642, hlam]
                                      · linarith only [h3637, hlam, p3618_0]
                                    · have p3618_0 := h3618c.1
                                      have p3618_1 := h3618c.2.1
                                      have p3618_2 := h3618c.2.2.1
                                      have p3618_3 := h3618c.2.2.2
                                      linarith only [h0, hlam, p3618_0]
                                    · have p3618_0 := h3618c.1
                                      have p3618_1 := h3618c.2.1
                                      have p3618_2 := h3618c.2.2.1
                                      have p3618_3 := h3618c.2.2.2
                                      linarith only [hlam, p3618_0]
                                    · have p3618_0 := h3618c.1
                                      have p3618_1 := h3618c.2.1
                                      have p3618_2 := h3618c.2.2.1
                                      have p3618_3 := h3618c.2.2.2
                                      linarith only [h3314, hlam, p3618_0]
                                    · have p3618_0 := h3618c.1
                                      have p3618_1 := h3618c.2.1
                                      have p3618_2 := h3618c.2.2.1
                                      have p3618_3 := h3618c.2.2.2
                                      linarith only [h3316, hlam, p3618_0]
                                    · have p3618_0 := h3618c.1
                                      have p3618_1 := h3618c.2.1
                                      have p3618_2 := h3618c.2.2.1
                                      have p3618_3 := h3618c.2.2.2
                                      linarith only [h3318, hlam, p3618_0]
                                    · have p3618_0 := h3618c.1
                                      have p3618_1 := h3618c.2.1
                                      have p3618_2 := h3618c.2.2.1
                                      have p3618_3 := h3618c.2.2.2
                                      linarith only [h1, hlam, p3618_0]
                                    · have p3618_0 := h3618c.1
                                      have p3618_1 := h3618c.2.1
                                      have p3618_2 := h3618c.2.2.1
                                      have p3618_3 := h3618c.2.2.2
                                      linarith only [h1, h2, h3313, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3384_1, p3618_1, u0elo0]
                                    · have p3618_0 := h3618c.1
                                      have p3618_1 := h3618c.2.1
                                      have p3618_2 := h3618c.2.2.1
                                      have p3618_3 := h3618c.2.2.2
                                      linarith only [hlam, p3618_0]
                                    · have p3618_0 := h3618c.1
                                      have p3618_1 := h3618c.2.1
                                      have p3618_2 := h3618c.2.2.1
                                      have p3618_3 := h3618c.2.2.2
                                      linarith only [h3320, hlam, p3618_1]
                                    · have p3618_0 := h3618c.1
                                      have p3618_1 := h3618c.2.1
                                      have p3618_2 := h3618c.2.2.1
                                      have p3618_3 := h3618c.2.2.2
                                      linarith only [h3322, hlam, p3618_1]
                                    · have p3618_0 := h3618c.1
                                      have p3618_1 := h3618c.2.1
                                      have p3618_2 := h3618c.2.2.1
                                      have p3618_3 := h3618c.2.2.2
                                      linarith only [h2, hlam, p3618_0]
                                    · have p3618_0 := h3618c.1
                                      have p3618_1 := h3618c.2.1
                                      have p3618_2 := h3618c.2.2.1
                                      have p3618_3 := h3618c.2.2.2
                                      linarith only [h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3618_1, u0elo0]
                                    · have p3618_0 := h3618c.1
                                      have p3618_1 := h3618c.2.1
                                      have p3618_2 := h3618c.2.2.1
                                      have p3618_3 := h3618c.2.2.2
                                      linarith only [h2, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3618_1, u0elo0]
                                    · have p3618_0 := h3618c.1
                                      have p3618_1 := h3618c.2.1
                                      have p3618_2 := h3618c.2.2.1
                                      have p3618_3 := h3618c.2.2.2
                                      linarith only [hlam, p3618_0]
                                    · have p3618_0 := h3618c.1
                                      have p3618_1 := h3618c.2.1
                                      have p3618_2 := h3618c.2.2.1
                                      have p3618_3 := h3618c.2.2.2
                                      linarith only [h2, hc15, hlam, hphi, ht0b, ht5b, p3618_1, u0elo0]
                                    · have p3618_0 := h3618c.1
                                      have p3618_1 := h3618c.2.1
                                      have p3618_2 := h3618c.2.2.1
                                      have p3618_3 := h3618c.2.2.2
                                      linarith only [h3, hlam, p3618_0]
                                    · have p3618_0 := h3618c.1
                                      have p3618_1 := h3618c.2.1
                                      have p3618_2 := h3618c.2.2.1
                                      have p3618_3 := h3618c.2.2.2
                                      linarith only [h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3618_1, u0elo0]
                                    · have p3618_0 := h3618c.1
                                      have p3618_1 := h3618c.2.1
                                      have p3618_2 := h3618c.2.2.1
                                      have p3618_3 := h3618c.2.2.2
                                      linarith only [h3, h3314, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3618_1, u0elo0]
                                    · have p3618_0 := h3618c.1
                                      have p3618_1 := h3618c.2.1
                                      have p3618_2 := h3618c.2.2.1
                                      have p3618_3 := h3618c.2.2.2
                                      linarith only [h3324, hlam, p3618_0]
                                    · have p3618_0 := h3618c.1
                                      have p3618_1 := h3618c.2.1
                                      have p3618_2 := h3618c.2.2.1
                                      have p3618_3 := h3618c.2.2.2
                                      linarith only [hlam, p3618_0]
                                  · rcases h1bigk with h3666c | h3666c | h3666c | h3666c | h3666c | h3666c | h3666c | h3666c | h3666c | h3666c | h3666c | h3666c | h3666c | h3666c | h3666c | h3666c | h3666c | h3666c | h3666c | h3666c | h3666c | h3666c | h3666c | h3666c | h3666c
                                    · have p3666_0 := h3666c.1
                                      have p3666_1 := h3666c.2.1
                                      have p3666_2 := h3666c.2.2.1
                                      have p3666_3 := h3666c.2.2.2
                                      linarith only [hlam, p3666_0]
                                    · have p3666_0 := h3666c.1
                                      have p3666_1 := h3666c.2.1
                                      have p3666_2 := h3666c.2.2.1
                                      have p3666_3 := h3666c.2.2.2
                                      rcases p3666_3 (m.d 0 1) (by simp) with h3668 | h3668
                                      · rcases p3666_3 (m.d 1 2) (by simp) with h3669 | h3669
                                        · linarith only [h3669, hlam, p3666_0]
                                        · rcases p3666_3 (m.d 1 3) (by simp) with h3671 | h3671
                                          · linarith only [h1, h3671, hlam]
                                          · linarith only [h3314, h3671, hlam]
                                      · linarith only [h3668, hlam, p3666_0]
                                    · have p3666_0 := h3666c.1
                                      have p3666_1 := h3666c.2.1
                                      have p3666_2 := h3666c.2.2.1
                                      have p3666_3 := h3666c.2.2.2
                                      rcases p3666_3 (m.d 0 1) (by simp) with h3675 | h3675
                                      · rcases p3666_3 (m.d 1 2) (by simp) with h3676 | h3676
                                        · linarith only [h0, h3676, hlam]
                                        · rcases p3666_3 (m.d 1 3) (by simp) with h3678 | h3678
                                          · linarith only [h3678, hlam, p3666_0]
                                          · rcases p3666_3 (m.d 1 4) (by simp) with h3680 | h3680
                                            · linarith only [h2, h3680, hlam]
                                            · linarith only [h3320, h3680, hlam]
                                      · linarith only [h3675, hlam, p3666_0]
                                    · have p3666_0 := h3666c.1
                                      have p3666_1 := h3666c.2.1
                                      have p3666_2 := h3666c.2.2.1
                                      have p3666_3 := h3666c.2.2.2
                                      linarith only [h3324, hc45, hlam, hphi, ht0b, ht5b, p3666_1, u0elo0]
                                    · have p3666_0 := h3666c.1
                                      have p3666_1 := h3666c.2.1
                                      have p3666_2 := h3666c.2.2.1
                                      have p3666_3 := h3666c.2.2.2
                                      rcases p3666_3 (m.d 0 1) (by simp) with h3685 | h3685
                                      · rcases p3666_3 (m.d 1 2) (by simp) with h3686 | h3686
                                        · linarith only [h0, h3686, hlam]
                                        · rcases p3666_3 (m.d 1 3) (by simp) with h3688 | h3688
                                          · linarith only [h1, h3688, hlam]
                                          · rcases p3666_3 (m.d 1 4) (by simp) with h3690 | h3690
                                            · linarith only [h2, h3690, hlam]
                                            · linarith only [h3324, h3690, hlam]
                                      · linarith only [h3685, hlam, p3666_0]
                                    · have p3666_0 := h3666c.1
                                      have p3666_1 := h3666c.2.1
                                      have p3666_2 := h3666c.2.2.1
                                      have p3666_3 := h3666c.2.2.2
                                      linarith only [h0, hlam, p3666_0]
                                    · have p3666_0 := h3666c.1
                                      have p3666_1 := h3666c.2.1
                                      have p3666_2 := h3666c.2.2.1
                                      have p3666_3 := h3666c.2.2.2
                                      linarith only [hlam, p3666_0]
                                    · have p3666_0 := h3666c.1
                                      have p3666_1 := h3666c.2.1
                                      have p3666_2 := h3666c.2.2.1
                                      have p3666_3 := h3666c.2.2.2
                                      linarith only [h3314, hlam, p3666_0]
                                    · have p3666_0 := h3666c.1
                                      have p3666_1 := h3666c.2.1
                                      have p3666_2 := h3666c.2.2.1
                                      have p3666_3 := h3666c.2.2.2
                                      linarith only [h3316, hlam, p3666_0]
                                    · have p3666_0 := h3666c.1
                                      have p3666_1 := h3666c.2.1
                                      have p3666_2 := h3666c.2.2.1
                                      have p3666_3 := h3666c.2.2.2
                                      linarith only [h3318, hlam, p3666_0]
                                    · have p3666_0 := h3666c.1
                                      have p3666_1 := h3666c.2.1
                                      have p3666_2 := h3666c.2.2.1
                                      have p3666_3 := h3666c.2.2.2
                                      linarith only [h1, hlam, p3666_0]
                                    · have p3666_0 := h3666c.1
                                      have p3666_1 := h3666c.2.1
                                      have p3666_2 := h3666c.2.2.1
                                      have p3666_3 := h3666c.2.2.2
                                      linarith only [h1, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3666_1, u0elo0]
                                    · have p3666_0 := h3666c.1
                                      have p3666_1 := h3666c.2.1
                                      have p3666_2 := h3666c.2.2.1
                                      have p3666_3 := h3666c.2.2.2
                                      linarith only [hlam, p3666_0]
                                    · have p3666_0 := h3666c.1
                                      have p3666_1 := h3666c.2.1
                                      have p3666_2 := h3666c.2.2.1
                                      have p3666_3 := h3666c.2.2.2
                                      linarith only [h3320, hlam, p3666_1]
                                    · have p3666_0 := h3666c.1
                                      have p3666_1 := h3666c.2.1
                                      have p3666_2 := h3666c.2.2.1
                                      have p3666_3 := h3666c.2.2.2
                                      linarith only [h3322, hlam, p3666_1]
                                    · have p3666_0 := h3666c.1
                                      have p3666_1 := h3666c.2.1
                                      have p3666_2 := h3666c.2.2.1
                                      have p3666_3 := h3666c.2.2.2
                                      linarith only [h2, hlam, p3666_0]
                                    · have p3666_0 := h3666c.1
                                      have p3666_1 := h3666c.2.1
                                      have p3666_2 := h3666c.2.2.1
                                      have p3666_3 := h3666c.2.2.2
                                      linarith only [h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3666_1, u0elo0]
                                    · have p3666_0 := h3666c.1
                                      have p3666_1 := h3666c.2.1
                                      have p3666_2 := h3666c.2.2.1
                                      have p3666_3 := h3666c.2.2.2
                                      linarith only [h2, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3666_1, u0elo0]
                                    · have p3666_0 := h3666c.1
                                      have p3666_1 := h3666c.2.1
                                      have p3666_2 := h3666c.2.2.1
                                      have p3666_3 := h3666c.2.2.2
                                      linarith only [hlam, p3666_0]
                                    · have p3666_0 := h3666c.1
                                      have p3666_1 := h3666c.2.1
                                      have p3666_2 := h3666c.2.2.1
                                      have p3666_3 := h3666c.2.2.2
                                      linarith only [h2, hc15, hlam, hphi, ht0b, ht5b, p3666_1, u0elo0]
                                    · have p3666_0 := h3666c.1
                                      have p3666_1 := h3666c.2.1
                                      have p3666_2 := h3666c.2.2.1
                                      have p3666_3 := h3666c.2.2.2
                                      linarith only [h3, hlam, p3666_0]
                                    · have p3666_0 := h3666c.1
                                      have p3666_1 := h3666c.2.1
                                      have p3666_2 := h3666c.2.2.1
                                      have p3666_3 := h3666c.2.2.2
                                      linarith only [h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3666_1, u0elo0]
                                    · have p3666_0 := h3666c.1
                                      have p3666_1 := h3666c.2.1
                                      have p3666_2 := h3666c.2.2.1
                                      have p3666_3 := h3666c.2.2.2
                                      linarith only [h3, h3314, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3666_1, u0elo0]
                                    · have p3666_0 := h3666c.1
                                      have p3666_1 := h3666c.2.1
                                      have p3666_2 := h3666c.2.2.1
                                      have p3666_3 := h3666c.2.2.2
                                      linarith only [h3324, hlam, p3666_0]
                                    · have p3666_0 := h3666c.1
                                      have p3666_1 := h3666c.2.1
                                      have p3666_2 := h3666c.2.2.1
                                      have p3666_3 := h3666c.2.2.2
                                      linarith only [hlam, p3666_0]
                                · linarith only [h3197, h3566, hlam]
                              · linarith only [h1947, h3565, hlam]
                        · linarith only [h1, h3560, hlam]
                      · have p3384_0 := h3384c.1
                        have p3384_1 := h3384c.2.1
                        have p3384_2 := h3384c.2.2.1
                        have p3384_3 := h3384c.2.2.2
                        linarith only [h3313, hlam, p3384_1]
                      · have p3384_0 := h3384c.1
                        have p3384_1 := h3384c.2.1
                        have p3384_2 := h3384c.2.2.1
                        have p3384_3 := h3384c.2.2.2
                        linarith only [hlam, p3384_0]
                    · linarith only [h1947, h3313, h3383, hlam]
                  · linarith only [h1304, h2, h3324, h3382, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h3721 | h3721
              · linarith only [h1947, h3313, h3314, h3320, h3324, h3721, hc12, hc23, hlam, hphi]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h3723 | h3723
                · linarith only [h1, h3197, h3314, h3721, h3723, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3725 | h3725
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3726 | h3726
                    · rcases h0bigk with h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c
                      · have p3727_0 := h3727c.1
                        have p3727_1 := h3727c.2.1
                        have p3727_2 := h3727c.2.2.1
                        have p3727_3 := h3727c.2.2.2
                        linarith only [hlam, p3727_0]
                      · have p3727_0 := h3727c.1
                        have p3727_1 := h3727c.2.1
                        have p3727_2 := h3727c.2.2.1
                        have p3727_3 := h3727c.2.2.2
                        rcases p3727_3 (m.d 0 1) (by simp) with h3729 | h3729
                        · rcases p3727_3 (m.d 0 2) (by simp) with h3730 | h3730
                          · linarith only [h0, h3730, hlam]
                          · rcases p3727_3 (m.d 0 3) (by simp) with h3732 | h3732
                            · linarith only [h1, h3732, hlam]
                            · linarith only [h3732, h4, hlam]
                        · linarith only [h0, h3729, hlam]
                      · have p3727_0 := h3727c.1
                        have p3727_1 := h3727c.2.1
                        have p3727_2 := h3727c.2.2.1
                        have p3727_3 := h3727c.2.2.2
                        rcases p3727_3 (m.d 0 1) (by simp) with h3736 | h3736
                        · rcases p3727_3 (m.d 0 2) (by simp) with h3737 | h3737
                          · linarith only [h0, h3737, hlam]
                          · rcases p3727_3 (m.d 0 3) (by simp) with h3739 | h3739
                            · linarith only [h1, h3739, hlam]
                            · rcases p3727_3 (m.d 0 4) (by simp) with h3741 | h3741
                              · linarith only [h2, h3741, hlam]
                              · linarith only [h1947, h3741, hlam]
                        · linarith only [h1, h3736, hlam]
                      · have p3727_0 := h3727c.1
                        have p3727_1 := h3727c.2.1
                        have p3727_2 := h3727c.2.2.1
                        have p3727_3 := h3727c.2.2.2
                        linarith only [h3313, h3314, h3320, h3324, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3727_1, u0elo0]
                      · have p3727_0 := h3727c.1
                        have p3727_1 := h3727c.2.1
                        have p3727_2 := h3727c.2.2.1
                        have p3727_3 := h3727c.2.2.2
                        linarith only [h3313, h3314, h3320, h3324, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3727_1, u0elo0]
                      · have p3727_0 := h3727c.1
                        have p3727_1 := h3727c.2.1
                        have p3727_2 := h3727c.2.2.1
                        have p3727_3 := h3727c.2.2.2
                        linarith only [h0, hlam, p3727_0]
                      · have p3727_0 := h3727c.1
                        have p3727_1 := h3727c.2.1
                        have p3727_2 := h3727c.2.2.1
                        have p3727_3 := h3727c.2.2.2
                        linarith only [hlam, p3727_0]
                      · have p3727_0 := h3727c.1
                        have p3727_1 := h3727c.2.1
                        have p3727_2 := h3727c.2.2.1
                        have p3727_3 := h3727c.2.2.2
                        linarith only [h4, hlam, p3727_0]
                      · have p3727_0 := h3727c.1
                        have p3727_1 := h3727c.2.1
                        have p3727_2 := h3727c.2.2.1
                        have p3727_3 := h3727c.2.2.2
                        linarith only [h1304, hlam, p3727_1]
                      · have p3727_0 := h3727c.1
                        have p3727_1 := h3727c.2.1
                        have p3727_2 := h3727c.2.2.1
                        have p3727_3 := h3727c.2.2.2
                        linarith only [h1819, hlam, p3727_0]
                      · have p3727_0 := h3727c.1
                        have p3727_1 := h3727c.2.1
                        have p3727_2 := h3727c.2.2.1
                        have p3727_3 := h3727c.2.2.2
                        linarith only [h1, hlam, p3727_1]
                      · have p3727_0 := h3727c.1
                        have p3727_1 := h3727c.2.1
                        have p3727_2 := h3727c.2.2.1
                        have p3727_3 := h3727c.2.2.2
                        linarith only [h0, h3723, h3726, h4, hc12, hc34, hlam, hphi, ht23, p3727_1]
                      · have p3727_0 := h3727c.1
                        have p3727_1 := h3727c.2.1
                        have p3727_2 := h3727c.2.2.1
                        have p3727_3 := h3727c.2.2.2
                        linarith only [hlam, p3727_0]
                      · have p3727_0 := h3727c.1
                        have p3727_1 := h3727c.2.1
                        have p3727_2 := h3727c.2.2.1
                        have p3727_3 := h3727c.2.2.2
                        linarith only [h1947, hlam, p3727_1]
                      · have p3727_0 := h3727c.1
                        have p3727_1 := h3727c.2.1
                        have p3727_2 := h3727c.2.2.1
                        have p3727_3 := h3727c.2.2.2
                        linarith only [h3197, hlam, p3727_1]
                      · have p3727_0 := h3727c.1
                        have p3727_1 := h3727c.2.1
                        have p3727_2 := h3727c.2.2.1
                        have p3727_3 := h3727c.2.2.2
                        linarith only [h2, hlam, p3727_0]
                      · have p3727_0 := h3727c.1
                        have p3727_1 := h3727c.2.1
                        have p3727_2 := h3727c.2.2.1
                        have p3727_3 := h3727c.2.2.2
                        rcases p3727_3 (m.d 0 1) (by simp) with h3758 | h3758
                        · rcases p3727_3 (m.d 0 2) (by simp) with h3759 | h3759
                          · linarith only [h1304, h3759, hlam]
                          · rcases p3727_3 (m.d 0 3) (by simp) with h3761 | h3761
                            · linarith only [h1947, h3761, hlam]
                            · linarith only [h3761, h4, hlam]
                        · linarith only [h0, h3758, hlam]
                      · have p3727_0 := h3727c.1
                        have p3727_1 := h3727c.2.1
                        have p3727_2 := h3727c.2.2.1
                        have p3727_3 := h3727c.2.2.2
                        rcases p3727_3 (m.d 0 1) (by simp) with h3765 | h3765
                        · rcases p3727_3 (m.d 0 2) (by simp) with h3766 | h3766
                          · linarith only [h1304, h3766, hlam]
                          · rcases p3727_3 (m.d 0 3) (by simp) with h3768 | h3768
                            · linarith only [h1947, h3768, hlam]
                            · rcases p3727_3 (m.d 0 4) (by simp) with h3770 | h3770
                              · rcases p3727_3 (m.d 0 5) (by simp) with h3771 | h3771
                                · linarith only [h3313, h3771, hlam]
                                · linarith only [h3197, h3771, hlam]
                              · linarith only [h1947, h3770, hlam]
                        · linarith only [h1, h3765, hlam]
                      · have p3727_0 := h3727c.1
                        have p3727_1 := h3727c.2.1
                        have p3727_2 := h3727c.2.2.1
                        have p3727_3 := h3727c.2.2.2
                        linarith only [hlam, p3727_0]
                      · have p3727_0 := h3727c.1
                        have p3727_1 := h3727c.2.1
                        have p3727_2 := h3727c.2.2.1
                        have p3727_3 := h3727c.2.2.2
                        linarith only [h3313, h3314, h3320, h3324, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3727_1, u0elo3]
                      · have p3727_0 := h3727c.1
                        have p3727_1 := h3727c.2.1
                        have p3727_2 := h3727c.2.2.1
                        have p3727_3 := h3727c.2.2.2
                        linarith only [h3, hlam, p3727_0]
                      · have p3727_0 := h3727c.1
                        have p3727_1 := h3727c.2.1
                        have p3727_2 := h3727c.2.2.1
                        have p3727_3 := h3727c.2.2.2
                        rcases p3727_3 (m.d 0 1) (by simp) with h3779 | h3779
                        · rcases p3727_3 (m.d 0 2) (by simp) with h3780 | h3780
                          · linarith only [h1819, h3780, hlam]
                          · rcases p3727_3 (m.d 0 3) (by simp) with h3782 | h3782
                            · linarith only [h3197, h3782, hlam]
                            · linarith only [h3782, h4, hlam]
                        · linarith only [h0, h3779, hlam]
                      · have p3727_0 := h3727c.1
                        have p3727_1 := h3727c.2.1
                        have p3727_2 := h3727c.2.2.1
                        have p3727_3 := h3727c.2.2.2
                        rcases p3727_3 (m.d 0 1) (by simp) with h3786 | h3786
                        · rcases p3727_3 (m.d 0 2) (by simp) with h3787 | h3787
                          · linarith only [h1819, h3787, hlam]
                          · rcases p3727_3 (m.d 0 3) (by simp) with h3789 | h3789
                            · linarith only [h3197, h3789, hlam]
                            · rcases p3727_3 (m.d 0 4) (by simp) with h3791 | h3791
                              · rcases p3727_3 (m.d 0 5) (by simp) with h3792 | h3792
                                · rcases h0emin with h3793 | h3793 | h3793 | h3793 | h3793
                                  · rcases h1bigk with h3794c | h3794c | h3794c | h3794c | h3794c | h3794c | h3794c | h3794c | h3794c | h3794c | h3794c | h3794c | h3794c | h3794c | h3794c | h3794c | h3794c | h3794c | h3794c | h3794c | h3794c | h3794c | h3794c | h3794c | h3794c
                                    · have p3794_0 := h3794c.1
                                      have p3794_1 := h3794c.2.1
                                      have p3794_2 := h3794c.2.2.1
                                      have p3794_3 := h3794c.2.2.2
                                      linarith only [hlam, p3794_0]
                                    · have p3794_0 := h3794c.1
                                      have p3794_1 := h3794c.2.1
                                      have p3794_2 := h3794c.2.2.1
                                      have p3794_3 := h3794c.2.2.2
                                      rcases p3794_3 (m.d 0 1) (by simp) with h3796 | h3796
                                      · rcases p3794_3 (m.d 1 2) (by simp) with h3797 | h3797
                                        · linarith only [h3797, hlam, p3794_0]
                                        · rcases p3794_3 (m.d 1 3) (by simp) with h3799 | h3799
                                          · linarith only [h1, h3799, hlam]
                                          · linarith only [h3314, h3799, hlam]
                                      · linarith only [h3796, hlam, p3794_0]
                                    · have p3794_0 := h3794c.1
                                      have p3794_1 := h3794c.2.1
                                      have p3794_2 := h3794c.2.2.1
                                      have p3794_3 := h3794c.2.2.2
                                      rcases p3794_3 (m.d 0 1) (by simp) with h3803 | h3803
                                      · rcases p3794_3 (m.d 1 2) (by simp) with h3804 | h3804
                                        · linarith only [h0, h3804, hlam]
                                        · rcases p3794_3 (m.d 1 3) (by simp) with h3806 | h3806
                                          · linarith only [h3806, hlam, p3794_0]
                                          · rcases p3794_3 (m.d 1 4) (by simp) with h3808 | h3808
                                            · linarith only [h2, h3808, hlam]
                                            · linarith only [h3320, h3808, hlam]
                                      · linarith only [h3803, hlam, p3794_0]
                                    · have p3794_0 := h3794c.1
                                      have p3794_1 := h3794c.2.1
                                      have p3794_2 := h3794c.2.2.1
                                      have p3794_3 := h3794c.2.2.2
                                      rcases p3794_3 (m.d 0 1) (by simp) with h3812 | h3812
                                      · rcases p3794_3 (m.d 1 2) (by simp) with h3813 | h3813
                                        · linarith only [h0, h3813, hlam]
                                        · rcases p3794_3 (m.d 1 3) (by simp) with h3815 | h3815
                                          · linarith only [h1, h3815, hlam]
                                          · rcases p3794_3 (m.d 1 4) (by simp) with h3817 | h3817
                                            · linarith only [h3817, hlam, p3794_0]
                                            · rcases p3794_3 (m.d 1 5) (by simp) with h3819 | h3819
                                              · linarith only [h3, h3819, hlam]
                                              · linarith only [h3324, h3819, hlam]
                                      · linarith only [h3812, hlam, p3794_0]
                                    · have p3794_0 := h3794c.1
                                      have p3794_1 := h3794c.2.1
                                      have p3794_2 := h3794c.2.2.1
                                      have p3794_3 := h3794c.2.2.2
                                      rcases p3794_3 (m.d 0 1) (by simp) with h3823 | h3823
                                      · rcases p3794_3 (m.d 1 2) (by simp) with h3824 | h3824
                                        · linarith only [h0, h3824, hlam]
                                        · rcases p3794_3 (m.d 1 3) (by simp) with h3826 | h3826
                                          · linarith only [h1, h3826, hlam]
                                          · rcases p3794_3 (m.d 1 4) (by simp) with h3828 | h3828
                                            · linarith only [h2, h3828, hlam]
                                            · rcases p3794_3 (m.d 1 5) (by simp) with h3830 | h3830
                                              · linarith only [h3830, hlam, p3794_0]
                                              · rcases h3bigk with h3832c | h3832c | h3832c | h3832c | h3832c | h3832c | h3832c | h3832c | h3832c | h3832c | h3832c | h3832c | h3832c | h3832c | h3832c | h3832c | h3832c | h3832c | h3832c | h3832c | h3832c | h3832c | h3832c | h3832c | h3832c
                                                · have p3832_0 := h3832c.1
                                                  have p3832_1 := h3832c.2.1
                                                  have p3832_2 := h3832c.2.2.1
                                                  have p3832_3 := h3832c.2.2.2
                                                  linarith only [hlam, p3832_0]
                                                · have p3832_0 := h3832c.1
                                                  have p3832_1 := h3832c.2.1
                                                  have p3832_2 := h3832c.2.2.1
                                                  have p3832_3 := h3832c.2.2.2
                                                  linarith only [h3314, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3727_1, p3832_1, u0elo4]
                                                · have p3832_0 := h3832c.1
                                                  have p3832_1 := h3832c.2.1
                                                  have p3832_2 := h3832c.2.2.1
                                                  have p3832_3 := h3832c.2.2.2
                                                  linarith only [h4, hlam, p3832_1]
                                                · have p3832_0 := h3832c.1
                                                  have p3832_1 := h3832c.2.1
                                                  have p3832_2 := h3832c.2.2.1
                                                  have p3832_3 := h3832c.2.2.2
                                                  linarith only [h1947, hlam, p3832_0]
                                                · have p3832_0 := h3832c.1
                                                  have p3832_1 := h3832c.2.1
                                                  have p3832_2 := h3832c.2.2.1
                                                  have p3832_3 := h3832c.2.2.2
                                                  linarith only [h3197, hlam, p3832_0]
                                                · have p3832_0 := h3832c.1
                                                  have p3832_1 := h3832c.2.1
                                                  have p3832_2 := h3832c.2.2.1
                                                  have p3832_3 := h3832c.2.2.2
                                                  linarith only [h1, hlam, p3832_0]
                                                · have p3832_0 := h3832c.1
                                                  have p3832_1 := h3832c.2.1
                                                  have p3832_2 := h3832c.2.2.1
                                                  have p3832_3 := h3832c.2.2.2
                                                  linarith only [hlam, p3832_0]
                                                · have p3832_0 := h3832c.1
                                                  have p3832_1 := h3832c.2.1
                                                  have p3832_2 := h3832c.2.2.1
                                                  have p3832_3 := h3832c.2.2.2
                                                  linarith only [h3314, hlam, p3832_1]
                                                · have p3832_0 := h3832c.1
                                                  have p3832_1 := h3832c.2.1
                                                  have p3832_2 := h3832c.2.2.1
                                                  have p3832_3 := h3832c.2.2.2
                                                  linarith only [h3320, hlam, p3832_0]
                                                · have p3832_0 := h3832c.1
                                                  have p3832_1 := h3832c.2.1
                                                  have p3832_2 := h3832c.2.2.1
                                                  have p3832_3 := h3832c.2.2.2
                                                  linarith only [h3322, hlam, p3832_0]
                                                · have p3832_0 := h3832c.1
                                                  have p3832_1 := h3832c.2.1
                                                  have p3832_2 := h3832c.2.2.1
                                                  have p3832_3 := h3832c.2.2.2
                                                  linarith only [h3723, h3726, hc03, hc34, hlam, hphi, p3832_1]
                                                · have p3832_0 := h3832c.1
                                                  have p3832_1 := h3832c.2.1
                                                  have p3832_2 := h3832c.2.2.1
                                                  have p3832_3 := h3832c.2.2.2
                                                  linarith only [h3314, h3723, h3726, hc12, hc34, hlam, hphi, ht23, p3832_1]
                                                · have p3832_0 := h3832c.1
                                                  have p3832_1 := h3832c.2.1
                                                  have p3832_2 := h3832c.2.2.1
                                                  have p3832_3 := h3832c.2.2.2
                                                  linarith only [hlam, p3832_0]
                                                · have p3832_0 := h3832c.1
                                                  have p3832_1 := h3832c.2.1
                                                  have p3832_2 := h3832c.2.2.1
                                                  have p3832_3 := h3832c.2.2.2
                                                  linarith only [h3721, hlam, p3832_0]
                                                · have p3832_0 := h3832c.1
                                                  have p3832_1 := h3832c.2.1
                                                  have p3832_2 := h3832c.2.2.1
                                                  have p3832_3 := h3832c.2.2.2
                                                  linarith only [h3723, hlam, p3832_0]
                                                · have p3832_0 := h3832c.1
                                                  have p3832_1 := h3832c.2.1
                                                  have p3832_2 := h3832c.2.2.1
                                                  have p3832_3 := h3832c.2.2.2
                                                  rcases p3832_3 (m.d 0 3) (by simp) with h3848 | h3848
                                                  · linarith only [h3848, hlam, p3832_0]
                                                  · rcases p3832_3 (m.d 1 3) (by simp) with h3850 | h3850
                                                    · linarith only [h3320, h3850, hlam]
                                                    · rcases p3832_3 (m.d 2 3) (by simp) with h3852 | h3852
                                                      · linarith only [h3721, h3852, hlam]
                                                      · linarith only [h3852, h4, hlam]
                                                · have p3832_0 := h3832c.1
                                                  have p3832_1 := h3832c.2.1
                                                  have p3832_2 := h3832c.2.2.1
                                                  have p3832_3 := h3832c.2.2.2
                                                  rcases p3832_3 (m.d 0 3) (by simp) with h3855 | h3855
                                                  · linarith only [h1947, h3855, hlam]
                                                  · linarith only [h1, h3855, hlam]
                                                · have p3832_0 := h3832c.1
                                                  have p3832_1 := h3832c.2.1
                                                  have p3832_2 := h3832c.2.2.1
                                                  have p3832_3 := h3832c.2.2.2
                                                  linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p3832_1]
                                                · have p3832_0 := h3832c.1
                                                  have p3832_1 := h3832c.2.1
                                                  have p3832_2 := h3832c.2.2.1
                                                  have p3832_3 := h3832c.2.2.2
                                                  linarith only [hlam, p3832_0]
                                                · have p3832_0 := h3832c.1
                                                  have p3832_1 := h3832c.2.1
                                                  have p3832_2 := h3832c.2.2.1
                                                  have p3832_3 := h3832c.2.2.2
                                                  linarith only [h1, h3197, h3314, hc12, hc34, hlam, hphi, ht23, p3832_1]
                                                · have p3832_0 := h3832c.1
                                                  have p3832_1 := h3832c.2.1
                                                  have p3832_2 := h3832c.2.2.1
                                                  have p3832_3 := h3832c.2.2.2
                                                  rcases p3832_3 (m.d 0 3) (by simp) with h3861 | h3861
                                                  · linarith only [h3861, hlam, p3832_0]
                                                  · rcases p3832_3 (m.d 1 3) (by simp) with h3863 | h3863
                                                    · linarith only [h3322, h3863, hlam]
                                                    · rcases p3832_3 (m.d 2 3) (by simp) with h3865 | h3865
                                                      · linarith only [h3723, h3865, hlam]
                                                      · linarith only [h3865, h4, hlam]
                                                · have p3832_0 := h3832c.1
                                                  have p3832_1 := h3832c.2.1
                                                  have p3832_2 := h3832c.2.2.1
                                                  have p3832_3 := h3832c.2.2.2
                                                  rcases p3832_3 (m.d 0 3) (by simp) with h3868 | h3868
                                                  · linarith only [h3197, h3868, hlam]
                                                  · linarith only [h1, h3868, hlam]
                                                · have p3832_0 := h3832c.1
                                                  have p3832_1 := h3832c.2.1
                                                  have p3832_2 := h3832c.2.2.1
                                                  have p3832_3 := h3832c.2.2.2
                                                  linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p3832_1]
                                                · have p3832_0 := h3832c.1
                                                  have p3832_1 := h3832c.2.1
                                                  have p3832_2 := h3832c.2.2.1
                                                  have p3832_3 := h3832c.2.2.2
                                                  linarith only [h3726, hlam, p3832_0]
                                                · have p3832_0 := h3832c.1
                                                  have p3832_1 := h3832c.2.1
                                                  have p3832_2 := h3832c.2.2.1
                                                  have p3832_3 := h3832c.2.2.2
                                                  linarith only [hlam, p3832_0]
                                      · linarith only [h3823, hlam, p3794_0]
                                    · have p3794_0 := h3794c.1
                                      have p3794_1 := h3794c.2.1
                                      have p3794_2 := h3794c.2.2.1
                                      have p3794_3 := h3794c.2.2.2
                                      linarith only [h0, hlam, p3794_0]
                                    · have p3794_0 := h3794c.1
                                      have p3794_1 := h3794c.2.1
                                      have p3794_2 := h3794c.2.2.1
                                      have p3794_3 := h3794c.2.2.2
                                      linarith only [hlam, p3794_0]
                                    · have p3794_0 := h3794c.1
                                      have p3794_1 := h3794c.2.1
                                      have p3794_2 := h3794c.2.2.1
                                      have p3794_3 := h3794c.2.2.2
                                      linarith only [h3314, hlam, p3794_0]
                                    · have p3794_0 := h3794c.1
                                      have p3794_1 := h3794c.2.1
                                      have p3794_2 := h3794c.2.2.1
                                      have p3794_3 := h3794c.2.2.2
                                      linarith only [h3316, hlam, p3794_0]
                                    · have p3794_0 := h3794c.1
                                      have p3794_1 := h3794c.2.1
                                      have p3794_2 := h3794c.2.2.1
                                      have p3794_3 := h3794c.2.2.2
                                      linarith only [h3318, hlam, p3794_0]
                                    · have p3794_0 := h3794c.1
                                      have p3794_1 := h3794c.2.1
                                      have p3794_2 := h3794c.2.2.1
                                      have p3794_3 := h3794c.2.2.2
                                      linarith only [h1, hlam, p3794_0]
                                    · have p3794_0 := h3794c.1
                                      have p3794_1 := h3794c.2.1
                                      have p3794_2 := h3794c.2.2.1
                                      have p3794_3 := h3794c.2.2.2
                                      linarith only [h3320, h3324, hc12, hc45, hlam, hphi, ht23, ht34, p3794_1]
                                    · have p3794_0 := h3794c.1
                                      have p3794_1 := h3794c.2.1
                                      have p3794_2 := h3794c.2.2.1
                                      have p3794_3 := h3794c.2.2.2
                                      linarith only [hlam, p3794_0]
                                    · have p3794_0 := h3794c.1
                                      have p3794_1 := h3794c.2.1
                                      have p3794_2 := h3794c.2.2.1
                                      have p3794_3 := h3794c.2.2.2
                                      linarith only [h3320, hlam, p3794_1]
                                    · have p3794_0 := h3794c.1
                                      have p3794_1 := h3794c.2.1
                                      have p3794_2 := h3794c.2.2.1
                                      have p3794_3 := h3794c.2.2.2
                                      linarith only [h3322, hlam, p3794_1]
                                    · have p3794_0 := h3794c.1
                                      have p3794_1 := h3794c.2.1
                                      have p3794_2 := h3794c.2.2.1
                                      have p3794_3 := h3794c.2.2.2
                                      linarith only [h2, hlam, p3794_0]
                                    · have p3794_0 := h3794c.1
                                      have p3794_1 := h3794c.2.1
                                      have p3794_2 := h3794c.2.2.1
                                      have p3794_3 := h3794c.2.2.2
                                      linarith only [h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3794_1, u0elo0]
                                    · have p3794_0 := h3794c.1
                                      have p3794_1 := h3794c.2.1
                                      have p3794_2 := h3794c.2.2.1
                                      have p3794_3 := h3794c.2.2.2
                                      linarith only [h2, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3794_1, u0elo0]
                                    · have p3794_0 := h3794c.1
                                      have p3794_1 := h3794c.2.1
                                      have p3794_2 := h3794c.2.2.1
                                      have p3794_3 := h3794c.2.2.2
                                      linarith only [hlam, p3794_0]
                                    · have p3794_0 := h3794c.1
                                      have p3794_1 := h3794c.2.1
                                      have p3794_2 := h3794c.2.2.1
                                      have p3794_3 := h3794c.2.2.2
                                      linarith only [h3324, hlam, p3794_1]
                                    · have p3794_0 := h3794c.1
                                      have p3794_1 := h3794c.2.1
                                      have p3794_2 := h3794c.2.2.1
                                      have p3794_3 := h3794c.2.2.2
                                      linarith only [h3, hlam, p3794_0]
                                    · have p3794_0 := h3794c.1
                                      have p3794_1 := h3794c.2.1
                                      have p3794_2 := h3794c.2.2.1
                                      have p3794_3 := h3794c.2.2.2
                                      linarith only [h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3794_1, u0elo0]
                                    · have p3794_0 := h3794c.1
                                      have p3794_1 := h3794c.2.1
                                      have p3794_2 := h3794c.2.2.1
                                      have p3794_3 := h3794c.2.2.2
                                      linarith only [h3, h3314, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3794_1, u0elo0]
                                    · have p3794_0 := h3794c.1
                                      have p3794_1 := h3794c.2.1
                                      have p3794_2 := h3794c.2.2.1
                                      have p3794_3 := h3794c.2.2.2
                                      linarith only [h2, h3313, h3324, hc14, hlam, hphi, ht0b, ht45, ht5b, p3794_1, u0elo0]
                                    · have p3794_0 := h3794c.1
                                      have p3794_1 := h3794c.2.1
                                      have p3794_2 := h3794c.2.2.1
                                      have p3794_3 := h3794c.2.2.2
                                      linarith only [hlam, p3794_0]
                                  · linarith only [h2, h3313, h3793, h4, hlam, p3727_1, u0elo0]
                                  · linarith only [h2, h3313, h3793, hlam, p3727_1, u0elo0]
                                  · rcases h1bigk with h3897c | h3897c | h3897c | h3897c | h3897c | h3897c | h3897c | h3897c | h3897c | h3897c | h3897c | h3897c | h3897c | h3897c | h3897c | h3897c | h3897c | h3897c | h3897c | h3897c | h3897c | h3897c | h3897c | h3897c | h3897c
                                    · have p3897_0 := h3897c.1
                                      have p3897_1 := h3897c.2.1
                                      have p3897_2 := h3897c.2.2.1
                                      have p3897_3 := h3897c.2.2.2
                                      linarith only [hlam, p3897_0]
                                    · have p3897_0 := h3897c.1
                                      have p3897_1 := h3897c.2.1
                                      have p3897_2 := h3897c.2.2.1
                                      have p3897_3 := h3897c.2.2.2
                                      rcases p3897_3 (m.d 0 1) (by simp) with h3899 | h3899
                                      · rcases p3897_3 (m.d 1 2) (by simp) with h3900 | h3900
                                        · linarith only [h3900, hlam, p3897_0]
                                        · rcases p3897_3 (m.d 1 3) (by simp) with h3902 | h3902
                                          · linarith only [h1, h3902, hlam]
                                          · linarith only [h3314, h3902, hlam]
                                      · linarith only [h3899, hlam, p3897_0]
                                    · have p3897_0 := h3897c.1
                                      have p3897_1 := h3897c.2.1
                                      have p3897_2 := h3897c.2.2.1
                                      have p3897_3 := h3897c.2.2.2
                                      rcases p3897_3 (m.d 0 1) (by simp) with h3906 | h3906
                                      · rcases p3897_3 (m.d 1 2) (by simp) with h3907 | h3907
                                        · linarith only [h0, h3907, hlam]
                                        · rcases p3897_3 (m.d 1 3) (by simp) with h3909 | h3909
                                          · linarith only [h3909, hlam, p3897_0]
                                          · rcases p3897_3 (m.d 1 4) (by simp) with h3911 | h3911
                                            · linarith only [h2, h3911, hlam]
                                            · linarith only [h3320, h3911, hlam]
                                      · linarith only [h3906, hlam, p3897_0]
                                    · have p3897_0 := h3897c.1
                                      have p3897_1 := h3897c.2.1
                                      have p3897_2 := h3897c.2.2.1
                                      have p3897_3 := h3897c.2.2.2
                                      rcases p3897_3 (m.d 0 1) (by simp) with h3915 | h3915
                                      · rcases p3897_3 (m.d 1 2) (by simp) with h3916 | h3916
                                        · linarith only [h0, h3916, hlam]
                                        · rcases p3897_3 (m.d 1 3) (by simp) with h3918 | h3918
                                          · linarith only [h1, h3918, hlam]
                                          · rcases p3897_3 (m.d 1 4) (by simp) with h3920 | h3920
                                            · linarith only [h3920, hlam, p3897_0]
                                            · rcases p3897_3 (m.d 1 5) (by simp) with h3922 | h3922
                                              · linarith only [h3, h3922, hlam]
                                              · linarith only [h3324, h3922, hlam]
                                      · linarith only [h3915, hlam, p3897_0]
                                    · have p3897_0 := h3897c.1
                                      have p3897_1 := h3897c.2.1
                                      have p3897_2 := h3897c.2.2.1
                                      have p3897_3 := h3897c.2.2.2
                                      rcases p3897_3 (m.d 0 1) (by simp) with h3926 | h3926
                                      · rcases p3897_3 (m.d 1 2) (by simp) with h3927 | h3927
                                        · linarith only [h0, h3927, hlam]
                                        · rcases p3897_3 (m.d 1 3) (by simp) with h3929 | h3929
                                          · linarith only [h1, h3929, hlam]
                                          · rcases p3897_3 (m.d 1 4) (by simp) with h3931 | h3931
                                            · linarith only [h2, h3931, hlam]
                                            · rcases p3897_3 (m.d 1 5) (by simp) with h3933 | h3933
                                              · linarith only [h3933, hlam, p3897_0]
                                              · rcases h3bigk with h3935c | h3935c | h3935c | h3935c | h3935c | h3935c | h3935c | h3935c | h3935c | h3935c | h3935c | h3935c | h3935c | h3935c | h3935c | h3935c | h3935c | h3935c | h3935c | h3935c | h3935c | h3935c | h3935c | h3935c | h3935c
                                                · have p3935_0 := h3935c.1
                                                  have p3935_1 := h3935c.2.1
                                                  have p3935_2 := h3935c.2.2.1
                                                  have p3935_3 := h3935c.2.2.2
                                                  linarith only [hlam, p3935_0]
                                                · have p3935_0 := h3935c.1
                                                  have p3935_1 := h3935c.2.1
                                                  have p3935_2 := h3935c.2.2.1
                                                  have p3935_3 := h3935c.2.2.2
                                                  linarith only [h2, h3313, h3314, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3727_1, p3935_1, u0elo0]
                                                · have p3935_0 := h3935c.1
                                                  have p3935_1 := h3935c.2.1
                                                  have p3935_2 := h3935c.2.2.1
                                                  have p3935_3 := h3935c.2.2.2
                                                  linarith only [h4, hlam, p3935_1]
                                                · have p3935_0 := h3935c.1
                                                  have p3935_1 := h3935c.2.1
                                                  have p3935_2 := h3935c.2.2.1
                                                  have p3935_3 := h3935c.2.2.2
                                                  linarith only [h1947, hlam, p3935_0]
                                                · have p3935_0 := h3935c.1
                                                  have p3935_1 := h3935c.2.1
                                                  have p3935_2 := h3935c.2.2.1
                                                  have p3935_3 := h3935c.2.2.2
                                                  linarith only [h3197, hlam, p3935_0]
                                                · have p3935_0 := h3935c.1
                                                  have p3935_1 := h3935c.2.1
                                                  have p3935_2 := h3935c.2.2.1
                                                  have p3935_3 := h3935c.2.2.2
                                                  linarith only [h1, hlam, p3935_0]
                                                · have p3935_0 := h3935c.1
                                                  have p3935_1 := h3935c.2.1
                                                  have p3935_2 := h3935c.2.2.1
                                                  have p3935_3 := h3935c.2.2.2
                                                  linarith only [hlam, p3935_0]
                                                · have p3935_0 := h3935c.1
                                                  have p3935_1 := h3935c.2.1
                                                  have p3935_2 := h3935c.2.2.1
                                                  have p3935_3 := h3935c.2.2.2
                                                  linarith only [h3314, hlam, p3935_1]
                                                · have p3935_0 := h3935c.1
                                                  have p3935_1 := h3935c.2.1
                                                  have p3935_2 := h3935c.2.2.1
                                                  have p3935_3 := h3935c.2.2.2
                                                  linarith only [h3320, hlam, p3935_0]
                                                · have p3935_0 := h3935c.1
                                                  have p3935_1 := h3935c.2.1
                                                  have p3935_2 := h3935c.2.2.1
                                                  have p3935_3 := h3935c.2.2.2
                                                  linarith only [h3322, hlam, p3935_0]
                                                · have p3935_0 := h3935c.1
                                                  have p3935_1 := h3935c.2.1
                                                  have p3935_2 := h3935c.2.2.1
                                                  have p3935_3 := h3935c.2.2.2
                                                  linarith only [h3721, h4, hc02, hc34, hlam, hphi, ht23, p3935_1]
                                                · have p3935_0 := h3935c.1
                                                  have p3935_1 := h3935c.2.1
                                                  have p3935_2 := h3935c.2.2.1
                                                  have p3935_3 := h3935c.2.2.2
                                                  linarith only [h3314, h3721, hc12, hc34, hlam, hphi, ht23, p3935_1]
                                                · have p3935_0 := h3935c.1
                                                  have p3935_1 := h3935c.2.1
                                                  have p3935_2 := h3935c.2.2.1
                                                  have p3935_3 := h3935c.2.2.2
                                                  linarith only [hlam, p3935_0]
                                                · have p3935_0 := h3935c.1
                                                  have p3935_1 := h3935c.2.1
                                                  have p3935_2 := h3935c.2.2.1
                                                  have p3935_3 := h3935c.2.2.2
                                                  linarith only [h3721, hlam, p3935_0]
                                                · have p3935_0 := h3935c.1
                                                  have p3935_1 := h3935c.2.1
                                                  have p3935_2 := h3935c.2.2.1
                                                  have p3935_3 := h3935c.2.2.2
                                                  linarith only [h3723, hlam, p3935_0]
                                                · have p3935_0 := h3935c.1
                                                  have p3935_1 := h3935c.2.1
                                                  have p3935_2 := h3935c.2.2.1
                                                  have p3935_3 := h3935c.2.2.2
                                                  rcases p3935_3 (m.d 0 3) (by simp) with h3951 | h3951
                                                  · linarith only [h3951, hlam, p3935_0]
                                                  · rcases p3935_3 (m.d 1 3) (by simp) with h3953 | h3953
                                                    · linarith only [h3320, h3953, hlam]
                                                    · rcases p3935_3 (m.d 2 3) (by simp) with h3955 | h3955
                                                      · linarith only [h3721, h3955, hlam]
                                                      · linarith only [h3955, h4, hlam]
                                                · have p3935_0 := h3935c.1
                                                  have p3935_1 := h3935c.2.1
                                                  have p3935_2 := h3935c.2.2.1
                                                  have p3935_3 := h3935c.2.2.2
                                                  rcases p3935_3 (m.d 0 3) (by simp) with h3958 | h3958
                                                  · linarith only [h1947, h3958, hlam]
                                                  · linarith only [h1, h3958, hlam]
                                                · have p3935_0 := h3935c.1
                                                  have p3935_1 := h3935c.2.1
                                                  have p3935_2 := h3935c.2.2.1
                                                  have p3935_3 := h3935c.2.2.2
                                                  linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p3935_1]
                                                · have p3935_0 := h3935c.1
                                                  have p3935_1 := h3935c.2.1
                                                  have p3935_2 := h3935c.2.2.1
                                                  have p3935_3 := h3935c.2.2.2
                                                  linarith only [hlam, p3935_0]
                                                · have p3935_0 := h3935c.1
                                                  have p3935_1 := h3935c.2.1
                                                  have p3935_2 := h3935c.2.2.1
                                                  have p3935_3 := h3935c.2.2.2
                                                  linarith only [h0, h3197, h4, hc12, hc34, hlam, hphi, ht23, p3935_1]
                                                · have p3935_0 := h3935c.1
                                                  have p3935_1 := h3935c.2.1
                                                  have p3935_2 := h3935c.2.2.1
                                                  have p3935_3 := h3935c.2.2.2
                                                  rcases p3935_3 (m.d 0 3) (by simp) with h3964 | h3964
                                                  · linarith only [h3964, hlam, p3935_0]
                                                  · rcases p3935_3 (m.d 1 3) (by simp) with h3966 | h3966
                                                    · linarith only [h3322, h3966, hlam]
                                                    · rcases p3935_3 (m.d 2 3) (by simp) with h3968 | h3968
                                                      · linarith only [h3723, h3968, hlam]
                                                      · linarith only [h3968, h4, hlam]
                                                · have p3935_0 := h3935c.1
                                                  have p3935_1 := h3935c.2.1
                                                  have p3935_2 := h3935c.2.2.1
                                                  have p3935_3 := h3935c.2.2.2
                                                  rcases p3935_3 (m.d 0 3) (by simp) with h3971 | h3971
                                                  · linarith only [h3197, h3971, hlam]
                                                  · linarith only [h1, h3971, hlam]
                                                · have p3935_0 := h3935c.1
                                                  have p3935_1 := h3935c.2.1
                                                  have p3935_2 := h3935c.2.2.1
                                                  have p3935_3 := h3935c.2.2.2
                                                  linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p3935_1]
                                                · have p3935_0 := h3935c.1
                                                  have p3935_1 := h3935c.2.1
                                                  have p3935_2 := h3935c.2.2.1
                                                  have p3935_3 := h3935c.2.2.2
                                                  linarith only [h3726, hlam, p3935_0]
                                                · have p3935_0 := h3935c.1
                                                  have p3935_1 := h3935c.2.1
                                                  have p3935_2 := h3935c.2.2.1
                                                  have p3935_3 := h3935c.2.2.2
                                                  linarith only [hlam, p3935_0]
                                      · linarith only [h3926, hlam, p3897_0]
                                    · have p3897_0 := h3897c.1
                                      have p3897_1 := h3897c.2.1
                                      have p3897_2 := h3897c.2.2.1
                                      have p3897_3 := h3897c.2.2.2
                                      linarith only [h0, hlam, p3897_0]
                                    · have p3897_0 := h3897c.1
                                      have p3897_1 := h3897c.2.1
                                      have p3897_2 := h3897c.2.2.1
                                      have p3897_3 := h3897c.2.2.2
                                      linarith only [hlam, p3897_0]
                                    · have p3897_0 := h3897c.1
                                      have p3897_1 := h3897c.2.1
                                      have p3897_2 := h3897c.2.2.1
                                      have p3897_3 := h3897c.2.2.2
                                      linarith only [h3314, hlam, p3897_0]
                                    · have p3897_0 := h3897c.1
                                      have p3897_1 := h3897c.2.1
                                      have p3897_2 := h3897c.2.2.1
                                      have p3897_3 := h3897c.2.2.2
                                      linarith only [h3316, hlam, p3897_0]
                                    · have p3897_0 := h3897c.1
                                      have p3897_1 := h3897c.2.1
                                      have p3897_2 := h3897c.2.2.1
                                      have p3897_3 := h3897c.2.2.2
                                      linarith only [h3318, hlam, p3897_0]
                                    · have p3897_0 := h3897c.1
                                      have p3897_1 := h3897c.2.1
                                      have p3897_2 := h3897c.2.2.1
                                      have p3897_3 := h3897c.2.2.2
                                      linarith only [h1, hlam, p3897_0]
                                    · have p3897_0 := h3897c.1
                                      have p3897_1 := h3897c.2.1
                                      have p3897_2 := h3897c.2.2.1
                                      have p3897_3 := h3897c.2.2.2
                                      linarith only [h1, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3897_1, u0elo0]
                                    · have p3897_0 := h3897c.1
                                      have p3897_1 := h3897c.2.1
                                      have p3897_2 := h3897c.2.2.1
                                      have p3897_3 := h3897c.2.2.2
                                      linarith only [hlam, p3897_0]
                                    · have p3897_0 := h3897c.1
                                      have p3897_1 := h3897c.2.1
                                      have p3897_2 := h3897c.2.2.1
                                      have p3897_3 := h3897c.2.2.2
                                      linarith only [h3320, hlam, p3897_1]
                                    · have p3897_0 := h3897c.1
                                      have p3897_1 := h3897c.2.1
                                      have p3897_2 := h3897c.2.2.1
                                      have p3897_3 := h3897c.2.2.2
                                      linarith only [h3322, hlam, p3897_1]
                                    · have p3897_0 := h3897c.1
                                      have p3897_1 := h3897c.2.1
                                      have p3897_2 := h3897c.2.2.1
                                      have p3897_3 := h3897c.2.2.2
                                      linarith only [h2, hlam, p3897_0]
                                    · have p3897_0 := h3897c.1
                                      have p3897_1 := h3897c.2.1
                                      have p3897_2 := h3897c.2.2.1
                                      have p3897_3 := h3897c.2.2.2
                                      linarith only [h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3897_1, u0elo0]
                                    · have p3897_0 := h3897c.1
                                      have p3897_1 := h3897c.2.1
                                      have p3897_2 := h3897c.2.2.1
                                      have p3897_3 := h3897c.2.2.2
                                      linarith only [h2, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3897_1, u0elo0]
                                    · have p3897_0 := h3897c.1
                                      have p3897_1 := h3897c.2.1
                                      have p3897_2 := h3897c.2.2.1
                                      have p3897_3 := h3897c.2.2.2
                                      linarith only [hlam, p3897_0]
                                    · have p3897_0 := h3897c.1
                                      have p3897_1 := h3897c.2.1
                                      have p3897_2 := h3897c.2.2.1
                                      have p3897_3 := h3897c.2.2.2
                                      linarith only [h3324, hlam, p3897_1]
                                    · have p3897_0 := h3897c.1
                                      have p3897_1 := h3897c.2.1
                                      have p3897_2 := h3897c.2.2.1
                                      have p3897_3 := h3897c.2.2.2
                                      linarith only [h3, hlam, p3897_0]
                                    · have p3897_0 := h3897c.1
                                      have p3897_1 := h3897c.2.1
                                      have p3897_2 := h3897c.2.2.1
                                      have p3897_3 := h3897c.2.2.2
                                      linarith only [h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3897_1, u0elo0]
                                    · have p3897_0 := h3897c.1
                                      have p3897_1 := h3897c.2.1
                                      have p3897_2 := h3897c.2.2.1
                                      have p3897_3 := h3897c.2.2.2
                                      linarith only [h3, h3314, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3897_1, u0elo0]
                                    · have p3897_0 := h3897c.1
                                      have p3897_1 := h3897c.2.1
                                      have p3897_2 := h3897c.2.2.1
                                      have p3897_3 := h3897c.2.2.2
                                      linarith only [h2, h3313, h3324, hc14, hlam, hphi, ht0b, ht45, ht5b, p3897_1, u0elo0]
                                    · have p3897_0 := h3897c.1
                                      have p3897_1 := h3897c.2.1
                                      have p3897_2 := h3897c.2.2.1
                                      have p3897_3 := h3897c.2.2.2
                                      linarith only [hlam, p3897_0]
                                  · rcases h1bigk with h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c
                                    · have p3998_0 := h3998c.1
                                      have p3998_1 := h3998c.2.1
                                      have p3998_2 := h3998c.2.2.1
                                      have p3998_3 := h3998c.2.2.2
                                      linarith only [hlam, p3998_0]
                                    · have p3998_0 := h3998c.1
                                      have p3998_1 := h3998c.2.1
                                      have p3998_2 := h3998c.2.2.1
                                      have p3998_3 := h3998c.2.2.2
                                      rcases p3998_3 (m.d 0 1) (by simp) with h4000 | h4000
                                      · rcases p3998_3 (m.d 1 2) (by simp) with h4001 | h4001
                                        · linarith only [h4001, hlam, p3998_0]
                                        · rcases p3998_3 (m.d 1 3) (by simp) with h4003 | h4003
                                          · linarith only [h1, h4003, hlam]
                                          · linarith only [h3314, h4003, hlam]
                                      · linarith only [h4000, hlam, p3998_0]
                                    · have p3998_0 := h3998c.1
                                      have p3998_1 := h3998c.2.1
                                      have p3998_2 := h3998c.2.2.1
                                      have p3998_3 := h3998c.2.2.2
                                      rcases p3998_3 (m.d 0 1) (by simp) with h4007 | h4007
                                      · rcases p3998_3 (m.d 1 2) (by simp) with h4008 | h4008
                                        · linarith only [h0, h4008, hlam]
                                        · rcases p3998_3 (m.d 1 3) (by simp) with h4010 | h4010
                                          · linarith only [h4010, hlam, p3998_0]
                                          · rcases p3998_3 (m.d 1 4) (by simp) with h4012 | h4012
                                            · linarith only [h2, h4012, hlam]
                                            · linarith only [h3320, h4012, hlam]
                                      · linarith only [h4007, hlam, p3998_0]
                                    · have p3998_0 := h3998c.1
                                      have p3998_1 := h3998c.2.1
                                      have p3998_2 := h3998c.2.2.1
                                      have p3998_3 := h3998c.2.2.2
                                      rcases p3998_3 (m.d 0 1) (by simp) with h4016 | h4016
                                      · rcases p3998_3 (m.d 1 2) (by simp) with h4017 | h4017
                                        · linarith only [h0, h4017, hlam]
                                        · rcases p3998_3 (m.d 1 3) (by simp) with h4019 | h4019
                                          · linarith only [h1, h4019, hlam]
                                          · rcases p3998_3 (m.d 1 4) (by simp) with h4021 | h4021
                                            · linarith only [h4021, hlam, p3998_0]
                                            · rcases p3998_3 (m.d 1 5) (by simp) with h4023 | h4023
                                              · linarith only [h3, h4023, hlam]
                                              · linarith only [h3324, h4023, hlam]
                                      · linarith only [h4016, hlam, p3998_0]
                                    · have p3998_0 := h3998c.1
                                      have p3998_1 := h3998c.2.1
                                      have p3998_2 := h3998c.2.2.1
                                      have p3998_3 := h3998c.2.2.2
                                      rcases p3998_3 (m.d 0 1) (by simp) with h4027 | h4027
                                      · rcases p3998_3 (m.d 1 2) (by simp) with h4028 | h4028
                                        · linarith only [h0, h4028, hlam]
                                        · rcases p3998_3 (m.d 1 3) (by simp) with h4030 | h4030
                                          · linarith only [h1, h4030, hlam]
                                          · rcases p3998_3 (m.d 1 4) (by simp) with h4032 | h4032
                                            · linarith only [h2, h4032, hlam]
                                            · rcases p3998_3 (m.d 1 5) (by simp) with h4034 | h4034
                                              · linarith only [h4034, hlam, p3998_0]
                                              · rcases h3bigk with h4036c | h4036c | h4036c | h4036c | h4036c | h4036c | h4036c | h4036c | h4036c | h4036c | h4036c | h4036c | h4036c | h4036c | h4036c | h4036c | h4036c | h4036c | h4036c | h4036c | h4036c | h4036c | h4036c | h4036c | h4036c
                                                · have p4036_0 := h4036c.1
                                                  have p4036_1 := h4036c.2.1
                                                  have p4036_2 := h4036c.2.2.1
                                                  have p4036_3 := h4036c.2.2.2
                                                  linarith only [hlam, p4036_0]
                                                · have p4036_0 := h4036c.1
                                                  have p4036_1 := h4036c.2.1
                                                  have p4036_2 := h4036c.2.2.1
                                                  have p4036_3 := h4036c.2.2.2
                                                  linarith only [h2, h3313, h3314, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3727_1, p4036_1, u0elo0]
                                                · have p4036_0 := h4036c.1
                                                  have p4036_1 := h4036c.2.1
                                                  have p4036_2 := h4036c.2.2.1
                                                  have p4036_3 := h4036c.2.2.2
                                                  linarith only [h4, hlam, p4036_1]
                                                · have p4036_0 := h4036c.1
                                                  have p4036_1 := h4036c.2.1
                                                  have p4036_2 := h4036c.2.2.1
                                                  have p4036_3 := h4036c.2.2.2
                                                  linarith only [h1947, hlam, p4036_0]
                                                · have p4036_0 := h4036c.1
                                                  have p4036_1 := h4036c.2.1
                                                  have p4036_2 := h4036c.2.2.1
                                                  have p4036_3 := h4036c.2.2.2
                                                  linarith only [h3197, hlam, p4036_0]
                                                · have p4036_0 := h4036c.1
                                                  have p4036_1 := h4036c.2.1
                                                  have p4036_2 := h4036c.2.2.1
                                                  have p4036_3 := h4036c.2.2.2
                                                  linarith only [h1, hlam, p4036_0]
                                                · have p4036_0 := h4036c.1
                                                  have p4036_1 := h4036c.2.1
                                                  have p4036_2 := h4036c.2.2.1
                                                  have p4036_3 := h4036c.2.2.2
                                                  linarith only [hlam, p4036_0]
                                                · have p4036_0 := h4036c.1
                                                  have p4036_1 := h4036c.2.1
                                                  have p4036_2 := h4036c.2.2.1
                                                  have p4036_3 := h4036c.2.2.2
                                                  linarith only [h3314, hlam, p4036_1]
                                                · have p4036_0 := h4036c.1
                                                  have p4036_1 := h4036c.2.1
                                                  have p4036_2 := h4036c.2.2.1
                                                  have p4036_3 := h4036c.2.2.2
                                                  linarith only [h3320, hlam, p4036_0]
                                                · have p4036_0 := h4036c.1
                                                  have p4036_1 := h4036c.2.1
                                                  have p4036_2 := h4036c.2.2.1
                                                  have p4036_3 := h4036c.2.2.2
                                                  linarith only [h3322, hlam, p4036_0]
                                                · have p4036_0 := h4036c.1
                                                  have p4036_1 := h4036c.2.1
                                                  have p4036_2 := h4036c.2.2.1
                                                  have p4036_3 := h4036c.2.2.2
                                                  linarith only [h1, h3314, h3721, hc12, hc34, hlam, hphi, ht23, p4036_1]
                                                · have p4036_0 := h4036c.1
                                                  have p4036_1 := h4036c.2.1
                                                  have p4036_2 := h4036c.2.2.1
                                                  have p4036_3 := h4036c.2.2.2
                                                  linarith only [h3314, h3721, hc12, hc34, hlam, hphi, ht23, p4036_1]
                                                · have p4036_0 := h4036c.1
                                                  have p4036_1 := h4036c.2.1
                                                  have p4036_2 := h4036c.2.2.1
                                                  have p4036_3 := h4036c.2.2.2
                                                  linarith only [hlam, p4036_0]
                                                · have p4036_0 := h4036c.1
                                                  have p4036_1 := h4036c.2.1
                                                  have p4036_2 := h4036c.2.2.1
                                                  have p4036_3 := h4036c.2.2.2
                                                  linarith only [h3721, hlam, p4036_0]
                                                · have p4036_0 := h4036c.1
                                                  have p4036_1 := h4036c.2.1
                                                  have p4036_2 := h4036c.2.2.1
                                                  have p4036_3 := h4036c.2.2.2
                                                  linarith only [h3723, hlam, p4036_0]
                                                · have p4036_0 := h4036c.1
                                                  have p4036_1 := h4036c.2.1
                                                  have p4036_2 := h4036c.2.2.1
                                                  have p4036_3 := h4036c.2.2.2
                                                  rcases p4036_3 (m.d 0 3) (by simp) with h4052 | h4052
                                                  · linarith only [h4052, hlam, p4036_0]
                                                  · rcases p4036_3 (m.d 1 3) (by simp) with h4054 | h4054
                                                    · linarith only [h3320, h4054, hlam]
                                                    · rcases p4036_3 (m.d 2 3) (by simp) with h4056 | h4056
                                                      · linarith only [h3721, h4056, hlam]
                                                      · linarith only [h4, h4056, hlam]
                                                · have p4036_0 := h4036c.1
                                                  have p4036_1 := h4036c.2.1
                                                  have p4036_2 := h4036c.2.2.1
                                                  have p4036_3 := h4036c.2.2.2
                                                  rcases p4036_3 (m.d 0 3) (by simp) with h4059 | h4059
                                                  · linarith only [h1947, h4059, hlam]
                                                  · linarith only [h1, h4059, hlam]
                                                · have p4036_0 := h4036c.1
                                                  have p4036_1 := h4036c.2.1
                                                  have p4036_2 := h4036c.2.2.1
                                                  have p4036_3 := h4036c.2.2.2
                                                  linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p4036_1]
                                                · have p4036_0 := h4036c.1
                                                  have p4036_1 := h4036c.2.1
                                                  have p4036_2 := h4036c.2.2.1
                                                  have p4036_3 := h4036c.2.2.2
                                                  linarith only [hlam, p4036_0]
                                                · have p4036_0 := h4036c.1
                                                  have p4036_1 := h4036c.2.1
                                                  have p4036_2 := h4036c.2.2.1
                                                  have p4036_3 := h4036c.2.2.2
                                                  linarith only [h1, h3197, h3314, hc12, hc34, hlam, hphi, ht23, p4036_1]
                                                · have p4036_0 := h4036c.1
                                                  have p4036_1 := h4036c.2.1
                                                  have p4036_2 := h4036c.2.2.1
                                                  have p4036_3 := h4036c.2.2.2
                                                  rcases p4036_3 (m.d 0 3) (by simp) with h4065 | h4065
                                                  · linarith only [h4065, hlam, p4036_0]
                                                  · rcases p4036_3 (m.d 1 3) (by simp) with h4067 | h4067
                                                    · linarith only [h3322, h4067, hlam]
                                                    · rcases p4036_3 (m.d 2 3) (by simp) with h4069 | h4069
                                                      · linarith only [h3723, h4069, hlam]
                                                      · linarith only [h4, h4069, hlam]
                                                · have p4036_0 := h4036c.1
                                                  have p4036_1 := h4036c.2.1
                                                  have p4036_2 := h4036c.2.2.1
                                                  have p4036_3 := h4036c.2.2.2
                                                  rcases p4036_3 (m.d 0 3) (by simp) with h4072 | h4072
                                                  · linarith only [h3197, h4072, hlam]
                                                  · linarith only [h1, h4072, hlam]
                                                · have p4036_0 := h4036c.1
                                                  have p4036_1 := h4036c.2.1
                                                  have p4036_2 := h4036c.2.2.1
                                                  have p4036_3 := h4036c.2.2.2
                                                  linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p4036_1]
                                                · have p4036_0 := h4036c.1
                                                  have p4036_1 := h4036c.2.1
                                                  have p4036_2 := h4036c.2.2.1
                                                  have p4036_3 := h4036c.2.2.2
                                                  linarith only [h3726, hlam, p4036_0]
                                                · have p4036_0 := h4036c.1
                                                  have p4036_1 := h4036c.2.1
                                                  have p4036_2 := h4036c.2.2.1
                                                  have p4036_3 := h4036c.2.2.2
                                                  linarith only [hlam, p4036_0]
                                      · linarith only [h4027, hlam, p3998_0]
                                    · have p3998_0 := h3998c.1
                                      have p3998_1 := h3998c.2.1
                                      have p3998_2 := h3998c.2.2.1
                                      have p3998_3 := h3998c.2.2.2
                                      linarith only [h0, hlam, p3998_0]
                                    · have p3998_0 := h3998c.1
                                      have p3998_1 := h3998c.2.1
                                      have p3998_2 := h3998c.2.2.1
                                      have p3998_3 := h3998c.2.2.2
                                      linarith only [hlam, p3998_0]
                                    · have p3998_0 := h3998c.1
                                      have p3998_1 := h3998c.2.1
                                      have p3998_2 := h3998c.2.2.1
                                      have p3998_3 := h3998c.2.2.2
                                      linarith only [h3314, hlam, p3998_0]
                                    · have p3998_0 := h3998c.1
                                      have p3998_1 := h3998c.2.1
                                      have p3998_2 := h3998c.2.2.1
                                      have p3998_3 := h3998c.2.2.2
                                      linarith only [h3316, hlam, p3998_0]
                                    · have p3998_0 := h3998c.1
                                      have p3998_1 := h3998c.2.1
                                      have p3998_2 := h3998c.2.2.1
                                      have p3998_3 := h3998c.2.2.2
                                      linarith only [h3318, hlam, p3998_0]
                                    · have p3998_0 := h3998c.1
                                      have p3998_1 := h3998c.2.1
                                      have p3998_2 := h3998c.2.2.1
                                      have p3998_3 := h3998c.2.2.2
                                      linarith only [h1, hlam, p3998_0]
                                    · have p3998_0 := h3998c.1
                                      have p3998_1 := h3998c.2.1
                                      have p3998_2 := h3998c.2.2.1
                                      have p3998_3 := h3998c.2.2.2
                                      linarith only [h1, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3998_1, u0elo0]
                                    · have p3998_0 := h3998c.1
                                      have p3998_1 := h3998c.2.1
                                      have p3998_2 := h3998c.2.2.1
                                      have p3998_3 := h3998c.2.2.2
                                      linarith only [hlam, p3998_0]
                                    · have p3998_0 := h3998c.1
                                      have p3998_1 := h3998c.2.1
                                      have p3998_2 := h3998c.2.2.1
                                      have p3998_3 := h3998c.2.2.2
                                      linarith only [h3320, hlam, p3998_1]
                                    · have p3998_0 := h3998c.1
                                      have p3998_1 := h3998c.2.1
                                      have p3998_2 := h3998c.2.2.1
                                      have p3998_3 := h3998c.2.2.2
                                      linarith only [h3322, hlam, p3998_1]
                                    · have p3998_0 := h3998c.1
                                      have p3998_1 := h3998c.2.1
                                      have p3998_2 := h3998c.2.2.1
                                      have p3998_3 := h3998c.2.2.2
                                      linarith only [h2, hlam, p3998_0]
                                    · have p3998_0 := h3998c.1
                                      have p3998_1 := h3998c.2.1
                                      have p3998_2 := h3998c.2.2.1
                                      have p3998_3 := h3998c.2.2.2
                                      linarith only [h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3998_1, u0elo0]
                                    · have p3998_0 := h3998c.1
                                      have p3998_1 := h3998c.2.1
                                      have p3998_2 := h3998c.2.2.1
                                      have p3998_3 := h3998c.2.2.2
                                      linarith only [h2, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3998_1, u0elo0]
                                    · have p3998_0 := h3998c.1
                                      have p3998_1 := h3998c.2.1
                                      have p3998_2 := h3998c.2.2.1
                                      have p3998_3 := h3998c.2.2.2
                                      linarith only [hlam, p3998_0]
                                    · have p3998_0 := h3998c.1
                                      have p3998_1 := h3998c.2.1
                                      have p3998_2 := h3998c.2.2.1
                                      have p3998_3 := h3998c.2.2.2
                                      linarith only [h3324, hlam, p3998_1]
                                    · have p3998_0 := h3998c.1
                                      have p3998_1 := h3998c.2.1
                                      have p3998_2 := h3998c.2.2.1
                                      have p3998_3 := h3998c.2.2.2
                                      linarith only [h3, hlam, p3998_0]
                                    · have p3998_0 := h3998c.1
                                      have p3998_1 := h3998c.2.1
                                      have p3998_2 := h3998c.2.2.1
                                      have p3998_3 := h3998c.2.2.2
                                      linarith only [h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3998_1, u0elo0]
                                    · have p3998_0 := h3998c.1
                                      have p3998_1 := h3998c.2.1
                                      have p3998_2 := h3998c.2.2.1
                                      have p3998_3 := h3998c.2.2.2
                                      linarith only [h3, h3314, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3998_1, u0elo0]
                                    · have p3998_0 := h3998c.1
                                      have p3998_1 := h3998c.2.1
                                      have p3998_2 := h3998c.2.2.1
                                      have p3998_3 := h3998c.2.2.2
                                      linarith only [h2, h3313, h3324, hc14, hlam, hphi, ht0b, ht45, ht5b, p3998_1, u0elo0]
                                    · have p3998_0 := h3998c.1
                                      have p3998_1 := h3998c.2.1
                                      have p3998_2 := h3998c.2.2.1
                                      have p3998_3 := h3998c.2.2.2
                                      linarith only [hlam, p3998_0]
                                · linarith only [h3197, h3792, hlam]
                              · linarith only [h1947, h3791, hlam]
                        · linarith only [h1, h3786, hlam]
                      · have p3727_0 := h3727c.1
                        have p3727_1 := h3727c.2.1
                        have p3727_2 := h3727c.2.2.1
                        have p3727_3 := h3727c.2.2.2
                        linarith only [h3313, hlam, p3727_1]
                      · have p3727_0 := h3727c.1
                        have p3727_1 := h3727c.2.1
                        have p3727_2 := h3727c.2.2.1
                        have p3727_3 := h3727c.2.2.2
                        linarith only [hlam, p3727_0]
                    · linarith only [h1947, h2, h3313, h3726, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h1304, h3313, h3725, hlam]

end R2N4
