import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6334000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_s0_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1951 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2940 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3280 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h2emin := hb2.2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h3281 | h3281
  · rcases m.htr 0 2 4 (by decide) (by decide) with h3282 | h3282
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3283 | h3283
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3284 | h3284
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3285 | h3285
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3286 | h3286
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3287 | h3287
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3288 | h3288
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3289 | h3289
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3290 | h3290
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3291 | h3291
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3292 | h3292
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3293 | h3293
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3294 | h3294
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3295 | h3295
                              · linarith only [h3281, h3292, h3295, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                              · linarith only [h3281, h3292, h3294, h3295, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3298 | h3298
                              · linarith only [h3281, h3284, h3294, h3298, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · rcases h0bigk with h3300c | h3300c | h3300c | h3300c | h3300c | h3300c | h3300c | h3300c | h3300c | h3300c | h3300c | h3300c | h3300c | h3300c | h3300c | h3300c | h3300c | h3300c | h3300c | h3300c | h3300c | h3300c | h3300c | h3300c | h3300c
                                · have p3300_0 := h3300c.1
                                  have p3300_1 := h3300c.2.1
                                  have p3300_2 := h3300c.2.2.1
                                  have p3300_3 := h3300c.2.2.2
                                  linarith only [hlam, p3300_0]
                                · have p3300_0 := h3300c.1
                                  have p3300_1 := h3300c.2.1
                                  have p3300_2 := h3300c.2.2.1
                                  have p3300_3 := h3300c.2.2.2
                                  linarith only [h0, hlam, p3300_1]
                                · have p3300_0 := h3300c.1
                                  have p3300_1 := h3300c.2.1
                                  have p3300_2 := h3300c.2.2.1
                                  have p3300_3 := h3300c.2.2.2
                                  linarith only [h1951, hlam, p3300_0]
                                · have p3300_0 := h3300c.1
                                  have p3300_1 := h3300c.2.1
                                  have p3300_2 := h3300c.2.2.1
                                  have p3300_3 := h3300c.2.2.2
                                  linarith only [h2940, hlam, p3300_1]
                                · have p3300_0 := h3300c.1
                                  have p3300_1 := h3300c.2.1
                                  have p3300_2 := h3300c.2.2.1
                                  have p3300_3 := h3300c.2.2.2
                                  linarith only [h2940, h3281, h3284, h3286, h3292, h3294, hc34, hlam, hphi, ht0b, ht45, ht5b, p3300_1, u0elo1]
                                · have p3300_0 := h3300c.1
                                  have p3300_1 := h3300c.2.1
                                  have p3300_2 := h3300c.2.2.1
                                  have p3300_3 := h3300c.2.2.2
                                  linarith only [h3280, h3289, h3293, hc35, hlam, hphi, ht0b, ht5b, p3300_1, u0elo1]
                                · have p3300_0 := h3300c.1
                                  have p3300_1 := h3300c.2.1
                                  have p3300_2 := h3300c.2.2.1
                                  have p3300_3 := h3300c.2.2.2
                                  linarith only [hlam, p3300_0]
                                · have p3300_0 := h3300c.1
                                  have p3300_1 := h3300c.2.1
                                  have p3300_2 := h3300c.2.2.1
                                  have p3300_3 := h3300c.2.2.2
                                  linarith only [h2940, h3280, h3284, h3289, h3293, hc35, hlam, hphi, ht0b, ht5b, p3300_1, u0elo1]
                                · have p3300_0 := h3300c.1
                                  have p3300_1 := h3300c.2.1
                                  have p3300_2 := h3300c.2.2.1
                                  have p3300_3 := h3300c.2.2.2
                                  linarith only [h2940, h3280, h3289, h3293, hc35, hlam, hphi, ht0b, ht5b, p3300_1, u0elo1]
                                · have p3300_0 := h3300c.1
                                  have p3300_1 := h3300c.2.1
                                  have p3300_2 := h3300c.2.2.1
                                  have p3300_3 := h3300c.2.2.2
                                  linarith only [h3286, h3292, h3294, hc34, hlam, hphi, ht0b, ht45, ht5b, p3300_1, u0elo1]
                                · have p3300_0 := h3300c.1
                                  have p3300_1 := h3300c.2.1
                                  have p3300_2 := h3300c.2.2.1
                                  have p3300_3 := h3300c.2.2.2
                                  linarith only [h3280, h3286, h3292, h3294, hc34, hlam, hphi, ht0b, ht45, ht5b, p3300_1, u0elo2]
                                · have p3300_0 := h3300c.1
                                  have p3300_1 := h3300c.2.1
                                  have p3300_2 := h3300c.2.2.1
                                  have p3300_3 := h3300c.2.2.2
                                  linarith only [h3281, hlam, p3300_1]
                                · have p3300_0 := h3300c.1
                                  have p3300_1 := h3300c.2.1
                                  have p3300_2 := h3300c.2.2.1
                                  have p3300_3 := h3300c.2.2.2
                                  linarith only [hlam, p3300_0]
                                · have p3300_0 := h3300c.1
                                  have p3300_1 := h3300c.2.1
                                  have p3300_2 := h3300c.2.2.1
                                  have p3300_3 := h3300c.2.2.2
                                  linarith only [h3281, h3286, h3292, h3294, hc34, hlam, hphi, ht0b, ht45, ht5b, p3300_1, u0elo1]
                                · have p3300_0 := h3300c.1
                                  have p3300_1 := h3300c.2.1
                                  have p3300_2 := h3300c.2.2.1
                                  have p3300_3 := h3300c.2.2.2
                                  linarith only [h3281, h3286, h3292, h3294, hc34, hlam, hphi, ht0b, ht45, ht5b, p3300_1, u0elo1]
                                · have p3300_0 := h3300c.1
                                  have p3300_1 := h3300c.2.1
                                  have p3300_2 := h3300c.2.2.1
                                  have p3300_3 := h3300c.2.2.2
                                  linarith only [h3280, h3286, h3292, h3294, hc34, hlam, hphi, ht0b, ht45, ht5b, p3300_1, u0elo3]
                                · have p3300_0 := h3300c.1
                                  have p3300_1 := h3300c.2.1
                                  have p3300_2 := h3300c.2.2.1
                                  have p3300_3 := h3300c.2.2.2
                                  linarith only [h3282, hlam, p3300_0]
                                · have p3300_0 := h3300c.1
                                  have p3300_1 := h3300c.2.1
                                  have p3300_2 := h3300c.2.2.1
                                  have p3300_3 := h3300c.2.2.2
                                  linarith only [h3284, hlam, p3300_0]
                                · have p3300_0 := h3300c.1
                                  have p3300_1 := h3300c.2.1
                                  have p3300_2 := h3300c.2.2.1
                                  have p3300_3 := h3300c.2.2.2
                                  linarith only [hlam, p3300_0]
                                · have p3300_0 := h3300c.1
                                  have p3300_1 := h3300c.2.1
                                  have p3300_2 := h3300c.2.2.1
                                  have p3300_3 := h3300c.2.2.2
                                  linarith only [h3281, h3284, h3286, h3292, h3294, hc34, hlam, hphi, ht0b, ht45, ht5b, p3300_1, u0elo1]
                                · have p3300_0 := h3300c.1
                                  have p3300_1 := h3300c.2.1
                                  have p3300_2 := h3300c.2.2.1
                                  have p3300_3 := h3300c.2.2.2
                                  linarith only [h3280, hlam, p3300_0]
                                · have p3300_0 := h3300c.1
                                  have p3300_1 := h3300c.2.1
                                  have p3300_2 := h3300c.2.2.1
                                  have p3300_3 := h3300c.2.2.2
                                  linarith only [h3283, hlam, p3300_1]
                                · have p3300_0 := h3300c.1
                                  have p3300_1 := h3300c.2.1
                                  have p3300_2 := h3300c.2.2.1
                                  have p3300_3 := h3300c.2.2.2
                                  linarith only [h3285, hlam, p3300_0]
                                · have p3300_0 := h3300c.1
                                  have p3300_1 := h3300c.2.1
                                  have p3300_2 := h3300c.2.2.1
                                  have p3300_3 := h3300c.2.2.2
                                  linarith only [h3286, hlam, p3300_1]
                                · have p3300_0 := h3300c.1
                                  have p3300_1 := h3300c.2.1
                                  have p3300_2 := h3300c.2.2.1
                                  have p3300_3 := h3300c.2.2.2
                                  linarith only [hlam, p3300_0]
                          · linarith only [h3292, h3293, hc34, hlam, hphi, ht45, u5elo3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3327 | h3327
                          · linarith only [h3281, h3284, h3292, h3327, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3329 | h3329
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3330 | h3330
                              · rcases h0bigk with h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c
                                · have p3331_0 := h3331c.1
                                  have p3331_1 := h3331c.2.1
                                  have p3331_2 := h3331c.2.2.1
                                  have p3331_3 := h3331c.2.2.2
                                  linarith only [hlam, p3331_0]
                                · have p3331_0 := h3331c.1
                                  have p3331_1 := h3331c.2.1
                                  have p3331_2 := h3331c.2.2.1
                                  have p3331_3 := h3331c.2.2.2
                                  linarith only [h0, hlam, p3331_1]
                                · have p3331_0 := h3331c.1
                                  have p3331_1 := h3331c.2.1
                                  have p3331_2 := h3331c.2.2.1
                                  have p3331_3 := h3331c.2.2.2
                                  linarith only [h1951, hlam, p3331_0]
                                · have p3331_0 := h3331c.1
                                  have p3331_1 := h3331c.2.1
                                  have p3331_2 := h3331c.2.2.1
                                  have p3331_3 := h3331c.2.2.2
                                  linarith only [h2940, hlam, p3331_1]
                                · have p3331_0 := h3331c.1
                                  have p3331_1 := h3331c.2.1
                                  have p3331_2 := h3331c.2.2.1
                                  have p3331_3 := h3331c.2.2.2
                                  linarith only [h2940, h3280, h3287, h3290, h3291, h3327, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3331_1]
                                · have p3331_0 := h3331c.1
                                  have p3331_1 := h3331c.2.1
                                  have p3331_2 := h3331c.2.2.1
                                  have p3331_3 := h3331c.2.2.2
                                  linarith only [h3280, h3291, h3327, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3331_1, u0elo1]
                                · have p3331_0 := h3331c.1
                                  have p3331_1 := h3331c.2.1
                                  have p3331_2 := h3331c.2.2.1
                                  have p3331_3 := h3331c.2.2.2
                                  linarith only [hlam, p3331_0]
                                · have p3331_0 := h3331c.1
                                  have p3331_1 := h3331c.2.1
                                  have p3331_2 := h3331c.2.2.1
                                  have p3331_3 := h3331c.2.2.2
                                  linarith only [h3284, hc34, hlam, hphi, ht0b, ht45, ht5b, p3331_1, u0elo1]
                                · have p3331_0 := h3331c.1
                                  have p3331_1 := h3331c.2.1
                                  have p3331_2 := h3331c.2.2.1
                                  have p3331_3 := h3331c.2.2.2
                                  linarith only [h2940, h3280, h3291, h3327, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3331_1, u0elo1]
                                · have p3331_0 := h3331c.1
                                  have p3331_1 := h3331c.2.1
                                  have p3331_2 := h3331c.2.2.1
                                  have p3331_3 := h3331c.2.2.2
                                  linarith only [h3280, h3291, h3327, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3331_1, u0elo1]
                                · have p3331_0 := h3331c.1
                                  have p3331_1 := h3331c.2.1
                                  have p3331_2 := h3331c.2.2.1
                                  have p3331_3 := h3331c.2.2.2
                                  linarith only [h3280, h3291, h3327, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3331_1, u0elo2]
                                · have p3331_0 := h3331c.1
                                  have p3331_1 := h3331c.2.1
                                  have p3331_2 := h3331c.2.2.1
                                  have p3331_3 := h3331c.2.2.2
                                  linarith only [h3281, hlam, p3331_1]
                                · have p3331_0 := h3331c.1
                                  have p3331_1 := h3331c.2.1
                                  have p3331_2 := h3331c.2.2.1
                                  have p3331_3 := h3331c.2.2.2
                                  linarith only [hlam, p3331_0]
                                · have p3331_0 := h3331c.1
                                  have p3331_1 := h3331c.2.1
                                  have p3331_2 := h3331c.2.2.1
                                  have p3331_3 := h3331c.2.2.2
                                  linarith only [h2940, h3280, h3281, h3291, h3327, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3331_1, u0elo1]
                                · have p3331_0 := h3331c.1
                                  have p3331_1 := h3331c.2.1
                                  have p3331_2 := h3331c.2.2.1
                                  have p3331_3 := h3331c.2.2.2
                                  linarith only [h3280, h3281, h3291, h3327, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3331_1, u0elo1]
                                · have p3331_0 := h3331c.1
                                  have p3331_1 := h3331c.2.1
                                  have p3331_2 := h3331c.2.2.1
                                  have p3331_3 := h3331c.2.2.2
                                  linarith only [h3280, h3291, h3327, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3331_1, u0elo3]
                                · have p3331_0 := h3331c.1
                                  have p3331_1 := h3331c.2.1
                                  have p3331_2 := h3331c.2.2.1
                                  have p3331_3 := h3331c.2.2.2
                                  linarith only [h3282, hlam, p3331_0]
                                · have p3331_0 := h3331c.1
                                  have p3331_1 := h3331c.2.1
                                  have p3331_2 := h3331c.2.2.1
                                  have p3331_3 := h3331c.2.2.2
                                  linarith only [h3284, hlam, p3331_0]
                                · have p3331_0 := h3331c.1
                                  have p3331_1 := h3331c.2.1
                                  have p3331_2 := h3331c.2.2.1
                                  have p3331_3 := h3331c.2.2.2
                                  linarith only [hlam, p3331_0]
                                · have p3331_0 := h3331c.1
                                  have p3331_1 := h3331c.2.1
                                  have p3331_2 := h3331c.2.2.1
                                  have p3331_3 := h3331c.2.2.2
                                  linarith only [h3280, h3281, h3284, h3291, h3327, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3331_1, u0elo1]
                                · have p3331_0 := h3331c.1
                                  have p3331_1 := h3331c.2.1
                                  have p3331_2 := h3331c.2.2.1
                                  have p3331_3 := h3331c.2.2.2
                                  linarith only [h3280, hlam, p3331_0]
                                · have p3331_0 := h3331c.1
                                  have p3331_1 := h3331c.2.1
                                  have p3331_2 := h3331c.2.2.1
                                  have p3331_3 := h3331c.2.2.2
                                  linarith only [h3283, hlam, p3331_1]
                                · have p3331_0 := h3331c.1
                                  have p3331_1 := h3331c.2.1
                                  have p3331_2 := h3331c.2.2.1
                                  have p3331_3 := h3331c.2.2.2
                                  linarith only [h3285, hlam, p3331_0]
                                · have p3331_0 := h3331c.1
                                  have p3331_1 := h3331c.2.1
                                  have p3331_2 := h3331c.2.2.1
                                  have p3331_3 := h3331c.2.2.2
                                  linarith only [h3286, hlam, p3331_1]
                                · have p3331_0 := h3331c.1
                                  have p3331_1 := h3331c.2.1
                                  have p3331_2 := h3331c.2.2.1
                                  have p3331_3 := h3331c.2.2.2
                                  linarith only [hlam, p3331_0]
                              · linarith only [h3281, h3284, h3286, h3292, h3330, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3358 | h3358
                              · linarith only [h3281, h3284, h3329, h3358, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · linarith only [h3281, h3284, h3286, h3292, h3358, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h1951, h3291, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                    · linarith only [h1951, h3284, h3290, hlam]
                  · linarith only [h0, h3289, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                · linarith only [h0, h3282, h3288, hlam]
              · linarith only [h0, h3281, h3287, hlam]
            · linarith only [h2940, h3280, h3286, hc15, hlam, hphi, u5elo4]
          · linarith only [h2940, h3280, h3284, h3285, hc15, hlam, hphi, u5elo3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3368 | h3368
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3369 | h3369
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3370 | h3370
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3371 | h3371
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3372 | h3372
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3373 | h3373
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3374 | h3374
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3375 | h3375
                        · linarith only [h3281, h3284, h3375, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3377 | h3377
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3378 | h3378
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3379 | h3379
                              · rcases h0bigk with h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c
                                · have p3380_0 := h3380c.1
                                  have p3380_1 := h3380c.2.1
                                  have p3380_2 := h3380c.2.2.1
                                  have p3380_3 := h3380c.2.2.2
                                  linarith only [hlam, p3380_0]
                                · have p3380_0 := h3380c.1
                                  have p3380_1 := h3380c.2.1
                                  have p3380_2 := h3380c.2.2.1
                                  have p3380_3 := h3380c.2.2.2
                                  linarith only [h0, hlam, p3380_1]
                                · have p3380_0 := h3380c.1
                                  have p3380_1 := h3380c.2.1
                                  have p3380_2 := h3380c.2.2.1
                                  have p3380_3 := h3380c.2.2.2
                                  linarith only [h1951, hlam, p3380_0]
                                · have p3380_0 := h3380c.1
                                  have p3380_1 := h3380c.2.1
                                  have p3380_2 := h3380c.2.2.1
                                  have p3380_3 := h3380c.2.2.2
                                  linarith only [h2940, hlam, p3380_1]
                                · have p3380_0 := h3380c.1
                                  have p3380_1 := h3380c.2.1
                                  have p3380_2 := h3380c.2.2.1
                                  have p3380_3 := h3380c.2.2.2
                                  linarith only [h1951, h3284, h3370, h3373, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p3380_1]
                                · have p3380_0 := h3380c.1
                                  have p3380_1 := h3380c.2.1
                                  have p3380_2 := h3380c.2.2.1
                                  have p3380_3 := h3380c.2.2.2
                                  linarith only [h3280, hc15, hlam, hphi, ht0b, ht5b, p3380_1, u0elo1]
                                · have p3380_0 := h3380c.1
                                  have p3380_1 := h3380c.2.1
                                  have p3380_2 := h3380c.2.2.1
                                  have p3380_3 := h3380c.2.2.2
                                  linarith only [hlam, p3380_0]
                                · have p3380_0 := h3380c.1
                                  have p3380_1 := h3380c.2.1
                                  have p3380_2 := h3380c.2.2.1
                                  have p3380_3 := h3380c.2.2.2
                                  linarith only [h1951, h3280, h3372, h3377, h3379, hc45, hlam, hphi, ht0b, ht5b, p3380_1, u0elo1]
                                · have p3380_0 := h3380c.1
                                  have p3380_1 := h3380c.2.1
                                  have p3380_2 := h3380c.2.2.1
                                  have p3380_3 := h3380c.2.2.2
                                  linarith only [h1951, h3280, h3284, h3372, h3377, h3379, hc45, hlam, hphi, ht0b, ht5b, p3380_1, u0elo1]
                                · have p3380_0 := h3380c.1
                                  have p3380_1 := h3380c.2.1
                                  have p3380_2 := h3380c.2.2.1
                                  have p3380_3 := h3380c.2.2.2
                                  rcases p3380_3 (m.d 0 1) (by simp) with h3390 | h3390
                                  · linarith only [h0, h3390, hlam]
                                  · linarith only [h3280, h3390, hlam]
                                · have p3380_0 := h3380c.1
                                  have p3380_1 := h3380c.2.1
                                  have p3380_2 := h3380c.2.2.1
                                  have p3380_3 := h3380c.2.2.2
                                  linarith only [h3280, h3284, h3370, h3372, h3373, h3377, h3379, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3380_1]
                                · have p3380_0 := h3380c.1
                                  have p3380_1 := h3380c.2.1
                                  have p3380_2 := h3380c.2.2.1
                                  have p3380_3 := h3380c.2.2.2
                                  linarith only [h3281, hlam, p3380_1]
                                · have p3380_0 := h3380c.1
                                  have p3380_1 := h3380c.2.1
                                  have p3380_2 := h3380c.2.2.1
                                  have p3380_3 := h3380c.2.2.2
                                  linarith only [hlam, p3380_0]
                                · have p3380_0 := h3380c.1
                                  have p3380_1 := h3380c.2.1
                                  have p3380_2 := h3380c.2.2.1
                                  have p3380_3 := h3380c.2.2.2
                                  linarith only [h3284, hlam, p3380_1]
                                · have p3380_0 := h3380c.1
                                  have p3380_1 := h3380c.2.1
                                  have p3380_2 := h3380c.2.2.1
                                  have p3380_3 := h3380c.2.2.2
                                  linarith only [h3280, h3284, h3370, h3372, h3373, h3377, h3379, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3380_1]
                                · have p3380_0 := h3380c.1
                                  have p3380_1 := h3380c.2.1
                                  have p3380_2 := h3380c.2.2.1
                                  have p3380_3 := h3380c.2.2.2
                                  linarith only [h3280, h3372, h3377, h3379, hc45, hlam, hphi, ht0b, ht5b, p3380_1, u0elo3]
                                · have p3380_0 := h3380c.1
                                  have p3380_1 := h3380c.2.1
                                  have p3380_2 := h3380c.2.2.1
                                  have p3380_3 := h3380c.2.2.2
                                  linarith only [h3282, hlam, p3380_0]
                                · have p3380_0 := h3380c.1
                                  have p3380_1 := h3380c.2.1
                                  have p3380_2 := h3380c.2.2.1
                                  have p3380_3 := h3380c.2.2.2
                                  linarith only [h1951, h3280, h3284, h3370, h3372, h3373, h3377, h3379, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3380_1]
                                · have p3380_0 := h3380c.1
                                  have p3380_1 := h3380c.2.1
                                  have p3380_2 := h3380c.2.2.1
                                  have p3380_3 := h3380c.2.2.2
                                  linarith only [hlam, p3380_0]
                                · have p3380_0 := h3380c.1
                                  have p3380_1 := h3380c.2.1
                                  have p3380_2 := h3380c.2.2.1
                                  have p3380_3 := h3380c.2.2.2
                                  rcases p3380_3 (m.d 0 1) (by simp) with h3402 | h3402
                                  · linarith only [h2940, h3402, hlam]
                                  · linarith only [h3280, h3402, hlam]
                                · have p3380_0 := h3380c.1
                                  have p3380_1 := h3380c.2.1
                                  have p3380_2 := h3380c.2.2.1
                                  have p3380_3 := h3380c.2.2.2
                                  linarith only [h3280, hlam, p3380_0]
                                · have p3380_0 := h3380c.1
                                  have p3380_1 := h3380c.2.1
                                  have p3380_2 := h3380c.2.2.1
                                  have p3380_3 := h3380c.2.2.2
                                  linarith only [h3283, hlam, p3380_1]
                                · have p3380_0 := h3380c.1
                                  have p3380_1 := h3380c.2.1
                                  have p3380_2 := h3380c.2.2.1
                                  have p3380_3 := h3380c.2.2.2
                                  linarith only [h3368, hlam, p3380_0]
                                · have p3380_0 := h3380c.1
                                  have p3380_1 := h3380c.2.1
                                  have p3380_2 := h3380c.2.2.1
                                  have p3380_3 := h3380c.2.2.2
                                  linarith only [h3369, hlam, p3380_1]
                                · have p3380_0 := h3380c.1
                                  have p3380_1 := h3380c.2.1
                                  have p3380_2 := h3380c.2.2.1
                                  have p3380_3 := h3380c.2.2.2
                                  linarith only [hlam, p3380_0]
                              · linarith only [h2940, h3280, h3284, h3372, h3377, h3379, hc35, hlam, hphi, u5elo4]
                            · linarith only [h3369, h3375, h3377, h3378, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                          · linarith only [h3284, h3368, h3370, h3373, h3377, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h3284, h3368, h3373, h3374, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3414 | h3414
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3415 | h3415
                        · linarith only [h1951, h3280, h3372, h3373, h3415, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3417 | h3417
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3418 | h3418
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3419 | h3419
                              · rcases h0bigk with h3420c | h3420c | h3420c | h3420c | h3420c | h3420c | h3420c | h3420c | h3420c | h3420c | h3420c | h3420c | h3420c | h3420c | h3420c | h3420c | h3420c | h3420c | h3420c | h3420c | h3420c | h3420c | h3420c | h3420c | h3420c
                                · have p3420_0 := h3420c.1
                                  have p3420_1 := h3420c.2.1
                                  have p3420_2 := h3420c.2.2.1
                                  have p3420_3 := h3420c.2.2.2
                                  linarith only [hlam, p3420_0]
                                · have p3420_0 := h3420c.1
                                  have p3420_1 := h3420c.2.1
                                  have p3420_2 := h3420c.2.2.1
                                  have p3420_3 := h3420c.2.2.2
                                  linarith only [h0, hlam, p3420_1]
                                · have p3420_0 := h3420c.1
                                  have p3420_1 := h3420c.2.1
                                  have p3420_2 := h3420c.2.2.1
                                  have p3420_3 := h3420c.2.2.2
                                  linarith only [h1951, hlam, p3420_0]
                                · have p3420_0 := h3420c.1
                                  have p3420_1 := h3420c.2.1
                                  have p3420_2 := h3420c.2.2.1
                                  have p3420_3 := h3420c.2.2.2
                                  linarith only [h2940, hlam, p3420_1]
                                · have p3420_0 := h3420c.1
                                  have p3420_1 := h3420c.2.1
                                  have p3420_2 := h3420c.2.2.1
                                  have p3420_3 := h3420c.2.2.2
                                  linarith only [h1951, h3373, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3420_1]
                                · have p3420_0 := h3420c.1
                                  have p3420_1 := h3420c.2.1
                                  have p3420_2 := h3420c.2.2.1
                                  have p3420_3 := h3420c.2.2.2
                                  linarith only [h3280, h3372, h3417, h3419, hc45, hlam, hphi, ht0b, ht5b, p3420_1, u0elo1]
                                · have p3420_0 := h3420c.1
                                  have p3420_1 := h3420c.2.1
                                  have p3420_2 := h3420c.2.2.1
                                  have p3420_3 := h3420c.2.2.2
                                  linarith only [hlam, p3420_0]
                                · have p3420_0 := h3420c.1
                                  have p3420_1 := h3420c.2.1
                                  have p3420_2 := h3420c.2.2.1
                                  have p3420_3 := h3420c.2.2.2
                                  linarith only [h1951, h3280, h3372, h3417, h3419, hc45, hlam, hphi, ht0b, ht5b, p3420_1, u0elo1]
                                · have p3420_0 := h3420c.1
                                  have p3420_1 := h3420c.2.1
                                  have p3420_2 := h3420c.2.2.1
                                  have p3420_3 := h3420c.2.2.2
                                  linarith only [h2940, h3280, h3372, h3417, h3419, hc45, hlam, hphi, ht0b, ht5b, p3420_1, u0elo1]
                                · have p3420_0 := h3420c.1
                                  have p3420_1 := h3420c.2.1
                                  have p3420_2 := h3420c.2.2.1
                                  have p3420_3 := h3420c.2.2.2
                                  rcases p3420_3 (m.d 0 1) (by simp) with h3430 | h3430
                                  · linarith only [h0, h3430, hlam]
                                  · linarith only [h3280, h3430, hlam]
                                · have p3420_0 := h3420c.1
                                  have p3420_1 := h3420c.2.1
                                  have p3420_2 := h3420c.2.2.1
                                  have p3420_3 := h3420c.2.2.2
                                  linarith only [h3280, h3372, h3417, h3419, hc45, hlam, hphi, ht0b, ht5b, p3420_1, u0elo2]
                                · have p3420_0 := h3420c.1
                                  have p3420_1 := h3420c.2.1
                                  have p3420_2 := h3420c.2.2.1
                                  have p3420_3 := h3420c.2.2.2
                                  linarith only [h3281, hlam, p3420_1]
                                · have p3420_0 := h3420c.1
                                  have p3420_1 := h3420c.2.1
                                  have p3420_2 := h3420c.2.2.1
                                  have p3420_3 := h3420c.2.2.2
                                  linarith only [hlam, p3420_0]
                                · have p3420_0 := h3420c.1
                                  have p3420_1 := h3420c.2.1
                                  have p3420_2 := h3420c.2.2.1
                                  have p3420_3 := h3420c.2.2.2
                                  linarith only [h3284, hlam, p3420_1]
                                · have p3420_0 := h3420c.1
                                  have p3420_1 := h3420c.2.1
                                  have p3420_2 := h3420c.2.2.1
                                  have p3420_3 := h3420c.2.2.2
                                  rcases p3420_3 (m.d 0 1) (by simp) with h3437 | h3437
                                  · linarith only [h1951, h3437, hlam]
                                  · linarith only [h3280, h3437, hlam]
                                · have p3420_0 := h3420c.1
                                  have p3420_1 := h3420c.2.1
                                  have p3420_2 := h3420c.2.2.1
                                  have p3420_3 := h3420c.2.2.2
                                  linarith only [h3280, h3282, h3372, h3417, h3419, hc45, hlam, hphi, ht0b, ht5b, p3420_1, u0elo1]
                                · have p3420_0 := h3420c.1
                                  have p3420_1 := h3420c.2.1
                                  have p3420_2 := h3420c.2.2.1
                                  have p3420_3 := h3420c.2.2.2
                                  linarith only [h3282, hlam, p3420_0]
                                · have p3420_0 := h3420c.1
                                  have p3420_1 := h3420c.2.1
                                  have p3420_2 := h3420c.2.2.1
                                  have p3420_3 := h3420c.2.2.2
                                  linarith only [h1951, h3280, h3282, h3372, h3417, h3419, hc45, hlam, hphi, ht0b, ht5b, p3420_1, u0elo1]
                                · have p3420_0 := h3420c.1
                                  have p3420_1 := h3420c.2.1
                                  have p3420_2 := h3420c.2.2.1
                                  have p3420_3 := h3420c.2.2.2
                                  linarith only [hlam, p3420_0]
                                · have p3420_0 := h3420c.1
                                  have p3420_1 := h3420c.2.1
                                  have p3420_2 := h3420c.2.2.1
                                  have p3420_3 := h3420c.2.2.2
                                  rcases p3420_3 (m.d 0 1) (by simp) with h3444 | h3444
                                  · linarith only [h2940, h3444, hlam]
                                  · linarith only [h3280, h3444, hlam]
                                · have p3420_0 := h3420c.1
                                  have p3420_1 := h3420c.2.1
                                  have p3420_2 := h3420c.2.2.1
                                  have p3420_3 := h3420c.2.2.2
                                  linarith only [h3280, hlam, p3420_0]
                                · have p3420_0 := h3420c.1
                                  have p3420_1 := h3420c.2.1
                                  have p3420_2 := h3420c.2.2.1
                                  have p3420_3 := h3420c.2.2.2
                                  linarith only [h3283, hlam, p3420_1]
                                · have p3420_0 := h3420c.1
                                  have p3420_1 := h3420c.2.1
                                  have p3420_2 := h3420c.2.2.1
                                  have p3420_3 := h3420c.2.2.2
                                  linarith only [h3368, hlam, p3420_0]
                                · have p3420_0 := h3420c.1
                                  have p3420_1 := h3420c.2.1
                                  have p3420_2 := h3420c.2.2.1
                                  have p3420_3 := h3420c.2.2.2
                                  linarith only [h3369, hlam, p3420_1]
                                · have p3420_0 := h3420c.1
                                  have p3420_1 := h3420c.2.1
                                  have p3420_2 := h3420c.2.2.1
                                  have p3420_3 := h3420c.2.2.2
                                  linarith only [hlam, p3420_0]
                              · linarith only [h3373, h3419, hc13, hlam, hphi, ht34, ht45, u5elo4]
                            · linarith only [h1951, h3280, h3369, h3373, h3415, h3418, hc23, hc34, hlam, hphi]
                          · linarith only [h1951, h3368, h3373, h3417, hc23, hc34, hlam, hphi]
                      · linarith only [h1951, h3280, h3368, h3414, hlam]
                  · linarith only [h0, h3372, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                · linarith only [h0, h3282, h3371, hlam]
              · linarith only [h0, h3281, h3370, hlam]
            · linarith only [h2940, h3280, h3369, hc15, hlam, hphi, u5elo4]
          · linarith only [h1951, h3280, h3368, hc15, hlam, hphi, u5elo3]
      · linarith only [h0, h3280, h3283, hc15, hlam, hphi, u5elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3462 | h3462
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3463 | h3463
        · linarith only [h3281, h3282, h3463, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3465 | h3465
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3466 | h3466
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3467 | h3467
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3468 | h3468
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3469 | h3469
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3470 | h3470
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3471 | h3471
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3472 | h3472
                        · linarith only [h1951, h3280, h3281, h3463, h3469, h3472, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3474 | h3474
                          · linarith only [h3281, h3282, h3467, h3470, h3472, h3474, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h3281, h3282, h3465, h3467, h3470, h3472, h3474, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h3281, h3465, h3470, h3471, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3478 | h3478
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3479 | h3479
                        · linarith only [h1951, h3280, h3469, h3470, h3479, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3481 | h3481
                          · linarith only [h3281, h3282, h3468, h3481, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h3281, h3282, h3465, h3468, h3481, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h1951, h3280, h3281, h3282, h3465, h3468, h3469, h3478, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h3282, h3468, h3469, hc02, hc25, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3486 | h3486
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3487 | h3487
                    · linarith only [h1951, h3280, h3463, h3467, h3468, h3486, h3487, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3489 | h3489
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3490 | h3490
                        · linarith only [h3281, h3487, h3490, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3492 | h3492
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3493 | h3493
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3494 | h3494
                              · rcases h0bigk with h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c
                                · have p3495_0 := h3495c.1
                                  have p3495_1 := h3495c.2.1
                                  have p3495_2 := h3495c.2.2.1
                                  have p3495_3 := h3495c.2.2.2
                                  linarith only [hlam, p3495_0]
                                · have p3495_0 := h3495c.1
                                  have p3495_1 := h3495c.2.1
                                  have p3495_2 := h3495c.2.2.1
                                  have p3495_3 := h3495c.2.2.2
                                  linarith only [h0, hlam, p3495_1]
                                · have p3495_0 := h3495c.1
                                  have p3495_1 := h3495c.2.1
                                  have p3495_2 := h3495c.2.2.1
                                  have p3495_3 := h3495c.2.2.2
                                  linarith only [h1951, hlam, p3495_0]
                                · have p3495_0 := h3495c.1
                                  have p3495_1 := h3495c.2.1
                                  have p3495_2 := h3495c.2.2.1
                                  have p3495_3 := h3495c.2.2.2
                                  linarith only [h2940, hlam, p3495_1]
                                · have p3495_0 := h3495c.1
                                  have p3495_1 := h3495c.2.1
                                  have p3495_2 := h3495c.2.2.1
                                  have p3495_3 := h3495c.2.2.2
                                  linarith only [h0, h3468, h3490, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3495_1]
                                · have p3495_0 := h3495c.1
                                  have p3495_1 := h3495c.2.1
                                  have p3495_2 := h3495c.2.2.1
                                  have p3495_3 := h3495c.2.2.2
                                  linarith only [h0, h3468, h3490, hc01, hc34, hlam, hphi, ht12, ht23, p3495_1]
                                · have p3495_0 := h3495c.1
                                  have p3495_1 := h3495c.2.1
                                  have p3495_2 := h3495c.2.2.1
                                  have p3495_3 := h3495c.2.2.2
                                  linarith only [hlam, p3495_0]
                                · have p3495_0 := h3495c.1
                                  have p3495_1 := h3495c.2.1
                                  have p3495_2 := h3495c.2.2.1
                                  have p3495_3 := h3495c.2.2.2
                                  linarith only [h0, h1951, h3280, h3468, h3486, h3490, h3492, h3494, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3495_1]
                                · have p3495_0 := h3495c.1
                                  have p3495_1 := h3495c.2.1
                                  have p3495_2 := h3495c.2.2.1
                                  have p3495_3 := h3495c.2.2.2
                                  linarith only [h3282, hlam, p3495_1]
                                · have p3495_0 := h3495c.1
                                  have p3495_1 := h3495c.2.1
                                  have p3495_2 := h3495c.2.2.1
                                  have p3495_3 := h3495c.2.2.2
                                  rcases p3495_3 (m.d 0 1) (by simp) with h3505 | h3505
                                  · linarith only [h0, h3505, hlam]
                                  · linarith only [h3280, h3505, hlam]
                                · have p3495_0 := h3495c.1
                                  have p3495_1 := h3495c.2.1
                                  have p3495_2 := h3495c.2.2.1
                                  have p3495_3 := h3495c.2.2.2
                                  linarith only [h3280, h3486, h3492, h3494, hc45, hlam, hphi, ht0b, ht5b, p3495_1, u0elo2]
                                · have p3495_0 := h3495c.1
                                  have p3495_1 := h3495c.2.1
                                  have p3495_2 := h3495c.2.2.1
                                  have p3495_3 := h3495c.2.2.2
                                  linarith only [h3281, hlam, p3495_1]
                                · have p3495_0 := h3495c.1
                                  have p3495_1 := h3495c.2.1
                                  have p3495_2 := h3495c.2.2.1
                                  have p3495_3 := h3495c.2.2.2
                                  linarith only [hlam, p3495_0]
                                · have p3495_0 := h3495c.1
                                  have p3495_1 := h3495c.2.1
                                  have p3495_2 := h3495c.2.2.1
                                  have p3495_3 := h3495c.2.2.2
                                  linarith only [h3463, hlam, p3495_1]
                                · have p3495_0 := h3495c.1
                                  have p3495_1 := h3495c.2.1
                                  have p3495_2 := h3495c.2.2.1
                                  have p3495_3 := h3495c.2.2.2
                                  rcases p3495_3 (m.d 0 1) (by simp) with h3512 | h3512
                                  · linarith only [h1951, h3512, hlam]
                                  · linarith only [h3280, h3512, hlam]
                                · have p3495_0 := h3495c.1
                                  have p3495_1 := h3495c.2.1
                                  have p3495_2 := h3495c.2.2.1
                                  have p3495_3 := h3495c.2.2.2
                                  linarith only [h3280, h3486, h3492, h3494, hc45, hlam, hphi, ht0b, ht5b, p3495_1, u0elo3]
                                · have p3495_0 := h3495c.1
                                  have p3495_1 := h3495c.2.1
                                  have p3495_2 := h3495c.2.2.1
                                  have p3495_3 := h3495c.2.2.2
                                  linarith only [h3281, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3495_1, u0elo3]
                                · have p3495_0 := h3495c.1
                                  have p3495_1 := h3495c.2.1
                                  have p3495_2 := h3495c.2.2.1
                                  have p3495_3 := h3495c.2.2.2
                                  linarith only [h1951, h3280, h3486, h3492, h3494, hc45, hlam, hphi, ht0b, ht5b, p3495_1, u0elo3]
                                · have p3495_0 := h3495c.1
                                  have p3495_1 := h3495c.2.1
                                  have p3495_2 := h3495c.2.2.1
                                  have p3495_3 := h3495c.2.2.2
                                  linarith only [hlam, p3495_0]
                                · have p3495_0 := h3495c.1
                                  have p3495_1 := h3495c.2.1
                                  have p3495_2 := h3495c.2.2.1
                                  have p3495_3 := h3495c.2.2.2
                                  rcases p3495_3 (m.d 0 1) (by simp) with h3519 | h3519
                                  · linarith only [h2940, h3519, hlam]
                                  · linarith only [h3280, h3519, hlam]
                                · have p3495_0 := h3495c.1
                                  have p3495_1 := h3495c.2.1
                                  have p3495_2 := h3495c.2.2.1
                                  have p3495_3 := h3495c.2.2.2
                                  linarith only [h3280, hlam, p3495_0]
                                · have p3495_0 := h3495c.1
                                  have p3495_1 := h3495c.2.1
                                  have p3495_2 := h3495c.2.2.1
                                  have p3495_3 := h3495c.2.2.2
                                  linarith only [h3462, hlam, p3495_1]
                                · have p3495_0 := h3495c.1
                                  have p3495_1 := h3495c.2.1
                                  have p3495_2 := h3495c.2.2.1
                                  have p3495_3 := h3495c.2.2.2
                                  linarith only [h3465, hlam, p3495_0]
                                · have p3495_0 := h3495c.1
                                  have p3495_1 := h3495c.2.1
                                  have p3495_2 := h3495c.2.2.1
                                  have p3495_3 := h3495c.2.2.2
                                  linarith only [h3466, hlam, p3495_1]
                                · have p3495_0 := h3495c.1
                                  have p3495_1 := h3495c.2.1
                                  have p3495_2 := h3495c.2.2.1
                                  have p3495_3 := h3495c.2.2.2
                                  linarith only [hlam, p3495_0]
                              · linarith only [h1951, h3280, h3467, h3468, h3486, h3490, h3492, h3494, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                            · linarith only [h1951, h3280, h3467, h3468, h3486, h3492, h3493, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h1951, h3465, h3467, h3468, h3490, h3492, hc23, hc34, hlam, hphi]
                      · linarith only [h1951, h3465, h3489, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
                  · linarith only [h0, h3280, h3486, hc15, hlam, hphi, u5elo2]
              · linarith only [h0, h3281, h3467, hlam]
            · linarith only [h2940, h3280, h3466, hc15, hlam, hphi, u5elo4]
          · linarith only [h1951, h3280, h3465, hc15, hlam, hphi, u5elo3]
      · linarith only [h3281, h3462, hc23, hlam, hphi, ht34, ht45, u5elo2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h3536 | h3536
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3537 | h3537
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3538 | h3538
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3539 | h3539
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3540 | h3540
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3541 | h3541
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3542 | h3542
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3543 | h3543
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3544 | h3544
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3545 | h3545
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3546 | h3546
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3547 | h3547
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3548 | h3548
                            · linarith only [h3281, h3536, h3541, h3548, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h3281, h3536, h3540, h3541, h3548, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h2940, h3281, h3536, h3547, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                        · linarith only [h2940, h3281, h3536, h3538, h3546, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h1951, h3280, h3543, h3545, hc25, hlam, hphi, u5elo3]
                    · linarith only [h3281, h3536, h3538, h3541, h3544, hlam]
                  · linarith only [h0, h3543, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                · linarith only [h3281, h3536, h3541, h3542, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3557 | h3557
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3558 | h3558
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3559 | h3559
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3560 | h3560
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3561 | h3561
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3562 | h3562
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3563 | h3563
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3564 | h3564
                              · rcases h0bigk with h3565c | h3565c | h3565c | h3565c | h3565c | h3565c | h3565c | h3565c | h3565c | h3565c | h3565c | h3565c | h3565c | h3565c | h3565c | h3565c | h3565c | h3565c | h3565c | h3565c | h3565c | h3565c | h3565c | h3565c | h3565c
                                · have p3565_0 := h3565c.1
                                  have p3565_1 := h3565c.2.1
                                  have p3565_2 := h3565c.2.2.1
                                  have p3565_3 := h3565c.2.2.2
                                  linarith only [hlam, p3565_0]
                                · have p3565_0 := h3565c.1
                                  have p3565_1 := h3565c.2.1
                                  have p3565_2 := h3565c.2.2.1
                                  have p3565_3 := h3565c.2.2.2
                                  linarith only [h0, hlam, p3565_1]
                                · have p3565_0 := h3565c.1
                                  have p3565_1 := h3565c.2.1
                                  have p3565_2 := h3565c.2.2.1
                                  have p3565_3 := h3565c.2.2.2
                                  linarith only [h1951, hlam, p3565_0]
                                · have p3565_0 := h3565c.1
                                  have p3565_1 := h3565c.2.1
                                  have p3565_2 := h3565c.2.2.1
                                  have p3565_3 := h3565c.2.2.2
                                  linarith only [h2940, hlam, p3565_1]
                                · have p3565_0 := h3565c.1
                                  have p3565_1 := h3565c.2.1
                                  have p3565_2 := h3565c.2.2.1
                                  have p3565_3 := h3565c.2.2.2
                                  linarith only [h0, h3541, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3565_1]
                                · have p3565_0 := h3565c.1
                                  have p3565_1 := h3565c.2.1
                                  have p3565_2 := h3565c.2.2.1
                                  have p3565_3 := h3565c.2.2.2
                                  linarith only [h0, h3541, hc01, hc23, hlam, hphi, ht12, p3565_1]
                                · have p3565_0 := h3565c.1
                                  have p3565_1 := h3565c.2.1
                                  have p3565_2 := h3565c.2.2.1
                                  have p3565_3 := h3565c.2.2.2
                                  linarith only [hlam, p3565_0]
                                · have p3565_0 := h3565c.1
                                  have p3565_1 := h3565c.2.1
                                  have p3565_2 := h3565c.2.2.1
                                  have p3565_3 := h3565c.2.2.2
                                  linarith only [h3281, hlam, p3565_0]
                                · have p3565_0 := h3565c.1
                                  have p3565_1 := h3565c.2.1
                                  have p3565_2 := h3565c.2.2.1
                                  have p3565_3 := h3565c.2.2.2
                                  linarith only [h0, h2940, h3280, h3541, h3558, h3562, h3564, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3565_1]
                                · have p3565_0 := h3565c.1
                                  have p3565_1 := h3565c.2.1
                                  have p3565_2 := h3565c.2.2.1
                                  have p3565_3 := h3565c.2.2.2
                                  rcases p3565_3 (m.d 0 1) (by simp) with h3575 | h3575
                                  · linarith only [h0, h3575, hlam]
                                  · linarith only [h3280, h3575, hlam]
                                · have p3565_0 := h3565c.1
                                  have p3565_1 := h3565c.2.1
                                  have p3565_2 := h3565c.2.2.1
                                  have p3565_3 := h3565c.2.2.2
                                  linarith only [h3280, h3558, h3562, h3564, hc45, hlam, hphi, ht0b, ht5b, p3565_1, u0elo2]
                                · have p3565_0 := h3565c.1
                                  have p3565_1 := h3565c.2.1
                                  have p3565_2 := h3565c.2.2.1
                                  have p3565_3 := h3565c.2.2.2
                                  linarith only [h0, h3280, h3558, h3562, h3564, hc45, hlam, hphi, ht0b, ht5b, p3565_1, u0elo2]
                                · have p3565_0 := h3565c.1
                                  have p3565_1 := h3565c.2.1
                                  have p3565_2 := h3565c.2.2.1
                                  have p3565_3 := h3565c.2.2.2
                                  linarith only [hlam, p3565_0]
                                · have p3565_0 := h3565c.1
                                  have p3565_1 := h3565c.2.1
                                  have p3565_2 := h3565c.2.2.1
                                  have p3565_3 := h3565c.2.2.2
                                  linarith only [h2940, h3280, h3558, h3562, h3564, hc45, hlam, hphi, ht0b, ht5b, p3565_1, u0elo2]
                                · have p3565_0 := h3565c.1
                                  have p3565_1 := h3565c.2.1
                                  have p3565_2 := h3565c.2.2.1
                                  have p3565_3 := h3565c.2.2.2
                                  rcases p3565_3 (m.d 0 1) (by simp) with h3582 | h3582
                                  · linarith only [h1951, h3582, hlam]
                                  · linarith only [h3280, h3582, hlam]
                                · have p3565_0 := h3565c.1
                                  have p3565_1 := h3565c.2.1
                                  have p3565_2 := h3565c.2.2.1
                                  have p3565_3 := h3565c.2.2.2
                                  linarith only [h3280, h3558, h3562, h3564, hc45, hlam, hphi, ht0b, ht5b, p3565_1, u0elo3]
                                · have p3565_0 := h3565c.1
                                  have p3565_1 := h3565c.2.1
                                  have p3565_2 := h3565c.2.2.1
                                  have p3565_3 := h3565c.2.2.2
                                  linarith only [h3536, hlam, p3565_0]
                                · have p3565_0 := h3565c.1
                                  have p3565_1 := h3565c.2.1
                                  have p3565_2 := h3565c.2.2.1
                                  have p3565_3 := h3565c.2.2.2
                                  linarith only [h3538, hlam, p3565_0]
                                · have p3565_0 := h3565c.1
                                  have p3565_1 := h3565c.2.1
                                  have p3565_2 := h3565c.2.2.1
                                  have p3565_3 := h3565c.2.2.2
                                  linarith only [hlam, p3565_0]
                                · have p3565_0 := h3565c.1
                                  have p3565_1 := h3565c.2.1
                                  have p3565_2 := h3565c.2.2.1
                                  have p3565_3 := h3565c.2.2.2
                                  rcases p3565_3 (m.d 0 1) (by simp) with h3589 | h3589
                                  · linarith only [h2940, h3589, hlam]
                                  · linarith only [h3280, h3589, hlam]
                                · have p3565_0 := h3565c.1
                                  have p3565_1 := h3565c.2.1
                                  have p3565_2 := h3565c.2.2.1
                                  have p3565_3 := h3565c.2.2.2
                                  linarith only [h3280, hlam, p3565_0]
                                · have p3565_0 := h3565c.1
                                  have p3565_1 := h3565c.2.1
                                  have p3565_2 := h3565c.2.2.1
                                  have p3565_3 := h3565c.2.2.2
                                  linarith only [h3537, hlam, p3565_1]
                                · have p3565_0 := h3565c.1
                                  have p3565_1 := h3565c.2.1
                                  have p3565_2 := h3565c.2.2.1
                                  have p3565_3 := h3565c.2.2.2
                                  linarith only [h3539, hlam, p3565_0]
                                · have p3565_0 := h3565c.1
                                  have p3565_1 := h3565c.2.1
                                  have p3565_2 := h3565c.2.2.1
                                  have p3565_3 := h3565c.2.2.2
                                  linarith only [h3540, hlam, p3565_1]
                                · have p3565_0 := h3565c.1
                                  have p3565_1 := h3565c.2.1
                                  have p3565_2 := h3565c.2.2.1
                                  have p3565_3 := h3565c.2.2.2
                                  linarith only [hlam, p3565_0]
                              · linarith only [h0, h3536, h3541, h3563, h3564, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3598 | h3598
                              · linarith only [h3561, h3563, h3598, hlam]
                              · rcases h0bigk with h3600c | h3600c | h3600c | h3600c | h3600c | h3600c | h3600c | h3600c | h3600c | h3600c | h3600c | h3600c | h3600c | h3600c | h3600c | h3600c | h3600c | h3600c | h3600c | h3600c | h3600c | h3600c | h3600c | h3600c | h3600c
                                · have p3600_0 := h3600c.1
                                  have p3600_1 := h3600c.2.1
                                  have p3600_2 := h3600c.2.2.1
                                  have p3600_3 := h3600c.2.2.2
                                  linarith only [hlam, p3600_0]
                                · have p3600_0 := h3600c.1
                                  have p3600_1 := h3600c.2.1
                                  have p3600_2 := h3600c.2.2.1
                                  have p3600_3 := h3600c.2.2.2
                                  linarith only [h0, hlam, p3600_1]
                                · have p3600_0 := h3600c.1
                                  have p3600_1 := h3600c.2.1
                                  have p3600_2 := h3600c.2.2.1
                                  have p3600_3 := h3600c.2.2.2
                                  linarith only [h1951, hlam, p3600_0]
                                · have p3600_0 := h3600c.1
                                  have p3600_1 := h3600c.2.1
                                  have p3600_2 := h3600c.2.2.1
                                  have p3600_3 := h3600c.2.2.2
                                  linarith only [h2940, hlam, p3600_1]
                                · have p3600_0 := h3600c.1
                                  have p3600_1 := h3600c.2.1
                                  have p3600_2 := h3600c.2.2.1
                                  have p3600_3 := h3600c.2.2.2
                                  linarith only [h3540, h3561, h3563, hc34, hlam, hphi, ht0b, ht45, ht5b, p3600_1, u0elo0]
                                · have p3600_0 := h3600c.1
                                  have p3600_1 := h3600c.2.1
                                  have p3600_2 := h3600c.2.2.1
                                  have p3600_3 := h3600c.2.2.2
                                  linarith only [h0, h3541, hc01, hc23, hlam, hphi, ht12, p3600_1]
                                · have p3600_0 := h3600c.1
                                  have p3600_1 := h3600c.2.1
                                  have p3600_2 := h3600c.2.2.1
                                  have p3600_3 := h3600c.2.2.2
                                  linarith only [hlam, p3600_0]
                                · have p3600_0 := h3600c.1
                                  have p3600_1 := h3600c.2.1
                                  have p3600_2 := h3600c.2.2.1
                                  have p3600_3 := h3600c.2.2.2
                                  linarith only [h3281, hlam, p3600_0]
                                · have p3600_0 := h3600c.1
                                  have p3600_1 := h3600c.2.1
                                  have p3600_2 := h3600c.2.2.1
                                  have p3600_3 := h3600c.2.2.2
                                  linarith only [h0, h2940, h3280, h3541, h3558, h3561, h3563, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3600_1]
                                · have p3600_0 := h3600c.1
                                  have p3600_1 := h3600c.2.1
                                  have p3600_2 := h3600c.2.2.1
                                  have p3600_3 := h3600c.2.2.2
                                  linarith only [h0, h3540, h3541, h3561, h3563, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3600_1]
                                · have p3600_0 := h3600c.1
                                  have p3600_1 := h3600c.2.1
                                  have p3600_2 := h3600c.2.2.1
                                  have p3600_3 := h3600c.2.2.2
                                  linarith only [h3280, h3558, h3561, h3563, hc34, hlam, hphi, ht0b, ht45, ht5b, p3600_1, u0elo2]
                                · have p3600_0 := h3600c.1
                                  have p3600_1 := h3600c.2.1
                                  have p3600_2 := h3600c.2.2.1
                                  have p3600_3 := h3600c.2.2.2
                                  linarith only [h0, h3280, h3558, h3561, h3563, hc34, hlam, hphi, ht0b, ht45, ht5b, p3600_1, u0elo2]
                                · have p3600_0 := h3600c.1
                                  have p3600_1 := h3600c.2.1
                                  have p3600_2 := h3600c.2.2.1
                                  have p3600_3 := h3600c.2.2.2
                                  linarith only [hlam, p3600_0]
                                · have p3600_0 := h3600c.1
                                  have p3600_1 := h3600c.2.1
                                  have p3600_2 := h3600c.2.2.1
                                  have p3600_3 := h3600c.2.2.2
                                  linarith only [h2940, h3280, h3558, h3561, h3563, hc34, hlam, hphi, ht0b, ht45, ht5b, p3600_1, u0elo2]
                                · have p3600_0 := h3600c.1
                                  have p3600_1 := h3600c.2.1
                                  have p3600_2 := h3600c.2.2.1
                                  have p3600_3 := h3600c.2.2.2
                                  linarith only [h3540, h3561, h3563, hc34, hlam, hphi, ht0b, ht45, ht5b, p3600_1, u0elo2]
                                · have p3600_0 := h3600c.1
                                  have p3600_1 := h3600c.2.1
                                  have p3600_2 := h3600c.2.2.1
                                  have p3600_3 := h3600c.2.2.2
                                  linarith only [h3280, h3536, h3558, h3561, h3563, hc34, hlam, hphi, ht0b, ht45, ht5b, p3600_1, u0elo1]
                                · have p3600_0 := h3600c.1
                                  have p3600_1 := h3600c.2.1
                                  have p3600_2 := h3600c.2.2.1
                                  have p3600_3 := h3600c.2.2.2
                                  linarith only [h3536, hlam, p3600_0]
                                · have p3600_0 := h3600c.1
                                  have p3600_1 := h3600c.2.1
                                  have p3600_2 := h3600c.2.2.1
                                  have p3600_3 := h3600c.2.2.2
                                  linarith only [h3538, hlam, p3600_0]
                                · have p3600_0 := h3600c.1
                                  have p3600_1 := h3600c.2.1
                                  have p3600_2 := h3600c.2.2.1
                                  have p3600_3 := h3600c.2.2.2
                                  linarith only [hlam, p3600_0]
                                · have p3600_0 := h3600c.1
                                  have p3600_1 := h3600c.2.1
                                  have p3600_2 := h3600c.2.2.1
                                  have p3600_3 := h3600c.2.2.2
                                  linarith only [h0, h3536, h3540, h3541, h3561, h3563, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3600_1]
                                · have p3600_0 := h3600c.1
                                  have p3600_1 := h3600c.2.1
                                  have p3600_2 := h3600c.2.2.1
                                  have p3600_3 := h3600c.2.2.2
                                  linarith only [h3280, hlam, p3600_0]
                                · have p3600_0 := h3600c.1
                                  have p3600_1 := h3600c.2.1
                                  have p3600_2 := h3600c.2.2.1
                                  have p3600_3 := h3600c.2.2.2
                                  linarith only [h3537, hlam, p3600_1]
                                · have p3600_0 := h3600c.1
                                  have p3600_1 := h3600c.2.1
                                  have p3600_2 := h3600c.2.2.1
                                  have p3600_3 := h3600c.2.2.2
                                  linarith only [h3539, hlam, p3600_0]
                                · have p3600_0 := h3600c.1
                                  have p3600_1 := h3600c.2.1
                                  have p3600_2 := h3600c.2.2.1
                                  have p3600_3 := h3600c.2.2.2
                                  linarith only [h3540, hlam, p3600_1]
                                · have p3600_0 := h3600c.1
                                  have p3600_1 := h3600c.2.1
                                  have p3600_2 := h3600c.2.2.1
                                  have p3600_3 := h3600c.2.2.2
                                  linarith only [hlam, p3600_0]
                          · linarith only [h0, h3541, h3562, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                        · linarith only [h2940, h3280, h3541, h3557, h3558, h3561, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h1951, h3280, h3558, h3560, hc25, hlam, hphi, u5elo3]
                    · linarith only [h1951, h3280, h3536, h3538, h3558, h3559, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                  · linarith only [h2940, h3557, h3558, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                · linarith only [h0, h3536, h3557, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h2940, h3280, h3540, hc15, hlam, hphi, u5elo4]
          · linarith only [h1951, h3280, h3539, hc15, hlam, hphi, u5elo3]
        · linarith only [h3281, h3536, h3538, hlam]
      · linarith only [h3536, h3537, hc24, hlam, hphi, ht45, u5elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3636 | h3636
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3637 | h3637
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3638 | h3638
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3639 | h3639
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3640 | h3640
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3641 | h3641
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3642 | h3642
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3643 | h3643
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3644 | h3644
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3645 | h3645
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3646 | h3646
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3647 | h3647
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3648 | h3648
                              · rcases h0bigk with h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c
                                · have p3649_0 := h3649c.1
                                  have p3649_1 := h3649c.2.1
                                  have p3649_2 := h3649c.2.2.1
                                  have p3649_3 := h3649c.2.2.2
                                  linarith only [hlam, p3649_0]
                                · have p3649_0 := h3649c.1
                                  have p3649_1 := h3649c.2.1
                                  have p3649_2 := h3649c.2.2.1
                                  have p3649_3 := h3649c.2.2.2
                                  linarith only [h0, hlam, p3649_1]
                                · have p3649_0 := h3649c.1
                                  have p3649_1 := h3649c.2.1
                                  have p3649_2 := h3649c.2.2.1
                                  have p3649_3 := h3649c.2.2.2
                                  linarith only [h1951, hlam, p3649_0]
                                · have p3649_0 := h3649c.1
                                  have p3649_1 := h3649c.2.1
                                  have p3649_2 := h3649c.2.2.1
                                  have p3649_3 := h3649c.2.2.2
                                  linarith only [h2940, hlam, p3649_1]
                                · have p3649_0 := h3649c.1
                                  have p3649_1 := h3649c.2.1
                                  have p3649_2 := h3649c.2.2.1
                                  have p3649_3 := h3649c.2.2.2
                                  linarith only [h0, h3536, h3640, h3645, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p3649_1]
                                · have p3649_0 := h3649c.1
                                  have p3649_1 := h3649c.2.1
                                  have p3649_2 := h3649c.2.2.1
                                  have p3649_3 := h3649c.2.2.2
                                  linarith only [h3536, h3640, h3645, hc01, hc12, hlam, hphi, p3649_1]
                                · have p3649_0 := h3649c.1
                                  have p3649_1 := h3649c.2.1
                                  have p3649_2 := h3649c.2.2.1
                                  have p3649_3 := h3649c.2.2.2
                                  linarith only [hlam, p3649_0]
                                · have p3649_0 := h3649c.1
                                  have p3649_1 := h3649c.2.1
                                  have p3649_2 := h3649c.2.2.1
                                  have p3649_3 := h3649c.2.2.2
                                  linarith only [h3281, hlam, p3649_0]
                                · have p3649_0 := h3649c.1
                                  have p3649_1 := h3649c.2.1
                                  have p3649_2 := h3649c.2.2.1
                                  have p3649_3 := h3649c.2.2.2
                                  linarith only [h3536, hlam, p3649_1]
                                · have p3649_0 := h3649c.1
                                  have p3649_1 := h3649c.2.1
                                  have p3649_2 := h3649c.2.2.1
                                  have p3649_3 := h3649c.2.2.2
                                  linarith only [h3280, h3536, h3640, h3642, h3645, h3646, h3648, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3649_1]
                                · have p3649_0 := h3649c.1
                                  have p3649_1 := h3649c.2.1
                                  have p3649_2 := h3649c.2.2.1
                                  have p3649_3 := h3649c.2.2.2
                                  linarith only [h3280, h3642, h3646, h3648, hc45, hlam, hphi, ht0b, ht5b, p3649_1, u0elo2]
                                · have p3649_0 := h3649c.1
                                  have p3649_1 := h3649c.2.1
                                  have p3649_2 := h3649c.2.2.1
                                  have p3649_3 := h3649c.2.2.2
                                  linarith only [h0, h3280, h3281, h3640, h3642, h3646, h3648, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3649_1]
                                · have p3649_0 := h3649c.1
                                  have p3649_1 := h3649c.2.1
                                  have p3649_2 := h3649c.2.2.1
                                  have p3649_3 := h3649c.2.2.2
                                  linarith only [hlam, p3649_0]
                                · have p3649_0 := h3649c.1
                                  have p3649_1 := h3649c.2.1
                                  have p3649_2 := h3649c.2.2.1
                                  have p3649_3 := h3649c.2.2.2
                                  linarith only [h0, h3280, h3281, h3536, h3640, h3642, h3646, h3648, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3649_1]
                                · have p3649_0 := h3649c.1
                                  have p3649_1 := h3649c.2.1
                                  have p3649_2 := h3649c.2.2.1
                                  have p3649_3 := h3649c.2.2.2
                                  rcases p3649_3 (m.d 0 1) (by simp) with h3664 | h3664
                                  · linarith only [h1951, h3664, hlam]
                                  · linarith only [h3280, h3664, hlam]
                                · have p3649_0 := h3649c.1
                                  have p3649_1 := h3649c.2.1
                                  have p3649_2 := h3649c.2.2.1
                                  have p3649_3 := h3649c.2.2.2
                                  linarith only [h3280, h3642, h3646, h3648, hc45, hlam, hphi, ht0b, ht5b, p3649_1, u0elo3]
                                · have p3649_0 := h3649c.1
                                  have p3649_1 := h3649c.2.1
                                  have p3649_2 := h3649c.2.2.1
                                  have p3649_3 := h3649c.2.2.2
                                  linarith only [h0, h3280, h3536, h3640, h3642, h3645, h3646, h3648, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3649_1]
                                · have p3649_0 := h3649c.1
                                  have p3649_1 := h3649c.2.1
                                  have p3649_2 := h3649c.2.2.1
                                  have p3649_3 := h3649c.2.2.2
                                  linarith only [h3637, hlam, p3649_0]
                                · have p3649_0 := h3649c.1
                                  have p3649_1 := h3649c.2.1
                                  have p3649_2 := h3649c.2.2.1
                                  have p3649_3 := h3649c.2.2.2
                                  linarith only [hlam, p3649_0]
                                · have p3649_0 := h3649c.1
                                  have p3649_1 := h3649c.2.1
                                  have p3649_2 := h3649c.2.2.1
                                  have p3649_3 := h3649c.2.2.2
                                  rcases p3649_3 (m.d 0 1) (by simp) with h3671 | h3671
                                  · linarith only [h2940, h3671, hlam]
                                  · linarith only [h3280, h3671, hlam]
                                · have p3649_0 := h3649c.1
                                  have p3649_1 := h3649c.2.1
                                  have p3649_2 := h3649c.2.2.1
                                  have p3649_3 := h3649c.2.2.2
                                  linarith only [h3280, hlam, p3649_0]
                                · have p3649_0 := h3649c.1
                                  have p3649_1 := h3649c.2.1
                                  have p3649_2 := h3649c.2.2.1
                                  have p3649_3 := h3649c.2.2.2
                                  linarith only [h3636, hlam, p3649_1]
                                · have p3649_0 := h3649c.1
                                  have p3649_1 := h3649c.2.1
                                  have p3649_2 := h3649c.2.2.1
                                  have p3649_3 := h3649c.2.2.2
                                  linarith only [h3638, hlam, p3649_0]
                                · have p3649_0 := h3649c.1
                                  have p3649_1 := h3649c.2.1
                                  have p3649_2 := h3649c.2.2.1
                                  have p3649_3 := h3649c.2.2.2
                                  linarith only [h3639, hlam, p3649_1]
                                · have p3649_0 := h3649c.1
                                  have p3649_1 := h3649c.2.1
                                  have p3649_2 := h3649c.2.2.1
                                  have p3649_3 := h3649c.2.2.2
                                  linarith only [hlam, p3649_0]
                              · linarith only [h0, h3280, h3536, h3640, h3642, h3645, h3647, h3648, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h0, h3536, h3647, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                          · linarith only [h0, h3280, h3536, h3642, h3645, h3646, hc25, hlam, hphi, u5elo3]
                        · linarith only [h3281, h3637, h3645, hlam]
                      · linarith only [h1951, h3280, h3642, h3644, hc25, hlam, hphi, u5elo3]
                    · linarith only [h3281, h3637, h3640, h3643, hlam]
                  · linarith only [h3281, h3637, h3640, h3642, hc34, hlam, hphi, ht45, u5elo2]
                · linarith only [h0, h3281, h3640, h3641, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3687 | h3687
                · linarith only [h0, h3280, h3536, h3640, h3687, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3689 | h3689
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3690 | h3690
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3691 | h3691
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3692 | h3692
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3693 | h3693
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3694 | h3694
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3695 | h3695
                              · rcases h0bigk with h3696c | h3696c | h3696c | h3696c | h3696c | h3696c | h3696c | h3696c | h3696c | h3696c | h3696c | h3696c | h3696c | h3696c | h3696c | h3696c | h3696c | h3696c | h3696c | h3696c | h3696c | h3696c | h3696c | h3696c | h3696c
                                · have p3696_0 := h3696c.1
                                  have p3696_1 := h3696c.2.1
                                  have p3696_2 := h3696c.2.2.1
                                  have p3696_3 := h3696c.2.2.2
                                  linarith only [hlam, p3696_0]
                                · have p3696_0 := h3696c.1
                                  have p3696_1 := h3696c.2.1
                                  have p3696_2 := h3696c.2.2.1
                                  have p3696_3 := h3696c.2.2.2
                                  linarith only [h0, hlam, p3696_1]
                                · have p3696_0 := h3696c.1
                                  have p3696_1 := h3696c.2.1
                                  have p3696_2 := h3696c.2.2.1
                                  have p3696_3 := h3696c.2.2.2
                                  linarith only [h1951, hlam, p3696_0]
                                · have p3696_0 := h3696c.1
                                  have p3696_1 := h3696c.2.1
                                  have p3696_2 := h3696c.2.2.1
                                  have p3696_3 := h3696c.2.2.2
                                  linarith only [h2940, hlam, p3696_1]
                                · have p3696_0 := h3696c.1
                                  have p3696_1 := h3696c.2.1
                                  have p3696_2 := h3696c.2.2.1
                                  have p3696_3 := h3696c.2.2.2
                                  linarith only [h0, h3687, h3692, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3696_1]
                                · have p3696_0 := h3696c.1
                                  have p3696_1 := h3696c.2.1
                                  have p3696_2 := h3696c.2.2.1
                                  have p3696_3 := h3696c.2.2.2
                                  linarith only [h0, h3687, h3692, hc01, hc23, hlam, hphi, ht12, p3696_1]
                                · have p3696_0 := h3696c.1
                                  have p3696_1 := h3696c.2.1
                                  have p3696_2 := h3696c.2.2.1
                                  have p3696_3 := h3696c.2.2.2
                                  linarith only [hlam, p3696_0]
                                · have p3696_0 := h3696c.1
                                  have p3696_1 := h3696c.2.1
                                  have p3696_2 := h3696c.2.2.1
                                  have p3696_3 := h3696c.2.2.2
                                  linarith only [h3281, hlam, p3696_0]
                                · have p3696_0 := h3696c.1
                                  have p3696_1 := h3696c.2.1
                                  have p3696_2 := h3696c.2.2.1
                                  have p3696_3 := h3696c.2.2.2
                                  linarith only [h3536, hlam, p3696_1]
                                · have p3696_0 := h3696c.1
                                  have p3696_1 := h3696c.2.1
                                  have p3696_2 := h3696c.2.2.1
                                  have p3696_3 := h3696c.2.2.2
                                  rcases p3696_3 (m.d 0 1) (by simp) with h3706 | h3706
                                  · linarith only [h0, h3706, hlam]
                                  · linarith only [h3280, h3706, hlam]
                                · have p3696_0 := h3696c.1
                                  have p3696_1 := h3696c.2.1
                                  have p3696_2 := h3696c.2.2.1
                                  have p3696_3 := h3696c.2.2.2
                                  linarith only [h3280, h3689, h3693, h3695, hc45, hlam, hphi, ht0b, ht5b, p3696_1, u0elo2]
                                · have p3696_0 := h3696c.1
                                  have p3696_1 := h3696c.2.1
                                  have p3696_2 := h3696c.2.2.1
                                  have p3696_3 := h3696c.2.2.2
                                  linarith only [h0, h3280, h3689, h3693, h3695, hc45, hlam, hphi, ht0b, ht5b, p3696_1, u0elo2]
                                · have p3696_0 := h3696c.1
                                  have p3696_1 := h3696c.2.1
                                  have p3696_2 := h3696c.2.2.1
                                  have p3696_3 := h3696c.2.2.2
                                  linarith only [hlam, p3696_0]
                                · have p3696_0 := h3696c.1
                                  have p3696_1 := h3696c.2.1
                                  have p3696_2 := h3696c.2.2.1
                                  have p3696_3 := h3696c.2.2.2
                                  linarith only [h0, h3280, h3536, h3689, h3693, h3695, hc45, hlam, hphi, ht0b, ht5b, p3696_1, u0elo2]
                                · have p3696_0 := h3696c.1
                                  have p3696_1 := h3696c.2.1
                                  have p3696_2 := h3696c.2.2.1
                                  have p3696_3 := h3696c.2.2.2
                                  rcases p3696_3 (m.d 0 1) (by simp) with h3713 | h3713
                                  · linarith only [h1951, h3713, hlam]
                                  · linarith only [h3280, h3713, hlam]
                                · have p3696_0 := h3696c.1
                                  have p3696_1 := h3696c.2.1
                                  have p3696_2 := h3696c.2.2.1
                                  have p3696_3 := h3696c.2.2.2
                                  linarith only [h3280, h3689, h3693, h3695, hc45, hlam, hphi, ht0b, ht5b, p3696_1, u0elo3]
                                · have p3696_0 := h3696c.1
                                  have p3696_1 := h3696c.2.1
                                  have p3696_2 := h3696c.2.2.1
                                  have p3696_3 := h3696c.2.2.2
                                  linarith only [h0, h3280, h3689, h3693, h3695, hc45, hlam, hphi, ht0b, ht5b, p3696_1, u0elo3]
                                · have p3696_0 := h3696c.1
                                  have p3696_1 := h3696c.2.1
                                  have p3696_2 := h3696c.2.2.1
                                  have p3696_3 := h3696c.2.2.2
                                  linarith only [h3637, hlam, p3696_0]
                                · have p3696_0 := h3696c.1
                                  have p3696_1 := h3696c.2.1
                                  have p3696_2 := h3696c.2.2.1
                                  have p3696_3 := h3696c.2.2.2
                                  linarith only [hlam, p3696_0]
                                · have p3696_0 := h3696c.1
                                  have p3696_1 := h3696c.2.1
                                  have p3696_2 := h3696c.2.2.1
                                  have p3696_3 := h3696c.2.2.2
                                  rcases p3696_3 (m.d 0 1) (by simp) with h3720 | h3720
                                  · linarith only [h2940, h3720, hlam]
                                  · linarith only [h3280, h3720, hlam]
                                · have p3696_0 := h3696c.1
                                  have p3696_1 := h3696c.2.1
                                  have p3696_2 := h3696c.2.2.1
                                  have p3696_3 := h3696c.2.2.2
                                  linarith only [h3280, hlam, p3696_0]
                                · have p3696_0 := h3696c.1
                                  have p3696_1 := h3696c.2.1
                                  have p3696_2 := h3696c.2.2.1
                                  have p3696_3 := h3696c.2.2.2
                                  linarith only [h3636, hlam, p3696_1]
                                · have p3696_0 := h3696c.1
                                  have p3696_1 := h3696c.2.1
                                  have p3696_2 := h3696c.2.2.1
                                  have p3696_3 := h3696c.2.2.2
                                  linarith only [h3638, hlam, p3696_0]
                                · have p3696_0 := h3696c.1
                                  have p3696_1 := h3696c.2.1
                                  have p3696_2 := h3696c.2.2.1
                                  have p3696_3 := h3696c.2.2.2
                                  linarith only [h3639, hlam, p3696_1]
                                · have p3696_0 := h3696c.1
                                  have p3696_1 := h3696c.2.1
                                  have p3696_2 := h3696c.2.2.1
                                  have p3696_3 := h3696c.2.2.2
                                  linarith only [hlam, p3696_0]
                              · linarith only [h0, h3280, h3687, h3689, h3692, h3694, h3695, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h3687, h3694, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h0, h3280, h3687, h3691, h3692, h3693, hlam]
                        · linarith only [h1951, h3637, h3640, h3692, hlam]
                      · linarith only [h1951, h3637, h3691, hc34, hlam, hphi, ht45, u5elo3]
                    · linarith only [h1951, h3637, h3690, hlam]
                  · linarith only [h0, h3280, h3689, hc15, hlam, hphi, u5elo2]
            · linarith only [h2940, h3280, h3639, hc15, hlam, hphi, u5elo4]
          · linarith only [h3637, h3638, hc34, hlam, hphi, ht45, u5elo3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3737 | h3737
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3738 | h3738
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3739 | h3739
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3740 | h3740
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3741 | h3741
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3742 | h3742
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3743 | h3743
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3744 | h3744
                        · linarith only [h0, h3280, h3281, h3637, h3739, h3741, h3744, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h0, h3280, h3281, h3739, h3741, h3742, h3744, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h3742, h3743, hc34, hlam, hphi, ht45, u5elo3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3748 | h3748
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3749 | h3749
                        · linarith only [h3739, h3742, h3749, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3751 | h3751
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3752 | h3752
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3753 | h3753
                              · rcases h0bigk with h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c | h3754c
                                · have p3754_0 := h3754c.1
                                  have p3754_1 := h3754c.2.1
                                  have p3754_2 := h3754c.2.2.1
                                  have p3754_3 := h3754c.2.2.2
                                  linarith only [hlam, p3754_0]
                                · have p3754_0 := h3754c.1
                                  have p3754_1 := h3754c.2.1
                                  have p3754_2 := h3754c.2.2.1
                                  have p3754_3 := h3754c.2.2.2
                                  linarith only [h0, hlam, p3754_1]
                                · have p3754_0 := h3754c.1
                                  have p3754_1 := h3754c.2.1
                                  have p3754_2 := h3754c.2.2.1
                                  have p3754_3 := h3754c.2.2.2
                                  linarith only [h1951, hlam, p3754_0]
                                · have p3754_0 := h3754c.1
                                  have p3754_1 := h3754c.2.1
                                  have p3754_2 := h3754c.2.2.1
                                  have p3754_3 := h3754c.2.2.2
                                  linarith only [h2940, hlam, p3754_1]
                                · have p3754_0 := h3754c.1
                                  have p3754_1 := h3754c.2.1
                                  have p3754_2 := h3754c.2.2.1
                                  have p3754_3 := h3754c.2.2.2
                                  linarith only [h0, h3281, h3739, h3742, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3754_1]
                                · have p3754_0 := h3754c.1
                                  have p3754_1 := h3754c.2.1
                                  have p3754_2 := h3754c.2.2.1
                                  have p3754_3 := h3754c.2.2.2
                                  linarith only [h3281, h3739, hc01, hc13, hlam, hphi, p3754_1]
                                · have p3754_0 := h3754c.1
                                  have p3754_1 := h3754c.2.1
                                  have p3754_2 := h3754c.2.2.1
                                  have p3754_3 := h3754c.2.2.2
                                  linarith only [hlam, p3754_0]
                                · have p3754_0 := h3754c.1
                                  have p3754_1 := h3754c.2.1
                                  have p3754_2 := h3754c.2.2.1
                                  have p3754_3 := h3754c.2.2.2
                                  linarith only [h3281, hlam, p3754_0]
                                · have p3754_0 := h3754c.1
                                  have p3754_1 := h3754c.2.1
                                  have p3754_2 := h3754c.2.2.1
                                  have p3754_3 := h3754c.2.2.2
                                  linarith only [h3536, hlam, p3754_1]
                                · have p3754_0 := h3754c.1
                                  have p3754_1 := h3754c.2.1
                                  have p3754_2 := h3754c.2.2.1
                                  have p3754_3 := h3754c.2.2.2
                                  linarith only [h3280, h3281, h3739, h3741, h3742, h3751, h3753, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3754_1]
                                · have p3754_0 := h3754c.1
                                  have p3754_1 := h3754c.2.1
                                  have p3754_2 := h3754c.2.2.1
                                  have p3754_3 := h3754c.2.2.2
                                  linarith only [h3280, h3741, h3751, h3753, hc45, hlam, hphi, ht0b, ht5b, p3754_1, u0elo2]
                                · have p3754_0 := h3754c.1
                                  have p3754_1 := h3754c.2.1
                                  have p3754_2 := h3754c.2.2.1
                                  have p3754_3 := h3754c.2.2.2
                                  linarith only [h3281, h3739, h3742, hc02, hc34, hlam, hphi, ht23, p3754_1]
                                · have p3754_0 := h3754c.1
                                  have p3754_1 := h3754c.2.1
                                  have p3754_2 := h3754c.2.2.1
                                  have p3754_3 := h3754c.2.2.2
                                  linarith only [hlam, p3754_0]
                                · have p3754_0 := h3754c.1
                                  have p3754_1 := h3754c.2.1
                                  have p3754_2 := h3754c.2.2.1
                                  have p3754_3 := h3754c.2.2.2
                                  linarith only [h3637, hlam, p3754_1]
                                · have p3754_0 := h3754c.1
                                  have p3754_1 := h3754c.2.1
                                  have p3754_2 := h3754c.2.2.1
                                  have p3754_3 := h3754c.2.2.2
                                  rcases p3754_3 (m.d 0 1) (by simp) with h3769 | h3769
                                  · linarith only [h1951, h3769, hlam]
                                  · linarith only [h3280, h3769, hlam]
                                · have p3754_0 := h3754c.1
                                  have p3754_1 := h3754c.2.1
                                  have p3754_2 := h3754c.2.2.1
                                  have p3754_3 := h3754c.2.2.2
                                  linarith only [h3280, h3741, h3751, h3753, hc45, hlam, hphi, ht0b, ht5b, p3754_1, u0elo3]
                                · have p3754_0 := h3754c.1
                                  have p3754_1 := h3754c.2.1
                                  have p3754_2 := h3754c.2.2.1
                                  have p3754_3 := h3754c.2.2.2
                                  linarith only [h0, h3280, h3741, h3751, h3753, hc45, hlam, hphi, ht0b, ht5b, p3754_1, u0elo3]
                                · have p3754_0 := h3754c.1
                                  have p3754_1 := h3754c.2.1
                                  have p3754_2 := h3754c.2.2.1
                                  have p3754_3 := h3754c.2.2.2
                                  linarith only [h1951, h3280, h3741, h3751, h3753, hc45, hlam, hphi, ht0b, ht5b, p3754_1, u0elo3]
                                · have p3754_0 := h3754c.1
                                  have p3754_1 := h3754c.2.1
                                  have p3754_2 := h3754c.2.2.1
                                  have p3754_3 := h3754c.2.2.2
                                  linarith only [hlam, p3754_0]
                                · have p3754_0 := h3754c.1
                                  have p3754_1 := h3754c.2.1
                                  have p3754_2 := h3754c.2.2.1
                                  have p3754_3 := h3754c.2.2.2
                                  rcases p3754_3 (m.d 0 1) (by simp) with h3776 | h3776
                                  · linarith only [h2940, h3776, hlam]
                                  · linarith only [h3280, h3776, hlam]
                                · have p3754_0 := h3754c.1
                                  have p3754_1 := h3754c.2.1
                                  have p3754_2 := h3754c.2.2.1
                                  have p3754_3 := h3754c.2.2.2
                                  linarith only [h3280, hlam, p3754_0]
                                · have p3754_0 := h3754c.1
                                  have p3754_1 := h3754c.2.1
                                  have p3754_2 := h3754c.2.2.1
                                  have p3754_3 := h3754c.2.2.2
                                  linarith only [h3636, hlam, p3754_1]
                                · have p3754_0 := h3754c.1
                                  have p3754_1 := h3754c.2.1
                                  have p3754_2 := h3754c.2.2.1
                                  have p3754_3 := h3754c.2.2.2
                                  linarith only [h3737, hlam, p3754_0]
                                · have p3754_0 := h3754c.1
                                  have p3754_1 := h3754c.2.1
                                  have p3754_2 := h3754c.2.2.1
                                  have p3754_3 := h3754c.2.2.2
                                  linarith only [h3738, hlam, p3754_1]
                                · have p3754_0 := h3754c.1
                                  have p3754_1 := h3754c.2.1
                                  have p3754_2 := h3754c.2.2.1
                                  have p3754_3 := h3754c.2.2.2
                                  linarith only [hlam, p3754_0]
                              · linarith only [h3742, h3753, hc13, hlam, hphi, ht34, ht45, u5elo4]
                            · linarith only [h2940, h3280, h3536, h3738, h3752, hc15, hlam, hphi, u5elo0]
                          · linarith only [h0, h3280, h3281, h3741, h3751, hc25, hlam, hphi, u5elo3]
                      · linarith only [h0, h3280, h3281, h3737, h3739, h3741, h3748, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                  · linarith only [h3740, h3741, hc24, hlam, hphi, ht45, u5elo2]
                · linarith only [h0, h3281, h3739, h3740, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3790 | h3790
                · linarith only [h0, h3280, h3536, h3739, h3790, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3792 | h3792
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3793 | h3793
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3794 | h3794
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3795 | h3795
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3796 | h3796
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3797 | h3797
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3798 | h3798
                              · rcases h0bigk with h3799c | h3799c | h3799c | h3799c | h3799c | h3799c | h3799c | h3799c | h3799c | h3799c | h3799c | h3799c | h3799c | h3799c | h3799c | h3799c | h3799c | h3799c | h3799c | h3799c | h3799c | h3799c | h3799c | h3799c | h3799c
                                · have p3799_0 := h3799c.1
                                  have p3799_1 := h3799c.2.1
                                  have p3799_2 := h3799c.2.2.1
                                  have p3799_3 := h3799c.2.2.2
                                  linarith only [hlam, p3799_0]
                                · have p3799_0 := h3799c.1
                                  have p3799_1 := h3799c.2.1
                                  have p3799_2 := h3799c.2.2.1
                                  have p3799_3 := h3799c.2.2.2
                                  linarith only [h0, hlam, p3799_1]
                                · have p3799_0 := h3799c.1
                                  have p3799_1 := h3799c.2.1
                                  have p3799_2 := h3799c.2.2.1
                                  have p3799_3 := h3799c.2.2.2
                                  linarith only [h1951, hlam, p3799_0]
                                · have p3799_0 := h3799c.1
                                  have p3799_1 := h3799c.2.1
                                  have p3799_2 := h3799c.2.2.1
                                  have p3799_3 := h3799c.2.2.2
                                  linarith only [h2940, hlam, p3799_1]
                                · have p3799_0 := h3799c.1
                                  have p3799_1 := h3799c.2.1
                                  have p3799_2 := h3799c.2.2.1
                                  have p3799_3 := h3799c.2.2.2
                                  linarith only [h0, h3790, hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p3799_1]
                                · have p3799_0 := h3799c.1
                                  have p3799_1 := h3799c.2.1
                                  have p3799_2 := h3799c.2.2.1
                                  have p3799_3 := h3799c.2.2.2
                                  linarith only [h0, h3790, hc01, hc24, hlam, hphi, ht12, p3799_1]
                                · have p3799_0 := h3799c.1
                                  have p3799_1 := h3799c.2.1
                                  have p3799_2 := h3799c.2.2.1
                                  have p3799_3 := h3799c.2.2.2
                                  linarith only [hlam, p3799_0]
                                · have p3799_0 := h3799c.1
                                  have p3799_1 := h3799c.2.1
                                  have p3799_2 := h3799c.2.2.1
                                  have p3799_3 := h3799c.2.2.2
                                  linarith only [h3281, hlam, p3799_0]
                                · have p3799_0 := h3799c.1
                                  have p3799_1 := h3799c.2.1
                                  have p3799_2 := h3799c.2.2.1
                                  have p3799_3 := h3799c.2.2.2
                                  linarith only [h3536, hlam, p3799_1]
                                · have p3799_0 := h3799c.1
                                  have p3799_1 := h3799c.2.1
                                  have p3799_2 := h3799c.2.2.1
                                  have p3799_3 := h3799c.2.2.2
                                  linarith only [h3280, h3281, h3637, h3739, h3792, h3793, h3796, h3798, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3799_1]
                                · have p3799_0 := h3799c.1
                                  have p3799_1 := h3799c.2.1
                                  have p3799_2 := h3799c.2.2.1
                                  have p3799_3 := h3799c.2.2.2
                                  linarith only [h3280, h3637, h3739, h3792, h3793, h3796, h3798, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3799_1]
                                · have p3799_0 := h3799c.1
                                  have p3799_1 := h3799c.2.1
                                  have p3799_2 := h3799c.2.2.1
                                  have p3799_3 := h3799c.2.2.2
                                  linarith only [h3637, h3739, h3793, hc02, hc23, hlam, hphi, p3799_1]
                                · have p3799_0 := h3799c.1
                                  have p3799_1 := h3799c.2.1
                                  have p3799_2 := h3799c.2.2.1
                                  have p3799_3 := h3799c.2.2.2
                                  linarith only [hlam, p3799_0]
                                · have p3799_0 := h3799c.1
                                  have p3799_1 := h3799c.2.1
                                  have p3799_2 := h3799c.2.2.1
                                  have p3799_3 := h3799c.2.2.2
                                  linarith only [h3637, hlam, p3799_1]
                                · have p3799_0 := h3799c.1
                                  have p3799_1 := h3799c.2.1
                                  have p3799_2 := h3799c.2.2.1
                                  have p3799_3 := h3799c.2.2.2
                                  linarith only [h3280, h3637, h3739, h3792, h3793, h3796, h3798, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3799_1]
                                · have p3799_0 := h3799c.1
                                  have p3799_1 := h3799c.2.1
                                  have p3799_2 := h3799c.2.2.1
                                  have p3799_3 := h3799c.2.2.2
                                  linarith only [h3280, h3637, h3739, h3792, h3793, h3796, h3798, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3799_1]
                                · have p3799_0 := h3799c.1
                                  have p3799_1 := h3799c.2.1
                                  have p3799_2 := h3799c.2.2.1
                                  have p3799_3 := h3799c.2.2.2
                                  linarith only [h0, h3280, h3637, h3739, h3792, h3793, h3796, h3798, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3799_1]
                                · have p3799_0 := h3799c.1
                                  have p3799_1 := h3799c.2.1
                                  have p3799_2 := h3799c.2.2.1
                                  have p3799_3 := h3799c.2.2.2
                                  linarith only [h1951, h3280, h3637, h3739, h3792, h3793, h3796, h3798, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3799_1]
                                · have p3799_0 := h3799c.1
                                  have p3799_1 := h3799c.2.1
                                  have p3799_2 := h3799c.2.2.1
                                  have p3799_3 := h3799c.2.2.2
                                  linarith only [hlam, p3799_0]
                                · have p3799_0 := h3799c.1
                                  have p3799_1 := h3799c.2.1
                                  have p3799_2 := h3799c.2.2.1
                                  have p3799_3 := h3799c.2.2.2
                                  rcases p3799_3 (m.d 0 1) (by simp) with h3819 | h3819
                                  · linarith only [h2940, h3819, hlam]
                                  · linarith only [h3280, h3819, hlam]
                                · have p3799_0 := h3799c.1
                                  have p3799_1 := h3799c.2.1
                                  have p3799_2 := h3799c.2.2.1
                                  have p3799_3 := h3799c.2.2.2
                                  linarith only [h3280, hlam, p3799_0]
                                · have p3799_0 := h3799c.1
                                  have p3799_1 := h3799c.2.1
                                  have p3799_2 := h3799c.2.2.1
                                  have p3799_3 := h3799c.2.2.2
                                  linarith only [h3636, hlam, p3799_1]
                                · have p3799_0 := h3799c.1
                                  have p3799_1 := h3799c.2.1
                                  have p3799_2 := h3799c.2.2.1
                                  have p3799_3 := h3799c.2.2.2
                                  linarith only [h3737, hlam, p3799_0]
                                · have p3799_0 := h3799c.1
                                  have p3799_1 := h3799c.2.1
                                  have p3799_2 := h3799c.2.2.1
                                  have p3799_3 := h3799c.2.2.2
                                  linarith only [h3738, hlam, p3799_1]
                                · have p3799_0 := h3799c.1
                                  have p3799_1 := h3799c.2.1
                                  have p3799_2 := h3799c.2.2.1
                                  have p3799_3 := h3799c.2.2.2
                                  linarith only [hlam, p3799_0]
                              · linarith only [h2940, h3280, h3637, h3798, hc15, hlam, hphi, u5elo4]
                            · linarith only [h0, h3280, h3738, h3790, h3792, h3796, h3797, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                          · linarith only [h0, h3280, h3281, h3637, h3739, h3792, h3793, h3796, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h3739, h3793, h3795, hlam]
                      · linarith only [h0, h3281, h3637, h3793, h3794, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3832 | h3832
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3833 | h3833
                        · linarith only [h0, h3739, h3793, h3833, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h3280, h3739, h3792, h3833, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h0, h3280, h3739, h3792, h3832, hc25, hlam, hphi, u5elo3]
                  · linarith only [h0, h3280, h3792, hc15, hlam, hphi, u5elo2]
            · linarith only [h2940, h3280, h3738, hc15, hlam, hphi, u5elo4]
          · linarith only [h1951, h3280, h3737, hc15, hlam, hphi, u5elo3]
      · linarith only [h0, h3280, h3636, hc15, hlam, hphi, u5elo2]

end R2N4
