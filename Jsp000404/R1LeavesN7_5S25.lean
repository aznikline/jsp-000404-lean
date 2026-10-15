import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10516000 in
set_option maxHeartbeats 10516000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s16_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg9935 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11282 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11844 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h15274 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h9935 := hg9935
  have h11282 := hg11282
  rcases m.htr 0 2 5 (by decide) (by decide) with h15275 | h15275
  · rcases m.htr 0 3 4 (by decide) (by decide) with h15276 | h15276
    · rcases m.htr 0 3 5 (by decide) (by decide) with h15277 | h15277
      · rcases m.htr 0 4 5 (by decide) (by decide) with h15278 | h15278
        · rcases m.htr 1 2 3 (by decide) (by decide) with h15279 | h15279
          · rcases m.htr 1 2 4 (by decide) (by decide) with h15280 | h15280
            · rcases m.htr 1 2 5 (by decide) (by decide) with h15281 | h15281
              · rcases m.htr 1 3 4 (by decide) (by decide) with h15282 | h15282
                · rcases m.htr 1 3 5 (by decide) (by decide) with h15283 | h15283
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h15284 | h15284
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15285 | h15285
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15286 | h15286
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h15287 | h15287
                          · linarith only [h11844, h15274, h15279, h15287, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h11844, h15274, h15278, h15279, h15287, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h11844, h15277, h15286, hlam]
                      · linarith only [h11844, h15276, h15285, hlam]
                    · linarith only [h15274, h15278, h15284, h9935, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h11844, h15274, h15277, h15278, h15279, h15283, h6310, hc01, hc12, hlam, hphi]
                · linarith only [h11844, h15274, h15276, h15279, h15282, hlam]
              · linarith only [h11844, h15275, h15279, h15281, hlam]
            · linarith only [h11844, h15279, h15280, hc02, hc24, hlam, hphi]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h15297 | h15297
            · rcases m.htr 1 2 5 (by decide) (by decide) with h15298 | h15298
              · rcases m.htr 1 3 4 (by decide) (by decide) with h15299 | h15299
                · rcases m.htr 1 3 5 (by decide) (by decide) with h15300 | h15300
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h15301 | h15301
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15302 | h15302
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15303 | h15303
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h15304 | h15304
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h15305 | h15305
                            · rcases h0bigk with h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c
                              · have p15306_0 := h15306c.1
                                have p15306_1 := h15306c.2.1
                                have p15306_2 := h15306c.2.2.1
                                have p15306_3 := h15306c.2.2.2
                                linarith only [hlam, p15306_0]
                              · have p15306_0 := h15306c.1
                                have p15306_1 := h15306c.2.1
                                have p15306_2 := h15306c.2.2.1
                                have p15306_3 := h15306c.2.2.2
                                linarith only [h0, hlam, p15306_1]
                              · have p15306_0 := h15306c.1
                                have p15306_1 := h15306c.2.1
                                have p15306_2 := h15306c.2.2.1
                                have p15306_3 := h15306c.2.2.2
                                linarith only [h6310, hlam, p15306_0]
                              · have p15306_0 := h15306c.1
                                have p15306_1 := h15306c.2.1
                                have p15306_2 := h15306c.2.2.1
                                have p15306_3 := h15306c.2.2.2
                                linarith only [h9935, hlam, p15306_1]
                              · have p15306_0 := h15306c.1
                                have p15306_1 := h15306c.2.1
                                have p15306_2 := h15306c.2.2.1
                                have p15306_3 := h15306c.2.2.2
                                linarith only [h11282, hlam, p15306_1]
                              · have p15306_0 := h15306c.1
                                have p15306_1 := h15306c.2.1
                                have p15306_2 := h15306c.2.2.1
                                have p15306_3 := h15306c.2.2.2
                                linarith only [h0, h15279, hc01, hc23, hlam, hphi, ht12, p15306_1]
                              · have p15306_0 := h15306c.1
                                have p15306_1 := h15306c.2.1
                                have p15306_2 := h15306c.2.2.1
                                have p15306_3 := h15306c.2.2.2
                                linarith only [hlam, p15306_0]
                              · have p15306_0 := h15306c.1
                                have p15306_1 := h15306c.2.1
                                have p15306_2 := h15306c.2.2.1
                                have p15306_3 := h15306c.2.2.2
                                linarith only [h11844, hlam, p15306_0]
                              · have p15306_0 := h15306c.1
                                have p15306_1 := h15306c.2.1
                                have p15306_2 := h15306c.2.2.1
                                have p15306_3 := h15306c.2.2.2
                                linarith only [h0, h15279, h9935, hc01, hc23, hlam, hphi, ht12, p15306_1]
                              · have p15306_0 := h15306c.1
                                have p15306_1 := h15306c.2.1
                                have p15306_2 := h15306c.2.2.1
                                have p15306_3 := h15306c.2.2.2
                                linarith only [h0, h11282, h15279, hc01, hc23, hlam, hphi, ht12, p15306_1]
                              · have p15306_0 := h15306c.1
                                have p15306_1 := h15306c.2.1
                                have p15306_2 := h15306c.2.2.1
                                have p15306_3 := h15306c.2.2.2
                                rcases p15306_3 (m.d 0 1) (by simp) with h15317 | h15317
                                · linarith only [h15317, h6310, hlam]
                                · rcases p15306_3 (m.d 0 2) (by simp) with h15319 | h15319
                                  · linarith only [h11844, h15319, hlam]
                                  · linarith only [h0, h15319, hlam]
                              · have p15306_0 := h15306c.1
                                have p15306_1 := h15306c.2.1
                                have p15306_2 := h15306c.2.2.1
                                have p15306_3 := h15306c.2.2.2
                                linarith only [h15274, hc24, hlam, hphi, ht0b, ht45, ht5b, p15306_1, u0elo2]
                              · have p15306_0 := h15306c.1
                                have p15306_1 := h15306c.2.1
                                have p15306_2 := h15306c.2.2.1
                                have p15306_3 := h15306c.2.2.2
                                linarith only [hlam, p15306_0]
                              · have p15306_0 := h15306c.1
                                have p15306_1 := h15306c.2.1
                                have p15306_2 := h15306c.2.2.1
                                have p15306_3 := h15306c.2.2.2
                                linarith only [h15274, h15302, h15305, hc45, hlam, hphi, ht0b, ht5b, p15306_1, u0elo2]
                              · have p15306_0 := h15306c.1
                                have p15306_1 := h15306c.2.1
                                have p15306_2 := h15306c.2.2.1
                                have p15306_3 := h15306c.2.2.2
                                rcases p15306_3 (m.d 0 1) (by simp) with h15325 | h15325
                                · linarith only [h15325, h6310, hlam]
                                · rcases p15306_3 (m.d 0 2) (by simp) with h15327 | h15327
                                  · linarith only [h11844, h15327, hlam]
                                  · linarith only [h15275, h15327, hlam]
                              · have p15306_0 := h15306c.1
                                have p15306_1 := h15306c.2.1
                                have p15306_2 := h15306c.2.2.1
                                have p15306_3 := h15306c.2.2.2
                                linarith only [h15279, h15297, h9935, hc01, hc23, hlam, hphi, ht12, p15306_1]
                              · have p15306_0 := h15306c.1
                                have p15306_1 := h15306c.2.1
                                have p15306_2 := h15306c.2.2.1
                                have p15306_3 := h15306c.2.2.2
                                linarith only [h15274, hlam, p15306_0]
                              · have p15306_0 := h15306c.1
                                have p15306_1 := h15306c.2.1
                                have p15306_2 := h15306c.2.2.1
                                have p15306_3 := h15306c.2.2.2
                                linarith only [h15276, hlam, p15306_0]
                              · have p15306_0 := h15306c.1
                                have p15306_1 := h15306c.2.1
                                have p15306_2 := h15306c.2.2.1
                                have p15306_3 := h15306c.2.2.2
                                linarith only [hlam, p15306_0]
                              · have p15306_0 := h15306c.1
                                have p15306_1 := h15306c.2.1
                                have p15306_2 := h15306c.2.2.1
                                have p15306_3 := h15306c.2.2.2
                                linarith only [h0, h11282, h15274, h15279, hc01, hc23, hlam, hphi, ht12, p15306_1]
                              · have p15306_0 := h15306c.1
                                have p15306_1 := h15306c.2.1
                                have p15306_2 := h15306c.2.2.1
                                have p15306_3 := h15306c.2.2.2
                                linarith only [h11282, h15279, h15297, h15301, hc01, hc23, hlam, hphi, ht12, p15306_1]
                              · have p15306_0 := h15306c.1
                                have p15306_1 := h15306c.2.1
                                have p15306_2 := h15306c.2.2.1
                                have p15306_3 := h15306c.2.2.2
                                linarith only [h15275, hlam, p15306_1]
                              · have p15306_0 := h15306c.1
                                have p15306_1 := h15306c.2.1
                                have p15306_2 := h15306c.2.2.1
                                have p15306_3 := h15306c.2.2.2
                                linarith only [h15277, hlam, p15306_0]
                              · have p15306_0 := h15306c.1
                                have p15306_1 := h15306c.2.1
                                have p15306_2 := h15306c.2.2.1
                                have p15306_3 := h15306c.2.2.2
                                linarith only [h15278, hlam, p15306_1]
                              · have p15306_0 := h15306c.1
                                have p15306_1 := h15306c.2.1
                                have p15306_2 := h15306c.2.2.1
                                have p15306_3 := h15306c.2.2.2
                                linarith only [hlam, p15306_0]
                            · linarith only [h0, h15274, h15279, h15304, h15305, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h15341 | h15341
                            · linarith only [h15276, h15304, h15341, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · rcases h0bigk with h15343c | h15343c | h15343c | h15343c | h15343c | h15343c | h15343c | h15343c | h15343c | h15343c | h15343c | h15343c | h15343c | h15343c | h15343c | h15343c | h15343c | h15343c | h15343c | h15343c | h15343c | h15343c | h15343c | h15343c | h15343c
                              · have p15343_0 := h15343c.1
                                have p15343_1 := h15343c.2.1
                                have p15343_2 := h15343c.2.2.1
                                have p15343_3 := h15343c.2.2.2
                                linarith only [hlam, p15343_0]
                              · have p15343_0 := h15343c.1
                                have p15343_1 := h15343c.2.1
                                have p15343_2 := h15343c.2.2.1
                                have p15343_3 := h15343c.2.2.2
                                linarith only [h0, hlam, p15343_1]
                              · have p15343_0 := h15343c.1
                                have p15343_1 := h15343c.2.1
                                have p15343_2 := h15343c.2.2.1
                                have p15343_3 := h15343c.2.2.2
                                linarith only [h6310, hlam, p15343_0]
                              · have p15343_0 := h15343c.1
                                have p15343_1 := h15343c.2.1
                                have p15343_2 := h15343c.2.2.1
                                have p15343_3 := h15343c.2.2.2
                                linarith only [h9935, hlam, p15343_1]
                              · have p15343_0 := h15343c.1
                                have p15343_1 := h15343c.2.1
                                have p15343_2 := h15343c.2.2.1
                                have p15343_3 := h15343c.2.2.2
                                linarith only [h11282, hlam, p15343_1]
                              · have p15343_0 := h15343c.1
                                have p15343_1 := h15343c.2.1
                                have p15343_2 := h15343c.2.2.1
                                have p15343_3 := h15343c.2.2.2
                                linarith only [h0, h15279, hc01, hc23, hlam, hphi, ht12, p15343_1]
                              · have p15343_0 := h15343c.1
                                have p15343_1 := h15343c.2.1
                                have p15343_2 := h15343c.2.2.1
                                have p15343_3 := h15343c.2.2.2
                                linarith only [hlam, p15343_0]
                              · have p15343_0 := h15343c.1
                                have p15343_1 := h15343c.2.1
                                have p15343_2 := h15343c.2.2.1
                                have p15343_3 := h15343c.2.2.2
                                linarith only [h11844, hlam, p15343_0]
                              · have p15343_0 := h15343c.1
                                have p15343_1 := h15343c.2.1
                                have p15343_2 := h15343c.2.2.1
                                have p15343_3 := h15343c.2.2.2
                                linarith only [h0, h15278, h15279, h15302, h15304, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p15343_1]
                              · have p15343_0 := h15343c.1
                                have p15343_1 := h15343c.2.1
                                have p15343_2 := h15343c.2.2.1
                                have p15343_3 := h15343c.2.2.2
                                linarith only [h0, h11282, h15279, hc01, hc23, hlam, hphi, ht12, p15343_1]
                              · have p15343_0 := h15343c.1
                                have p15343_1 := h15343c.2.1
                                have p15343_2 := h15343c.2.2.1
                                have p15343_3 := h15343c.2.2.2
                                rcases p15343_3 (m.d 0 1) (by simp) with h15354 | h15354
                                · linarith only [h15354, h6310, hlam]
                                · rcases p15343_3 (m.d 0 2) (by simp) with h15356 | h15356
                                  · linarith only [h11844, h15356, hlam]
                                  · linarith only [h0, h15356, hlam]
                              · have p15343_0 := h15343c.1
                                have p15343_1 := h15343c.2.1
                                have p15343_2 := h15343c.2.2.1
                                have p15343_3 := h15343c.2.2.2
                                linarith only [h15274, h15302, hc34, hlam, hphi, ht0b, ht45, ht5b, p15343_1, u0elo2]
                              · have p15343_0 := h15343c.1
                                have p15343_1 := h15343c.2.1
                                have p15343_2 := h15343c.2.2.1
                                have p15343_3 := h15343c.2.2.2
                                linarith only [hlam, p15343_0]
                              · have p15343_0 := h15343c.1
                                have p15343_1 := h15343c.2.1
                                have p15343_2 := h15343c.2.2.1
                                have p15343_3 := h15343c.2.2.2
                                linarith only [h15278, h15302, h15304, hc34, hlam, hphi, ht0b, ht45, ht5b, p15343_1, u0elo2]
                              · have p15343_0 := h15343c.1
                                have p15343_1 := h15343c.2.1
                                have p15343_2 := h15343c.2.2.1
                                have p15343_3 := h15343c.2.2.2
                                linarith only [h15278, h15302, h15304, hc34, hlam, hphi, ht0b, ht45, ht5b, p15343_1, u0elo2]
                              · have p15343_0 := h15343c.1
                                have p15343_1 := h15343c.2.1
                                have p15343_2 := h15343c.2.2.1
                                have p15343_3 := h15343c.2.2.2
                                linarith only [h0, h15274, h15279, hc01, hc23, hlam, hphi, ht12, p15343_1]
                              · have p15343_0 := h15343c.1
                                have p15343_1 := h15343c.2.1
                                have p15343_2 := h15343c.2.2.1
                                have p15343_3 := h15343c.2.2.2
                                linarith only [h15274, hlam, p15343_0]
                              · have p15343_0 := h15343c.1
                                have p15343_1 := h15343c.2.1
                                have p15343_2 := h15343c.2.2.1
                                have p15343_3 := h15343c.2.2.2
                                linarith only [h15276, hlam, p15343_0]
                              · have p15343_0 := h15343c.1
                                have p15343_1 := h15343c.2.1
                                have p15343_2 := h15343c.2.2.1
                                have p15343_3 := h15343c.2.2.2
                                linarith only [hlam, p15343_0]
                              · have p15343_0 := h15343c.1
                                have p15343_1 := h15343c.2.1
                                have p15343_2 := h15343c.2.2.1
                                have p15343_3 := h15343c.2.2.2
                                linarith only [h0, h11282, h15274, h15279, hc01, hc23, hlam, hphi, ht12, p15343_1]
                              · have p15343_0 := h15343c.1
                                have p15343_1 := h15343c.2.1
                                have p15343_2 := h15343c.2.2.1
                                have p15343_3 := h15343c.2.2.2
                                linarith only [h0, h15275, h15279, hc01, hc23, hlam, hphi, ht12, p15343_1]
                              · have p15343_0 := h15343c.1
                                have p15343_1 := h15343c.2.1
                                have p15343_2 := h15343c.2.2.1
                                have p15343_3 := h15343c.2.2.2
                                linarith only [h15275, hlam, p15343_1]
                              · have p15343_0 := h15343c.1
                                have p15343_1 := h15343c.2.1
                                have p15343_2 := h15343c.2.2.1
                                have p15343_3 := h15343c.2.2.2
                                linarith only [h15277, hlam, p15343_0]
                              · have p15343_0 := h15343c.1
                                have p15343_1 := h15343c.2.1
                                have p15343_2 := h15343c.2.2.1
                                have p15343_3 := h15343c.2.2.2
                                linarith only [h15278, hlam, p15343_1]
                              · have p15343_0 := h15343c.1
                                have p15343_1 := h15343c.2.1
                                have p15343_2 := h15343c.2.2.1
                                have p15343_3 := h15343c.2.2.2
                                linarith only [hlam, p15343_0]
                        · linarith only [h0, h15279, h15303, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h11282, h15279, h15297, h15301, h15302, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h15274, h15278, h15301, h9935, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h15277, h15300, h6310, hlam]
                · linarith only [h15276, h15299, h6310, hlam]
              · linarith only [h0, h15275, h15298, hlam]
            · linarith only [h0, h15274, h15297, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h15380 | h15380
          · rcases m.htr 1 2 4 (by decide) (by decide) with h15381 | h15381
            · rcases m.htr 1 2 5 (by decide) (by decide) with h15382 | h15382
              · rcases m.htr 1 3 4 (by decide) (by decide) with h15383 | h15383
                · rcases m.htr 1 3 5 (by decide) (by decide) with h15384 | h15384
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h15385 | h15385
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15386 | h15386
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15387 | h15387
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h15388 | h15388
                          · linarith only [h11844, h15274, h15278, h15380, h15388, h9935, hc01, hc12, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h15390 | h15390
                            · linarith only [h11844, h15275, h15278, h15380, h15386, h15388, h15390, h9935, hc01, hc12, hlam, hphi]
                            · rcases h0bigk with h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [hlam, p15392_0]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h0, hlam, p15392_1]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h6310, hlam, p15392_0]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h9935, hlam, p15392_1]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h11282, hlam, p15392_1]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h11844, h15380, hc01, hc12, hlam, hphi, p15392_1]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [hlam, p15392_0]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h11844, hlam, p15392_0]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h11844, h15380, h9935, hc01, hc12, hlam, hphi, p15392_1]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h11844, h15380, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p15392_1]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h11844, h15380, hc01, hc12, hlam, hphi, p15392_1]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h11844, h15275, h15380, h15388, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p15392_1]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [hlam, p15392_0]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h11844, h15380, h9935, hc01, hc12, hlam, hphi, p15392_1]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h11282, h11844, h15380, hc01, hc12, hlam, hphi, p15392_1]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h15278, h15383, h15385, hc01, hc13, hlam, hphi, p15392_1]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h15274, hlam, p15392_0]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h15276, hlam, p15392_0]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [hlam, p15392_0]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h15278, hlam, p15392_0]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h11844, h15275, h15380, hc01, hc12, hlam, hphi, p15392_1]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h15275, hlam, p15392_1]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h15277, hlam, p15392_0]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h11844, h15275, h15380, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p15392_1]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [hlam, p15392_0]
                        · linarith only [h11844, h15277, h15387, hlam]
                      · linarith only [h11844, h15276, h15386, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15420 | h15420
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15421 | h15421
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h15422 | h15422
                          · linarith only [h15274, h15385, h15422, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h15424 | h15424
                            · linarith only [h15385, h15420, h15424, h9935, hc01, hc24, hlam, hphi, ht12]
                            · rcases h0bigk with h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [hlam, p15426_0]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h0, hlam, p15426_1]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h6310, hlam, p15426_0]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h9935, hlam, p15426_1]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h11282, hlam, p15426_1]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h11844, h15380, hc01, hc12, hlam, hphi, p15426_1]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [hlam, p15426_0]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h11844, hlam, p15426_0]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h11844, h15380, h9935, hc01, hc12, hlam, hphi, p15426_1]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h11844, h15380, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p15426_1]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h11844, h15380, hc01, hc12, hlam, hphi, p15426_1]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h11844, h15275, h15380, h15422, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p15426_1]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [hlam, p15426_0]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h11844, h15380, h9935, hc01, hc12, hlam, hphi, p15426_1]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h11282, h11844, h15380, hc01, hc12, hlam, hphi, p15426_1]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h15385, h9935, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p15426_1]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h15274, hlam, p15426_0]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h15276, hlam, p15426_0]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [hlam, p15426_0]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h15278, hlam, p15426_0]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h11844, h15275, h15380, hc01, hc12, hlam, hphi, p15426_1]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h15275, hlam, p15426_1]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h15277, hlam, p15426_0]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h11844, h15275, h15380, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p15426_1]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [hlam, p15426_0]
                        · linarith only [h11844, h15277, h15421, hlam]
                      · linarith only [h11844, h15276, h15420, hlam]
                  · linarith only [h11844, h15275, h15277, h15384, h6310, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h11844, h15274, h15276, h15380, h15383, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
              · linarith only [h11844, h15274, h15380, h15382, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h11844, h15274, h15380, h15381, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h15458 | h15458
            · rcases m.htr 1 2 5 (by decide) (by decide) with h15459 | h15459
              · rcases m.htr 1 3 4 (by decide) (by decide) with h15460 | h15460
                · rcases m.htr 1 3 5 (by decide) (by decide) with h15461 | h15461
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h15462 | h15462
                    · linarith only [h15278, h15380, h15458, h15462, h9935, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15464 | h15464
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15465 | h15465
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h15466 | h15466
                          · linarith only [h15274, h15462, h15466, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h15468 | h15468
                            · linarith only [h15462, h15468, h9935, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases h0bigk with h15470c | h15470c | h15470c | h15470c | h15470c | h15470c | h15470c | h15470c | h15470c | h15470c | h15470c | h15470c | h15470c | h15470c | h15470c | h15470c | h15470c | h15470c | h15470c | h15470c | h15470c | h15470c | h15470c | h15470c | h15470c
                              · have p15470_0 := h15470c.1
                                have p15470_1 := h15470c.2.1
                                have p15470_2 := h15470c.2.2.1
                                have p15470_3 := h15470c.2.2.2
                                linarith only [hlam, p15470_0]
                              · have p15470_0 := h15470c.1
                                have p15470_1 := h15470c.2.1
                                have p15470_2 := h15470c.2.2.1
                                have p15470_3 := h15470c.2.2.2
                                linarith only [h0, hlam, p15470_1]
                              · have p15470_0 := h15470c.1
                                have p15470_1 := h15470c.2.1
                                have p15470_2 := h15470c.2.2.1
                                have p15470_3 := h15470c.2.2.2
                                linarith only [h6310, hlam, p15470_0]
                              · have p15470_0 := h15470c.1
                                have p15470_1 := h15470c.2.1
                                have p15470_2 := h15470c.2.2.1
                                have p15470_3 := h15470c.2.2.2
                                linarith only [h9935, hlam, p15470_1]
                              · have p15470_0 := h15470c.1
                                have p15470_1 := h15470c.2.1
                                have p15470_2 := h15470c.2.2.1
                                have p15470_3 := h15470c.2.2.2
                                linarith only [h11282, hlam, p15470_1]
                              · have p15470_0 := h15470c.1
                                have p15470_1 := h15470c.2.1
                                have p15470_2 := h15470c.2.2.1
                                have p15470_3 := h15470c.2.2.2
                                linarith only [h0, h15380, hc01, hc23, hlam, hphi, ht12, p15470_1]
                              · have p15470_0 := h15470c.1
                                have p15470_1 := h15470c.2.1
                                have p15470_2 := h15470c.2.2.1
                                have p15470_3 := h15470c.2.2.2
                                linarith only [hlam, p15470_0]
                              · have p15470_0 := h15470c.1
                                have p15470_1 := h15470c.2.1
                                have p15470_2 := h15470c.2.2.1
                                have p15470_3 := h15470c.2.2.2
                                linarith only [h11844, hlam, p15470_0]
                              · have p15470_0 := h15470c.1
                                have p15470_1 := h15470c.2.1
                                have p15470_2 := h15470c.2.2.1
                                have p15470_3 := h15470c.2.2.2
                                linarith only [h0, h15380, h9935, hc01, hc23, hlam, hphi, ht12, p15470_1]
                              · have p15470_0 := h15470c.1
                                have p15470_1 := h15470c.2.1
                                have p15470_2 := h15470c.2.2.1
                                have p15470_3 := h15470c.2.2.2
                                linarith only [h0, h11282, h15380, hc01, hc23, hlam, hphi, ht12, p15470_1]
                              · have p15470_0 := h15470c.1
                                have p15470_1 := h15470c.2.1
                                have p15470_2 := h15470c.2.2.1
                                have p15470_3 := h15470c.2.2.2
                                rcases p15470_3 (m.d 0 1) (by simp) with h15481 | h15481
                                · linarith only [h15481, h6310, hlam]
                                · rcases p15470_3 (m.d 0 2) (by simp) with h15483 | h15483
                                  · linarith only [h11844, h15483, hlam]
                                  · linarith only [h0, h15483, hlam]
                              · have p15470_0 := h15470c.1
                                have p15470_1 := h15470c.2.1
                                have p15470_2 := h15470c.2.2.1
                                have p15470_3 := h15470c.2.2.2
                                linarith only [h15275, hc25, hlam, hphi, ht0b, ht5b, p15470_1, u0elo2]
                              · have p15470_0 := h15470c.1
                                have p15470_1 := h15470c.2.1
                                have p15470_2 := h15470c.2.2.1
                                have p15470_3 := h15470c.2.2.2
                                linarith only [hlam, p15470_0]
                              · have p15470_0 := h15470c.1
                                have p15470_1 := h15470c.2.1
                                have p15470_2 := h15470c.2.2.1
                                have p15470_3 := h15470c.2.2.2
                                rcases p15470_3 (m.d 0 1) (by simp) with h15488 | h15488
                                · linarith only [h15488, h6310, hlam]
                                · rcases p15470_3 (m.d 0 2) (by simp) with h15490 | h15490
                                  · linarith only [h11844, h15490, hlam]
                                  · linarith only [h15274, h15490, hlam]
                              · have p15470_0 := h15470c.1
                                have p15470_1 := h15470c.2.1
                                have p15470_2 := h15470c.2.2.1
                                have p15470_3 := h15470c.2.2.2
                                rcases p15470_3 (m.d 0 1) (by simp) with h15493 | h15493
                                · linarith only [h15493, h6310, hlam]
                                · rcases p15470_3 (m.d 0 2) (by simp) with h15495 | h15495
                                  · linarith only [h11844, h15495, hlam]
                                  · linarith only [h15275, h15495, hlam]
                              · have p15470_0 := h15470c.1
                                have p15470_1 := h15470c.2.1
                                have p15470_2 := h15470c.2.2.1
                                have p15470_3 := h15470c.2.2.2
                                linarith only [h15462, h9935, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p15470_1]
                              · have p15470_0 := h15470c.1
                                have p15470_1 := h15470c.2.1
                                have p15470_2 := h15470c.2.2.1
                                have p15470_3 := h15470c.2.2.2
                                linarith only [h15274, hlam, p15470_0]
                              · have p15470_0 := h15470c.1
                                have p15470_1 := h15470c.2.1
                                have p15470_2 := h15470c.2.2.1
                                have p15470_3 := h15470c.2.2.2
                                linarith only [h15276, hlam, p15470_0]
                              · have p15470_0 := h15470c.1
                                have p15470_1 := h15470c.2.1
                                have p15470_2 := h15470c.2.2.1
                                have p15470_3 := h15470c.2.2.2
                                linarith only [hlam, p15470_0]
                              · have p15470_0 := h15470c.1
                                have p15470_1 := h15470c.2.1
                                have p15470_2 := h15470c.2.2.1
                                have p15470_3 := h15470c.2.2.2
                                linarith only [h15278, hlam, p15470_0]
                              · have p15470_0 := h15470c.1
                                have p15470_1 := h15470c.2.1
                                have p15470_2 := h15470c.2.2.1
                                have p15470_3 := h15470c.2.2.2
                                linarith only [h0, h15275, h15380, hc01, hc23, hlam, hphi, ht12, p15470_1]
                              · have p15470_0 := h15470c.1
                                have p15470_1 := h15470c.2.1
                                have p15470_2 := h15470c.2.2.1
                                have p15470_3 := h15470c.2.2.2
                                linarith only [h15275, hlam, p15470_1]
                              · have p15470_0 := h15470c.1
                                have p15470_1 := h15470c.2.1
                                have p15470_2 := h15470c.2.2.1
                                have p15470_3 := h15470c.2.2.2
                                linarith only [h15277, hlam, p15470_0]
                              · have p15470_0 := h15470c.1
                                have p15470_1 := h15470c.2.1
                                have p15470_2 := h15470c.2.2.1
                                have p15470_3 := h15470c.2.2.2
                                linarith only [h0, h15275, h15380, h9935, hc01, hc23, hlam, hphi, ht12, p15470_1]
                              · have p15470_0 := h15470c.1
                                have p15470_1 := h15470c.2.1
                                have p15470_2 := h15470c.2.2.1
                                have p15470_3 := h15470c.2.2.2
                                linarith only [hlam, p15470_0]
                        · linarith only [h0, h15380, h15465, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h15380, h15459, h15462, h15464, h9935, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h11282, h15277, h15380, h15459, h15461, h6310, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h15274, h15276, h15380, h15460, hlam]
              · linarith only [h0, h15275, h15459, hlam]
            · linarith only [h0, h15274, h15458, hlam]
      · linarith only [h11844, h15275, h15277, hlam]
    · linarith only [h11844, h15274, h15276, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h15516 | h15516
    · rcases m.htr 0 3 5 (by decide) (by decide) with h15517 | h15517
      · rcases m.htr 0 4 5 (by decide) (by decide) with h15518 | h15518
        · linarith only [h15274, h15275, h15518, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h15520 | h15520
          · rcases m.htr 1 2 4 (by decide) (by decide) with h15521 | h15521
            · rcases m.htr 1 2 5 (by decide) (by decide) with h15522 | h15522
              · rcases m.htr 1 3 4 (by decide) (by decide) with h15523 | h15523
                · rcases m.htr 1 3 5 (by decide) (by decide) with h15524 | h15524
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h15525 | h15525
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15526 | h15526
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15527 | h15527
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h15528 | h15528
                          · linarith only [h15274, h15275, h15518, h15520, h15527, h15528, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h15530 | h15530
                            · linarith only [h15274, h15275, h15526, h15528, h15530, hlam]
                            · rcases h0bigk with h15532c | h15532c | h15532c | h15532c | h15532c | h15532c | h15532c | h15532c | h15532c | h15532c | h15532c | h15532c | h15532c | h15532c | h15532c | h15532c | h15532c | h15532c | h15532c | h15532c | h15532c | h15532c | h15532c | h15532c | h15532c
                              · have p15532_0 := h15532c.1
                                have p15532_1 := h15532c.2.1
                                have p15532_2 := h15532c.2.2.1
                                have p15532_3 := h15532c.2.2.2
                                linarith only [hlam, p15532_0]
                              · have p15532_0 := h15532c.1
                                have p15532_1 := h15532c.2.1
                                have p15532_2 := h15532c.2.2.1
                                have p15532_3 := h15532c.2.2.2
                                linarith only [h0, hlam, p15532_1]
                              · have p15532_0 := h15532c.1
                                have p15532_1 := h15532c.2.1
                                have p15532_2 := h15532c.2.2.1
                                have p15532_3 := h15532c.2.2.2
                                linarith only [h6310, hlam, p15532_0]
                              · have p15532_0 := h15532c.1
                                have p15532_1 := h15532c.2.1
                                have p15532_2 := h15532c.2.2.1
                                have p15532_3 := h15532c.2.2.2
                                linarith only [h9935, hlam, p15532_1]
                              · have p15532_0 := h15532c.1
                                have p15532_1 := h15532c.2.1
                                have p15532_2 := h15532c.2.2.1
                                have p15532_3 := h15532c.2.2.2
                                linarith only [h11282, hlam, p15532_1]
                              · have p15532_0 := h15532c.1
                                have p15532_1 := h15532c.2.1
                                have p15532_2 := h15532c.2.2.1
                                have p15532_3 := h15532c.2.2.2
                                linarith only [h15275, h15520, h15523, h15525, h15528, hc01, hc12, hlam, hphi, p15532_1]
                              · have p15532_0 := h15532c.1
                                have p15532_1 := h15532c.2.1
                                have p15532_2 := h15532c.2.2.1
                                have p15532_3 := h15532c.2.2.2
                                linarith only [hlam, p15532_0]
                              · have p15532_0 := h15532c.1
                                have p15532_1 := h15532c.2.1
                                have p15532_2 := h15532c.2.2.1
                                have p15532_3 := h15532c.2.2.2
                                linarith only [h11844, hlam, p15532_0]
                              · have p15532_0 := h15532c.1
                                have p15532_1 := h15532c.2.1
                                have p15532_2 := h15532c.2.2.1
                                have p15532_3 := h15532c.2.2.2
                                linarith only [h15275, h15520, h15523, h15525, h15528, h9935, hc01, hc12, hlam, hphi, p15532_1]
                              · have p15532_0 := h15532c.1
                                have p15532_1 := h15532c.2.1
                                have p15532_2 := h15532c.2.2.1
                                have p15532_3 := h15532c.2.2.2
                                linarith only [h15275, hlam, p15532_0]
                              · have p15532_0 := h15532c.1
                                have p15532_1 := h15532c.2.1
                                have p15532_2 := h15532c.2.2.1
                                have p15532_3 := h15532c.2.2.2
                                linarith only [h11844, h15520, hc01, hc12, hlam, hphi, p15532_1]
                              · have p15532_0 := h15532c.1
                                have p15532_1 := h15532c.2.1
                                have p15532_2 := h15532c.2.2.1
                                have p15532_3 := h15532c.2.2.2
                                linarith only [h15274, hc24, hlam, hphi, ht0b, ht45, ht5b, p15532_1, u0elo2]
                              · have p15532_0 := h15532c.1
                                have p15532_1 := h15532c.2.1
                                have p15532_2 := h15532c.2.2.1
                                have p15532_3 := h15532c.2.2.2
                                linarith only [hlam, p15532_0]
                              · have p15532_0 := h15532c.1
                                have p15532_1 := h15532c.2.1
                                have p15532_2 := h15532c.2.2.1
                                have p15532_3 := h15532c.2.2.2
                                linarith only [h11844, h15520, h9935, hc01, hc12, hlam, hphi, p15532_1]
                              · have p15532_0 := h15532c.1
                                have p15532_1 := h15532c.2.1
                                have p15532_2 := h15532c.2.2.1
                                have p15532_3 := h15532c.2.2.2
                                linarith only [h11844, h15274, h15275, h15520, h15526, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15532_1]
                              · have p15532_0 := h15532c.1
                                have p15532_1 := h15532c.2.1
                                have p15532_2 := h15532c.2.2.1
                                have p15532_3 := h15532c.2.2.2
                                linarith only [h15274, h15275, h15523, h15525, h15528, hc01, hc13, hlam, hphi, p15532_1]
                              · have p15532_0 := h15532c.1
                                have p15532_1 := h15532c.2.1
                                have p15532_2 := h15532c.2.2.1
                                have p15532_3 := h15532c.2.2.2
                                linarith only [h15274, hlam, p15532_0]
                              · have p15532_0 := h15532c.1
                                have p15532_1 := h15532c.2.1
                                have p15532_2 := h15532c.2.2.1
                                have p15532_3 := h15532c.2.2.2
                                linarith only [h15516, hlam, p15532_0]
                              · have p15532_0 := h15532c.1
                                have p15532_1 := h15532c.2.1
                                have p15532_2 := h15532c.2.2.1
                                have p15532_3 := h15532c.2.2.2
                                linarith only [hlam, p15532_0]
                              · have p15532_0 := h15532c.1
                                have p15532_1 := h15532c.2.1
                                have p15532_2 := h15532c.2.2.1
                                have p15532_3 := h15532c.2.2.2
                                linarith only [h15518, hlam, p15532_0]
                              · have p15532_0 := h15532c.1
                                have p15532_1 := h15532c.2.1
                                have p15532_2 := h15532c.2.2.1
                                have p15532_3 := h15532c.2.2.2
                                linarith only [h15275, h15523, h15525, h15528, hc01, hc13, hlam, hphi, p15532_1]
                              · have p15532_0 := h15532c.1
                                have p15532_1 := h15532c.2.1
                                have p15532_2 := h15532c.2.2.1
                                have p15532_3 := h15532c.2.2.2
                                linarith only [h15274, h15275, h15523, h15525, h15526, h15528, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15532_1]
                              · have p15532_0 := h15532c.1
                                have p15532_1 := h15532c.2.1
                                have p15532_2 := h15532c.2.2.1
                                have p15532_3 := h15532c.2.2.2
                                linarith only [h15517, hlam, p15532_0]
                              · have p15532_0 := h15532c.1
                                have p15532_1 := h15532c.2.1
                                have p15532_2 := h15532c.2.2.1
                                have p15532_3 := h15532c.2.2.2
                                linarith only [h15275, h15523, h15525, h15528, h9935, hc01, hc13, hlam, hphi, p15532_1]
                              · have p15532_0 := h15532c.1
                                have p15532_1 := h15532c.2.1
                                have p15532_2 := h15532c.2.2.1
                                have p15532_3 := h15532c.2.2.2
                                linarith only [hlam, p15532_0]
                        · linarith only [h11844, h15517, h15527, hlam]
                      · linarith only [h11844, h15516, h15526, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15560 | h15560
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15561 | h15561
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h15562 | h15562
                          · linarith only [h15274, h15525, h15562, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h15564 | h15564
                            · linarith only [h15275, h15516, h15522, h15525, h15564, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                            · rcases h0bigk with h15566c | h15566c | h15566c | h15566c | h15566c | h15566c | h15566c | h15566c | h15566c | h15566c | h15566c | h15566c | h15566c | h15566c | h15566c | h15566c | h15566c | h15566c | h15566c | h15566c | h15566c | h15566c | h15566c | h15566c | h15566c
                              · have p15566_0 := h15566c.1
                                have p15566_1 := h15566c.2.1
                                have p15566_2 := h15566c.2.2.1
                                have p15566_3 := h15566c.2.2.2
                                linarith only [hlam, p15566_0]
                              · have p15566_0 := h15566c.1
                                have p15566_1 := h15566c.2.1
                                have p15566_2 := h15566c.2.2.1
                                have p15566_3 := h15566c.2.2.2
                                linarith only [h0, hlam, p15566_1]
                              · have p15566_0 := h15566c.1
                                have p15566_1 := h15566c.2.1
                                have p15566_2 := h15566c.2.2.1
                                have p15566_3 := h15566c.2.2.2
                                linarith only [h6310, hlam, p15566_0]
                              · have p15566_0 := h15566c.1
                                have p15566_1 := h15566c.2.1
                                have p15566_2 := h15566c.2.2.1
                                have p15566_3 := h15566c.2.2.2
                                linarith only [h9935, hlam, p15566_1]
                              · have p15566_0 := h15566c.1
                                have p15566_1 := h15566c.2.1
                                have p15566_2 := h15566c.2.2.1
                                have p15566_3 := h15566c.2.2.2
                                linarith only [h11282, hlam, p15566_1]
                              · have p15566_0 := h15566c.1
                                have p15566_1 := h15566c.2.1
                                have p15566_2 := h15566c.2.2.1
                                have p15566_3 := h15566c.2.2.2
                                linarith only [h15275, h15522, hc01, hc15, hlam, hphi, p15566_1]
                              · have p15566_0 := h15566c.1
                                have p15566_1 := h15566c.2.1
                                have p15566_2 := h15566c.2.2.1
                                have p15566_3 := h15566c.2.2.2
                                linarith only [hlam, p15566_0]
                              · have p15566_0 := h15566c.1
                                have p15566_1 := h15566c.2.1
                                have p15566_2 := h15566c.2.2.1
                                have p15566_3 := h15566c.2.2.2
                                linarith only [h11844, hlam, p15566_0]
                              · have p15566_0 := h15566c.1
                                have p15566_1 := h15566c.2.1
                                have p15566_2 := h15566c.2.2.1
                                have p15566_3 := h15566c.2.2.2
                                linarith only [h15275, h15522, h9935, hc01, hc15, hlam, hphi, p15566_1]
                              · have p15566_0 := h15566c.1
                                have p15566_1 := h15566c.2.1
                                have p15566_2 := h15566c.2.2.1
                                have p15566_3 := h15566c.2.2.2
                                linarith only [h15275, hlam, p15566_0]
                              · have p15566_0 := h15566c.1
                                have p15566_1 := h15566c.2.1
                                have p15566_2 := h15566c.2.2.1
                                have p15566_3 := h15566c.2.2.2
                                linarith only [h11844, h15520, hc01, hc12, hlam, hphi, p15566_1]
                              · have p15566_0 := h15566c.1
                                have p15566_1 := h15566c.2.1
                                have p15566_2 := h15566c.2.2.1
                                have p15566_3 := h15566c.2.2.2
                                linarith only [h0, h11844, h15520, hc01, hc12, hlam, hphi, p15566_1]
                              · have p15566_0 := h15566c.1
                                have p15566_1 := h15566c.2.1
                                have p15566_2 := h15566c.2.2.1
                                have p15566_3 := h15566c.2.2.2
                                linarith only [hlam, p15566_0]
                              · have p15566_0 := h15566c.1
                                have p15566_1 := h15566c.2.1
                                have p15566_2 := h15566c.2.2.1
                                have p15566_3 := h15566c.2.2.2
                                linarith only [h11844, h15520, h9935, hc01, hc12, hlam, hphi, p15566_1]
                              · have p15566_0 := h15566c.1
                                have p15566_1 := h15566c.2.1
                                have p15566_2 := h15566c.2.2.1
                                have p15566_3 := h15566c.2.2.2
                                linarith only [h11282, h11844, h15520, hc01, hc12, hlam, hphi, p15566_1]
                              · have p15566_0 := h15566c.1
                                have p15566_1 := h15566c.2.1
                                have p15566_2 := h15566c.2.2.1
                                have p15566_3 := h15566c.2.2.2
                                linarith only [h15525, h9935, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p15566_1]
                              · have p15566_0 := h15566c.1
                                have p15566_1 := h15566c.2.1
                                have p15566_2 := h15566c.2.2.1
                                have p15566_3 := h15566c.2.2.2
                                linarith only [h15274, hlam, p15566_0]
                              · have p15566_0 := h15566c.1
                                have p15566_1 := h15566c.2.1
                                have p15566_2 := h15566c.2.2.1
                                have p15566_3 := h15566c.2.2.2
                                linarith only [h15516, hlam, p15566_0]
                              · have p15566_0 := h15566c.1
                                have p15566_1 := h15566c.2.1
                                have p15566_2 := h15566c.2.2.1
                                have p15566_3 := h15566c.2.2.2
                                linarith only [hlam, p15566_0]
                              · have p15566_0 := h15566c.1
                                have p15566_1 := h15566c.2.1
                                have p15566_2 := h15566c.2.2.1
                                have p15566_3 := h15566c.2.2.2
                                linarith only [h15518, hlam, p15566_0]
                              · have p15566_0 := h15566c.1
                                have p15566_1 := h15566c.2.1
                                have p15566_2 := h15566c.2.2.1
                                have p15566_3 := h15566c.2.2.2
                                linarith only [h11844, h15517, h15520, hc01, hc12, hlam, hphi, p15566_1]
                              · have p15566_0 := h15566c.1
                                have p15566_1 := h15566c.2.1
                                have p15566_2 := h15566c.2.2.1
                                have p15566_3 := h15566c.2.2.2
                                linarith only [h15274, h15560, hc34, hlam, hphi, ht0b, ht45, ht5b, p15566_1, u0elo4]
                              · have p15566_0 := h15566c.1
                                have p15566_1 := h15566c.2.1
                                have p15566_2 := h15566c.2.2.1
                                have p15566_3 := h15566c.2.2.2
                                linarith only [h15517, hlam, p15566_0]
                              · have p15566_0 := h15566c.1
                                have p15566_1 := h15566c.2.1
                                have p15566_2 := h15566c.2.2.1
                                have p15566_3 := h15566c.2.2.2
                                linarith only [h11844, h15517, h15520, h9935, hc01, hc12, hlam, hphi, p15566_1]
                              · have p15566_0 := h15566c.1
                                have p15566_1 := h15566c.2.1
                                have p15566_2 := h15566c.2.2.1
                                have p15566_3 := h15566c.2.2.2
                                linarith only [hlam, p15566_0]
                        · linarith only [h11844, h15517, h15561, hlam]
                      · linarith only [h11844, h15516, h15560, hlam]
                  · linarith only [h11844, h15517, h15520, h15524, h6310, hc01, hc12, hlam, hphi]
                · linarith only [h11844, h15274, h15516, h15520, h15523, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
              · linarith only [h11844, h15274, h15520, h15522, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h11844, h15274, h15520, h15521, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h15598 | h15598
            · rcases m.htr 1 2 5 (by decide) (by decide) with h15599 | h15599
              · linarith only [h15275, h15520, h15599, hc02, hc23, hlam, hphi]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h15601 | h15601
                · rcases m.htr 1 3 5 (by decide) (by decide) with h15602 | h15602
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h15603 | h15603
                    · linarith only [h15518, h15520, h15598, h15603, h9935, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15605 | h15605
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15606 | h15606
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h15607 | h15607
                          · linarith only [h15274, h15603, h15607, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h15609 | h15609
                            · linarith only [h0, h15599, h15607, h15609, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases h0bigk with h15611c | h15611c | h15611c | h15611c | h15611c | h15611c | h15611c | h15611c | h15611c | h15611c | h15611c | h15611c | h15611c | h15611c | h15611c | h15611c | h15611c | h15611c | h15611c | h15611c | h15611c | h15611c | h15611c | h15611c | h15611c
                              · have p15611_0 := h15611c.1
                                have p15611_1 := h15611c.2.1
                                have p15611_2 := h15611c.2.2.1
                                have p15611_3 := h15611c.2.2.2
                                linarith only [hlam, p15611_0]
                              · have p15611_0 := h15611c.1
                                have p15611_1 := h15611c.2.1
                                have p15611_2 := h15611c.2.2.1
                                have p15611_3 := h15611c.2.2.2
                                linarith only [h0, hlam, p15611_1]
                              · have p15611_0 := h15611c.1
                                have p15611_1 := h15611c.2.1
                                have p15611_2 := h15611c.2.2.1
                                have p15611_3 := h15611c.2.2.2
                                linarith only [h6310, hlam, p15611_0]
                              · have p15611_0 := h15611c.1
                                have p15611_1 := h15611c.2.1
                                have p15611_2 := h15611c.2.2.1
                                have p15611_3 := h15611c.2.2.2
                                linarith only [h9935, hlam, p15611_1]
                              · have p15611_0 := h15611c.1
                                have p15611_1 := h15611c.2.1
                                have p15611_2 := h15611c.2.2.1
                                have p15611_3 := h15611c.2.2.2
                                linarith only [h11282, hlam, p15611_1]
                              · have p15611_0 := h15611c.1
                                have p15611_1 := h15611c.2.1
                                have p15611_2 := h15611c.2.2.1
                                have p15611_3 := h15611c.2.2.2
                                linarith only [h0, h15599, hc01, hc25, hlam, hphi, ht12, p15611_1]
                              · have p15611_0 := h15611c.1
                                have p15611_1 := h15611c.2.1
                                have p15611_2 := h15611c.2.2.1
                                have p15611_3 := h15611c.2.2.2
                                linarith only [hlam, p15611_0]
                              · have p15611_0 := h15611c.1
                                have p15611_1 := h15611c.2.1
                                have p15611_2 := h15611c.2.2.1
                                have p15611_3 := h15611c.2.2.2
                                linarith only [h11844, hlam, p15611_0]
                              · have p15611_0 := h15611c.1
                                have p15611_1 := h15611c.2.1
                                have p15611_2 := h15611c.2.2.1
                                have p15611_3 := h15611c.2.2.2
                                linarith only [h0, h15599, h15607, hc04, hc45, hlam, hphi, p15611_1]
                              · have p15611_0 := h15611c.1
                                have p15611_1 := h15611c.2.1
                                have p15611_2 := h15611c.2.2.1
                                have p15611_3 := h15611c.2.2.2
                                linarith only [h15275, hlam, p15611_0]
                              · have p15611_0 := h15611c.1
                                have p15611_1 := h15611c.2.1
                                have p15611_2 := h15611c.2.2.1
                                have p15611_3 := h15611c.2.2.2
                                rcases p15611_3 (m.d 0 1) (by simp) with h15622 | h15622
                                · linarith only [h15622, h6310, hlam]
                                · rcases p15611_3 (m.d 0 2) (by simp) with h15624 | h15624
                                  · linarith only [h11844, h15624, hlam]
                                  · linarith only [h0, h15624, hlam]
                              · have p15611_0 := h15611c.1
                                have p15611_1 := h15611c.2.1
                                have p15611_2 := h15611c.2.2.1
                                have p15611_3 := h15611c.2.2.2
                                linarith only [h15274, hc24, hlam, hphi, ht0b, ht45, ht5b, p15611_1, u0elo2]
                              · have p15611_0 := h15611c.1
                                have p15611_1 := h15611c.2.1
                                have p15611_2 := h15611c.2.2.1
                                have p15611_3 := h15611c.2.2.2
                                linarith only [hlam, p15611_0]
                              · have p15611_0 := h15611c.1
                                have p15611_1 := h15611c.2.1
                                have p15611_2 := h15611c.2.2.1
                                have p15611_3 := h15611c.2.2.2
                                rcases p15611_3 (m.d 0 1) (by simp) with h15629 | h15629
                                · linarith only [h15629, h6310, hlam]
                                · rcases p15611_3 (m.d 0 2) (by simp) with h15631 | h15631
                                  · linarith only [h11844, h15631, hlam]
                                  · linarith only [h15274, h15631, hlam]
                              · have p15611_0 := h15611c.1
                                have p15611_1 := h15611c.2.1
                                have p15611_2 := h15611c.2.2.1
                                have p15611_3 := h15611c.2.2.2
                                linarith only [h15274, h15275, h15605, hc34, hlam, hphi, ht0b, ht45, ht5b, p15611_1, u0elo2]
                              · have p15611_0 := h15611c.1
                                have p15611_1 := h15611c.2.1
                                have p15611_2 := h15611c.2.2.1
                                have p15611_3 := h15611c.2.2.2
                                linarith only [h15598, h15599, h15607, h9935, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p15611_1]
                              · have p15611_0 := h15611c.1
                                have p15611_1 := h15611c.2.1
                                have p15611_2 := h15611c.2.2.1
                                have p15611_3 := h15611c.2.2.2
                                linarith only [h15274, hlam, p15611_0]
                              · have p15611_0 := h15611c.1
                                have p15611_1 := h15611c.2.1
                                have p15611_2 := h15611c.2.2.1
                                have p15611_3 := h15611c.2.2.2
                                linarith only [h15516, hlam, p15611_0]
                              · have p15611_0 := h15611c.1
                                have p15611_1 := h15611c.2.1
                                have p15611_2 := h15611c.2.2.1
                                have p15611_3 := h15611c.2.2.2
                                linarith only [hlam, p15611_0]
                              · have p15611_0 := h15611c.1
                                have p15611_1 := h15611c.2.1
                                have p15611_2 := h15611c.2.2.1
                                have p15611_3 := h15611c.2.2.2
                                linarith only [h15518, hlam, p15611_0]
                              · have p15611_0 := h15611c.1
                                have p15611_1 := h15611c.2.1
                                have p15611_2 := h15611c.2.2.1
                                have p15611_3 := h15611c.2.2.2
                                rcases p15611_3 (m.d 0 1) (by simp) with h15640 | h15640
                                · linarith only [h11282, h15640, hlam]
                                · rcases p15611_3 (m.d 0 2) (by simp) with h15642 | h15642
                                  · linarith only [h15275, h15642, hlam]
                                  · linarith only [h0, h15642, hlam]
                              · have p15611_0 := h15611c.1
                                have p15611_1 := h15611c.2.1
                                have p15611_2 := h15611c.2.2.1
                                have p15611_3 := h15611c.2.2.2
                                linarith only [h11282, h15274, h15599, h15605, h15607, hc34, hc45, hlam, hphi, p15611_1]
                              · have p15611_0 := h15611c.1
                                have p15611_1 := h15611c.2.1
                                have p15611_2 := h15611c.2.2.1
                                have p15611_3 := h15611c.2.2.2
                                linarith only [h15517, hlam, p15611_0]
                              · have p15611_0 := h15611c.1
                                have p15611_1 := h15611c.2.1
                                have p15611_2 := h15611c.2.2.1
                                have p15611_3 := h15611c.2.2.2
                                rcases p15611_3 (m.d 0 1) (by simp) with h15647 | h15647
                                · linarith only [h11282, h15647, hlam]
                                · rcases p15611_3 (m.d 0 2) (by simp) with h15649 | h15649
                                  · linarith only [h15275, h15649, hlam]
                                  · linarith only [h15274, h15649, hlam]
                              · have p15611_0 := h15611c.1
                                have p15611_1 := h15611c.2.1
                                have p15611_2 := h15611c.2.2.1
                                have p15611_3 := h15611c.2.2.2
                                linarith only [hlam, p15611_0]
                        · linarith only [h15517, h15520, h15606, h6310, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h15516, h15520, h15605, h6310, hlam]
                  · linarith only [h15517, h15602, h6310, hlam]
                · linarith only [h15516, h15520, h15598, h15601, h6310, h9935, hc01, hc23, hlam, hphi, ht12]
            · linarith only [h0, h15274, h15598, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h15658 | h15658
        · linarith only [h15274, h15275, h15658, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h15660 | h15660
          · rcases m.htr 1 2 4 (by decide) (by decide) with h15661 | h15661
            · rcases m.htr 1 2 5 (by decide) (by decide) with h15662 | h15662
              · rcases m.htr 1 3 4 (by decide) (by decide) with h15663 | h15663
                · rcases m.htr 1 3 5 (by decide) (by decide) with h15664 | h15664
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h15665 | h15665
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15666 | h15666
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15667 | h15667
                        · linarith only [h11844, h15274, h15517, h15660, h15667, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h11844, h15274, h15664, h15666, h15667, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h11844, h15516, h15666, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15671 | h15671
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15672 | h15672
                        · linarith only [h15517, h15660, h15672, h6310, hc01, hc12, hlam, hphi]
                        · linarith only [h11844, h15274, h15660, h15664, h15671, h15672, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h11844, h15516, h15671, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h15676 | h15676
                    · linarith only [h15658, h15663, h15664, h15676, h9935, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15678 | h15678
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15679 | h15679
                        · linarith only [h15660, h15664, h15679, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h15681 | h15681
                          · linarith only [h11282, h15274, h15676, h15681, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h15683 | h15683
                            · linarith only [h11844, h15274, h15660, h15664, h15676, h15678, h15683, h9935, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h11844, h15274, h15660, h15664, h15678, h15683, hc34, hc45, hlam, hphi]
                      · linarith only [h11844, h15274, h15516, h15678, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · linarith only [h11844, h15274, h15516, h15660, h15663, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
              · linarith only [h11844, h15274, h15660, h15662, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h11844, h15274, h15660, h15661, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h15690 | h15690
            · rcases m.htr 1 2 5 (by decide) (by decide) with h15691 | h15691
              · linarith only [h15274, h15275, h15660, h15691, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h15693 | h15693
                · rcases m.htr 1 3 5 (by decide) (by decide) with h15694 | h15694
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h15695 | h15695
                    · linarith only [h15658, h15660, h15690, h15695, h9935, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15697 | h15697
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15698 | h15698
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h15699 | h15699
                          · linarith only [h15274, h15695, h15699, h9935, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h15701 | h15701
                            · linarith only [h11844, h15274, h15517, h15660, h15691, h15694, h15697, h15699, h15701, hc12, hc23, hlam, hphi]
                            · rcases h0bigk with h15703c | h15703c | h15703c | h15703c | h15703c | h15703c | h15703c | h15703c | h15703c | h15703c | h15703c | h15703c | h15703c | h15703c | h15703c | h15703c | h15703c | h15703c | h15703c | h15703c | h15703c | h15703c | h15703c | h15703c | h15703c
                              · have p15703_0 := h15703c.1
                                have p15703_1 := h15703c.2.1
                                have p15703_2 := h15703c.2.2.1
                                have p15703_3 := h15703c.2.2.2
                                linarith only [hlam, p15703_0]
                              · have p15703_0 := h15703c.1
                                have p15703_1 := h15703c.2.1
                                have p15703_2 := h15703c.2.2.1
                                have p15703_3 := h15703c.2.2.2
                                linarith only [h0, hlam, p15703_1]
                              · have p15703_0 := h15703c.1
                                have p15703_1 := h15703c.2.1
                                have p15703_2 := h15703c.2.2.1
                                have p15703_3 := h15703c.2.2.2
                                linarith only [h6310, hlam, p15703_0]
                              · have p15703_0 := h15703c.1
                                have p15703_1 := h15703c.2.1
                                have p15703_2 := h15703c.2.2.1
                                have p15703_3 := h15703c.2.2.2
                                linarith only [h9935, hlam, p15703_1]
                              · have p15703_0 := h15703c.1
                                have p15703_1 := h15703c.2.1
                                have p15703_2 := h15703c.2.2.1
                                have p15703_3 := h15703c.2.2.2
                                linarith only [h11282, hlam, p15703_1]
                              · have p15703_0 := h15703c.1
                                have p15703_1 := h15703c.2.1
                                have p15703_2 := h15703c.2.2.1
                                have p15703_3 := h15703c.2.2.2
                                linarith only [h11844, h15517, h15660, h15694, hc01, hc23, hlam, hphi, ht12, p15703_1]
                              · have p15703_0 := h15703c.1
                                have p15703_1 := h15703c.2.1
                                have p15703_2 := h15703c.2.2.1
                                have p15703_3 := h15703c.2.2.2
                                linarith only [hlam, p15703_0]
                              · have p15703_0 := h15703c.1
                                have p15703_1 := h15703c.2.1
                                have p15703_2 := h15703c.2.2.1
                                have p15703_3 := h15703c.2.2.2
                                linarith only [h11844, hlam, p15703_0]
                              · have p15703_0 := h15703c.1
                                have p15703_1 := h15703c.2.1
                                have p15703_2 := h15703c.2.2.1
                                have p15703_3 := h15703c.2.2.2
                                linarith only [h11844, h15517, h15660, h15694, h9935, hc01, hc23, hlam, hphi, ht12, p15703_1]
                              · have p15703_0 := h15703c.1
                                have p15703_1 := h15703c.2.1
                                have p15703_2 := h15703c.2.2.1
                                have p15703_3 := h15703c.2.2.2
                                linarith only [h15275, hlam, p15703_0]
                              · have p15703_0 := h15703c.1
                                have p15703_1 := h15703c.2.1
                                have p15703_2 := h15703c.2.2.1
                                have p15703_3 := h15703c.2.2.2
                                linarith only [h15517, h15660, h15694, hc01, hc23, hlam, hphi, ht12, p15703_1]
                              · have p15703_0 := h15703c.1
                                have p15703_1 := h15703c.2.1
                                have p15703_2 := h15703c.2.2.1
                                have p15703_3 := h15703c.2.2.2
                                linarith only [h15274, h15517, h15660, h15694, h15697, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p15703_1]
                              · have p15703_0 := h15703c.1
                                have p15703_1 := h15703c.2.1
                                have p15703_2 := h15703c.2.2.1
                                have p15703_3 := h15703c.2.2.2
                                linarith only [hlam, p15703_0]
                              · have p15703_0 := h15703c.1
                                have p15703_1 := h15703c.2.1
                                have p15703_2 := h15703c.2.2.1
                                have p15703_3 := h15703c.2.2.2
                                linarith only [h15517, h15660, h15694, h9935, hc01, hc23, hlam, hphi, ht12, p15703_1]
                              · have p15703_0 := h15703c.1
                                have p15703_1 := h15703c.2.1
                                have p15703_2 := h15703c.2.2.1
                                have p15703_3 := h15703c.2.2.2
                                linarith only [h15517, hlam, p15703_1]
                              · have p15703_0 := h15703c.1
                                have p15703_1 := h15703c.2.1
                                have p15703_2 := h15703c.2.2.1
                                have p15703_3 := h15703c.2.2.2
                                linarith only [h15690, h15691, h9935, hc01, hc25, hlam, hphi, ht12, p15703_1]
                              · have p15703_0 := h15703c.1
                                have p15703_1 := h15703c.2.1
                                have p15703_2 := h15703c.2.2.1
                                have p15703_3 := h15703c.2.2.2
                                linarith only [h15274, hlam, p15703_0]
                              · have p15703_0 := h15703c.1
                                have p15703_1 := h15703c.2.1
                                have p15703_2 := h15703c.2.2.1
                                have p15703_3 := h15703c.2.2.2
                                linarith only [h15516, hlam, p15703_0]
                              · have p15703_0 := h15703c.1
                                have p15703_1 := h15703c.2.1
                                have p15703_2 := h15703c.2.2.1
                                have p15703_3 := h15703c.2.2.2
                                linarith only [hlam, p15703_0]
                              · have p15703_0 := h15703c.1
                                have p15703_1 := h15703c.2.1
                                have p15703_2 := h15703c.2.2.1
                                have p15703_3 := h15703c.2.2.2
                                linarith only [h15658, hlam, p15703_0]
                              · have p15703_0 := h15703c.1
                                have p15703_1 := h15703c.2.1
                                have p15703_2 := h15703c.2.2.1
                                have p15703_3 := h15703c.2.2.2
                                linarith only [h15517, h15660, h15694, hc01, hc23, hlam, hphi, ht12, p15703_1]
                              · have p15703_0 := h15703c.1
                                have p15703_1 := h15703c.2.1
                                have p15703_2 := h15703c.2.2.1
                                have p15703_3 := h15703c.2.2.2
                                linarith only [h15274, h15517, h15660, h15694, h15697, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p15703_1]
                              · have p15703_0 := h15703c.1
                                have p15703_1 := h15703c.2.1
                                have p15703_2 := h15703c.2.2.1
                                have p15703_3 := h15703c.2.2.2
                                linarith only [h15517, h15660, h15694, h6310, hc01, hc23, hlam, hphi, ht12, p15703_1]
                              · have p15703_0 := h15703c.1
                                have p15703_1 := h15703c.2.1
                                have p15703_2 := h15703c.2.2.1
                                have p15703_3 := h15703c.2.2.2
                                linarith only [h15517, h15660, h15694, h9935, hc01, hc23, hlam, hphi, ht12, p15703_1]
                              · have p15703_0 := h15703c.1
                                have p15703_1 := h15703c.2.1
                                have p15703_2 := h15703c.2.2.1
                                have p15703_3 := h15703c.2.2.2
                                linarith only [hlam, p15703_0]
                        · linarith only [h15660, h15694, h15698, hlam]
                      · linarith only [h15516, h15660, h15697, h6310, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h15731 | h15731
                    · linarith only [h15658, h15660, h15690, h15694, h15731, h9935, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15733 | h15733
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15734 | h15734
                        · linarith only [h0, h15660, h15694, h15734, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h15660, h15690, h15734, h9935, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h15660, h15690, h15733, h9935, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h15516, h15660, h15690, h15693, h9935, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
            · linarith only [h0, h15274, h15690, hlam]
    · linarith only [h11844, h15274, h15516, hlam]

set_option maxHeartbeats 10516000 in
set_option maxHeartbeats 10516000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s16_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg9935 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11282 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11844 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h15274 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h15741 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h9935 := hg9935
  have h11282 := hg11282
  rcases m.htr 0 3 4 (by decide) (by decide) with h15742 | h15742
  · rcases m.htr 0 3 5 (by decide) (by decide) with h15743 | h15743
    · rcases m.htr 0 4 5 (by decide) (by decide) with h15744 | h15744
      · rcases m.htr 1 2 3 (by decide) (by decide) with h15745 | h15745
        · rcases m.htr 1 2 4 (by decide) (by decide) with h15746 | h15746
          · rcases m.htr 1 2 5 (by decide) (by decide) with h15747 | h15747
            · rcases m.htr 1 3 4 (by decide) (by decide) with h15748 | h15748
              · rcases m.htr 1 3 5 (by decide) (by decide) with h15749 | h15749
                · rcases m.htr 1 4 5 (by decide) (by decide) with h15750 | h15750
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h15751 | h15751
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h15752 | h15752
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h15753 | h15753
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h15754 | h15754
                          · rcases h0bigk with h15755c | h15755c | h15755c | h15755c | h15755c | h15755c | h15755c | h15755c | h15755c | h15755c | h15755c | h15755c | h15755c | h15755c | h15755c | h15755c | h15755c | h15755c | h15755c | h15755c | h15755c | h15755c | h15755c | h15755c | h15755c
                            · have p15755_0 := h15755c.1
                              have p15755_1 := h15755c.2.1
                              have p15755_2 := h15755c.2.2.1
                              have p15755_3 := h15755c.2.2.2
                              linarith only [hlam, p15755_0]
                            · have p15755_0 := h15755c.1
                              have p15755_1 := h15755c.2.1
                              have p15755_2 := h15755c.2.2.1
                              have p15755_3 := h15755c.2.2.2
                              linarith only [h0, hlam, p15755_1]
                            · have p15755_0 := h15755c.1
                              have p15755_1 := h15755c.2.1
                              have p15755_2 := h15755c.2.2.1
                              have p15755_3 := h15755c.2.2.2
                              linarith only [h6310, hlam, p15755_0]
                            · have p15755_0 := h15755c.1
                              have p15755_1 := h15755c.2.1
                              have p15755_2 := h15755c.2.2.1
                              have p15755_3 := h15755c.2.2.2
                              linarith only [h9935, hlam, p15755_1]
                            · have p15755_0 := h15755c.1
                              have p15755_1 := h15755c.2.1
                              have p15755_2 := h15755c.2.2.1
                              have p15755_3 := h15755c.2.2.2
                              linarith only [h11282, hlam, p15755_1]
                            · have p15755_0 := h15755c.1
                              have p15755_1 := h15755c.2.1
                              have p15755_2 := h15755c.2.2.1
                              have p15755_3 := h15755c.2.2.2
                              linarith only [h15274, h15745, h15751, hc01, hc12, hlam, hphi, p15755_1]
                            · have p15755_0 := h15755c.1
                              have p15755_1 := h15755c.2.1
                              have p15755_2 := h15755c.2.2.1
                              have p15755_3 := h15755c.2.2.2
                              linarith only [hlam, p15755_0]
                            · have p15755_0 := h15755c.1
                              have p15755_1 := h15755c.2.1
                              have p15755_2 := h15755c.2.2.1
                              have p15755_3 := h15755c.2.2.2
                              linarith only [h11844, hlam, p15755_0]
                            · have p15755_0 := h15755c.1
                              have p15755_1 := h15755c.2.1
                              have p15755_2 := h15755c.2.2.1
                              have p15755_3 := h15755c.2.2.2
                              linarith only [h15274, hlam, p15755_1]
                            · have p15755_0 := h15755c.1
                              have p15755_1 := h15755c.2.1
                              have p15755_2 := h15755c.2.2.1
                              have p15755_3 := h15755c.2.2.2
                              linarith only [h15274, h15745, h15751, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p15755_1]
                            · have p15755_0 := h15755c.1
                              have p15755_1 := h15755c.2.1
                              have p15755_2 := h15755c.2.2.1
                              have p15755_3 := h15755c.2.2.2
                              linarith only [h11844, h15745, hc01, hc12, hlam, hphi, p15755_1]
                            · have p15755_0 := h15755c.1
                              have p15755_1 := h15755c.2.1
                              have p15755_2 := h15755c.2.2.1
                              have p15755_3 := h15755c.2.2.2
                              linarith only [h11844, h15741, h15745, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p15755_1]
                            · have p15755_0 := h15755c.1
                              have p15755_1 := h15755c.2.1
                              have p15755_2 := h15755c.2.2.1
                              have p15755_3 := h15755c.2.2.2
                              linarith only [hlam, p15755_0]
                            · have p15755_0 := h15755c.1
                              have p15755_1 := h15755c.2.1
                              have p15755_2 := h15755c.2.2.1
                              have p15755_3 := h15755c.2.2.2
                              linarith only [h11844, h15274, h15741, h15745, h15752, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p15755_1]
                            · have p15755_0 := h15755c.1
                              have p15755_1 := h15755c.2.1
                              have p15755_2 := h15755c.2.2.1
                              have p15755_3 := h15755c.2.2.2
                              linarith only [h11282, h11844, h15745, hc01, hc12, hlam, hphi, p15755_1]
                            · have p15755_0 := h15755c.1
                              have p15755_1 := h15755c.2.1
                              have p15755_2 := h15755c.2.2.1
                              have p15755_3 := h15755c.2.2.2
                              linarith only [h15274, h15745, h15751, hc01, hc12, hlam, hphi, p15755_1]
                            · have p15755_0 := h15755c.1
                              have p15755_1 := h15755c.2.1
                              have p15755_2 := h15755c.2.2.1
                              have p15755_3 := h15755c.2.2.2
                              linarith only [h15274, h15741, h15745, h15751, h15752, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p15755_1]
                            · have p15755_0 := h15755c.1
                              have p15755_1 := h15755c.2.1
                              have p15755_2 := h15755c.2.2.1
                              have p15755_3 := h15755c.2.2.2
                              linarith only [h15742, hlam, p15755_0]
                            · have p15755_0 := h15755c.1
                              have p15755_1 := h15755c.2.1
                              have p15755_2 := h15755c.2.2.1
                              have p15755_3 := h15755c.2.2.2
                              linarith only [hlam, p15755_0]
                            · have p15755_0 := h15755c.1
                              have p15755_1 := h15755c.2.1
                              have p15755_2 := h15755c.2.2.1
                              have p15755_3 := h15755c.2.2.2
                              linarith only [h11282, h15274, h15745, h15751, hc01, hc12, hlam, hphi, p15755_1]
                            · have p15755_0 := h15755c.1
                              have p15755_1 := h15755c.2.1
                              have p15755_2 := h15755c.2.2.1
                              have p15755_3 := h15755c.2.2.2
                              linarith only [h11844, h15741, h15745, hc01, hc12, hlam, hphi, p15755_1]
                            · have p15755_0 := h15755c.1
                              have p15755_1 := h15755c.2.1
                              have p15755_2 := h15755c.2.2.1
                              have p15755_3 := h15755c.2.2.2
                              linarith only [h15741, hlam, p15755_1]
                            · have p15755_0 := h15755c.1
                              have p15755_1 := h15755c.2.1
                              have p15755_2 := h15755c.2.2.1
                              have p15755_3 := h15755c.2.2.2
                              linarith only [h15743, hlam, p15755_0]
                            · have p15755_0 := h15755c.1
                              have p15755_1 := h15755c.2.1
                              have p15755_2 := h15755c.2.2.1
                              have p15755_3 := h15755c.2.2.2
                              linarith only [h15744, hlam, p15755_1]
                            · have p15755_0 := h15755c.1
                              have p15755_1 := h15755c.2.1
                              have p15755_2 := h15755c.2.2.1
                              have p15755_3 := h15755c.2.2.2
                              linarith only [hlam, p15755_0]
                          · linarith only [h15274, h15741, h15745, h15751, h15753, h15754, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h15274, h15744, h15753, hlam]
                      · linarith only [h11844, h15743, h15752, hlam]
                    · linarith only [h11844, h15742, h15751, hlam]
                  · linarith only [h15274, h15741, h15744, h15746, h15750, hlam]
                · linarith only [h15274, h15741, h15743, h15746, h15749, h6310, hc01, hc14, hlam, hphi]
              · linarith only [h11844, h15742, h15745, h15748, hlam]
            · linarith only [h11844, h15741, h15745, h15747, hlam]
          · linarith only [h11844, h15745, h15746, hc02, hc24, hlam, hphi]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h15790 | h15790
          · linarith only [h15274, h15745, h15790, hc02, hc23, hlam, hphi]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h15792 | h15792
            · rcases m.htr 1 3 4 (by decide) (by decide) with h15793 | h15793
              · rcases m.htr 1 3 5 (by decide) (by decide) with h15794 | h15794
                · rcases m.htr 1 4 5 (by decide) (by decide) with h15795 | h15795
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h15796 | h15796
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h15797 | h15797
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h15798 | h15798
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h15799 | h15799
                          · rcases h0bigk with h15800c | h15800c | h15800c | h15800c | h15800c | h15800c | h15800c | h15800c | h15800c | h15800c | h15800c | h15800c | h15800c | h15800c | h15800c | h15800c | h15800c | h15800c | h15800c | h15800c | h15800c | h15800c | h15800c | h15800c | h15800c
                            · have p15800_0 := h15800c.1
                              have p15800_1 := h15800c.2.1
                              have p15800_2 := h15800c.2.2.1
                              have p15800_3 := h15800c.2.2.2
                              linarith only [hlam, p15800_0]
                            · have p15800_0 := h15800c.1
                              have p15800_1 := h15800c.2.1
                              have p15800_2 := h15800c.2.2.1
                              have p15800_3 := h15800c.2.2.2
                              linarith only [h0, hlam, p15800_1]
                            · have p15800_0 := h15800c.1
                              have p15800_1 := h15800c.2.1
                              have p15800_2 := h15800c.2.2.1
                              have p15800_3 := h15800c.2.2.2
                              linarith only [h6310, hlam, p15800_0]
                            · have p15800_0 := h15800c.1
                              have p15800_1 := h15800c.2.1
                              have p15800_2 := h15800c.2.2.1
                              have p15800_3 := h15800c.2.2.2
                              linarith only [h9935, hlam, p15800_1]
                            · have p15800_0 := h15800c.1
                              have p15800_1 := h15800c.2.1
                              have p15800_2 := h15800c.2.2.1
                              have p15800_3 := h15800c.2.2.2
                              linarith only [h11282, hlam, p15800_1]
                            · have p15800_0 := h15800c.1
                              have p15800_1 := h15800c.2.1
                              have p15800_2 := h15800c.2.2.1
                              have p15800_3 := h15800c.2.2.2
                              linarith only [h0, h15790, h15796, hc01, hc23, hlam, hphi, ht12, p15800_1]
                            · have p15800_0 := h15800c.1
                              have p15800_1 := h15800c.2.1
                              have p15800_2 := h15800c.2.2.1
                              have p15800_3 := h15800c.2.2.2
                              linarith only [hlam, p15800_0]
                            · have p15800_0 := h15800c.1
                              have p15800_1 := h15800c.2.1
                              have p15800_2 := h15800c.2.2.1
                              have p15800_3 := h15800c.2.2.2
                              linarith only [h11844, hlam, p15800_0]
                            · have p15800_0 := h15800c.1
                              have p15800_1 := h15800c.2.1
                              have p15800_2 := h15800c.2.2.1
                              have p15800_3 := h15800c.2.2.2
                              linarith only [h15274, hlam, p15800_1]
                            · have p15800_0 := h15800c.1
                              have p15800_1 := h15800c.2.1
                              have p15800_2 := h15800c.2.2.1
                              have p15800_3 := h15800c.2.2.2
                              linarith only [h0, h11282, h15790, h15796, hc01, hc23, hlam, hphi, ht12, p15800_1]
                            · have p15800_0 := h15800c.1
                              have p15800_1 := h15800c.2.1
                              have p15800_2 := h15800c.2.2.1
                              have p15800_3 := h15800c.2.2.2
                              rcases p15800_3 (m.d 0 1) (by simp) with h15811 | h15811
                              · linarith only [h15811, h6310, hlam]
                              · rcases p15800_3 (m.d 0 2) (by simp) with h15813 | h15813
                                · linarith only [h11844, h15813, hlam]
                                · linarith only [h0, h15813, hlam]
                            · have p15800_0 := h15800c.1
                              have p15800_1 := h15800c.2.1
                              have p15800_2 := h15800c.2.2.1
                              have p15800_3 := h15800c.2.2.2
                              linarith only [h15741, h15797, h15799, hc45, hlam, hphi, ht0b, ht5b, p15800_1, u0elo2]
                            · have p15800_0 := h15800c.1
                              have p15800_1 := h15800c.2.1
                              have p15800_2 := h15800c.2.2.1
                              have p15800_3 := h15800c.2.2.2
                              linarith only [hlam, p15800_0]
                            · have p15800_0 := h15800c.1
                              have p15800_1 := h15800c.2.1
                              have p15800_2 := h15800c.2.2.1
                              have p15800_3 := h15800c.2.2.2
                              linarith only [h15274, h15741, h15797, h15799, hc45, hlam, hphi, ht0b, ht5b, p15800_1, u0elo2]
                            · have p15800_0 := h15800c.1
                              have p15800_1 := h15800c.2.1
                              have p15800_2 := h15800c.2.2.1
                              have p15800_3 := h15800c.2.2.2
                              rcases p15800_3 (m.d 0 1) (by simp) with h15819 | h15819
                              · linarith only [h15819, h6310, hlam]
                              · rcases p15800_3 (m.d 0 2) (by simp) with h15821 | h15821
                                · linarith only [h11844, h15821, hlam]
                                · linarith only [h15741, h15821, hlam]
                            · have p15800_0 := h15800c.1
                              have p15800_1 := h15800c.2.1
                              have p15800_2 := h15800c.2.2.1
                              have p15800_3 := h15800c.2.2.2
                              rcases p15800_3 (m.d 0 1) (by simp) with h15824 | h15824
                              · linarith only [h15824, h9935, hlam]
                              · rcases p15800_3 (m.d 0 2) (by simp) with h15826 | h15826
                                · linarith only [h15274, h15826, hlam]
                                · linarith only [h0, h15826, hlam]
                            · have p15800_0 := h15800c.1
                              have p15800_1 := h15800c.2.1
                              have p15800_2 := h15800c.2.2.1
                              have p15800_3 := h15800c.2.2.2
                              linarith only [h15741, h15797, h15799, hc45, hlam, hphi, ht0b, ht5b, p15800_1, u0elo3]
                            · have p15800_0 := h15800c.1
                              have p15800_1 := h15800c.2.1
                              have p15800_2 := h15800c.2.2.1
                              have p15800_3 := h15800c.2.2.2
                              linarith only [h15742, hlam, p15800_0]
                            · have p15800_0 := h15800c.1
                              have p15800_1 := h15800c.2.1
                              have p15800_2 := h15800c.2.2.1
                              have p15800_3 := h15800c.2.2.2
                              linarith only [hlam, p15800_0]
                            · have p15800_0 := h15800c.1
                              have p15800_1 := h15800c.2.1
                              have p15800_2 := h15800c.2.2.1
                              have p15800_3 := h15800c.2.2.2
                              rcases p15800_3 (m.d 0 1) (by simp) with h15832 | h15832
                              · linarith only [h15832, h9935, hlam]
                              · rcases p15800_3 (m.d 0 2) (by simp) with h15834 | h15834
                                · linarith only [h15274, h15834, hlam]
                                · linarith only [h15741, h15834, hlam]
                            · have p15800_0 := h15800c.1
                              have p15800_1 := h15800c.2.1
                              have p15800_2 := h15800c.2.2.1
                              have p15800_3 := h15800c.2.2.2
                              linarith only [h11844, h15741, hc01, hc23, hlam, hphi, ht12, p15800_1]
                            · have p15800_0 := h15800c.1
                              have p15800_1 := h15800c.2.1
                              have p15800_2 := h15800c.2.2.1
                              have p15800_3 := h15800c.2.2.2
                              linarith only [h15741, hlam, p15800_1]
                            · have p15800_0 := h15800c.1
                              have p15800_1 := h15800c.2.1
                              have p15800_2 := h15800c.2.2.1
                              have p15800_3 := h15800c.2.2.2
                              linarith only [h15743, hlam, p15800_0]
                            · have p15800_0 := h15800c.1
                              have p15800_1 := h15800c.2.1
                              have p15800_2 := h15800c.2.2.1
                              have p15800_3 := h15800c.2.2.2
                              linarith only [h15744, hlam, p15800_1]
                            · have p15800_0 := h15800c.1
                              have p15800_1 := h15800c.2.1
                              have p15800_2 := h15800c.2.2.1
                              have p15800_3 := h15800c.2.2.2
                              linarith only [hlam, p15800_0]
                          · rcases h0bigk with h15842c | h15842c | h15842c | h15842c | h15842c | h15842c | h15842c | h15842c | h15842c | h15842c | h15842c | h15842c | h15842c | h15842c | h15842c | h15842c | h15842c | h15842c | h15842c | h15842c | h15842c | h15842c | h15842c | h15842c | h15842c
                            · have p15842_0 := h15842c.1
                              have p15842_1 := h15842c.2.1
                              have p15842_2 := h15842c.2.2.1
                              have p15842_3 := h15842c.2.2.2
                              linarith only [hlam, p15842_0]
                            · have p15842_0 := h15842c.1
                              have p15842_1 := h15842c.2.1
                              have p15842_2 := h15842c.2.2.1
                              have p15842_3 := h15842c.2.2.2
                              linarith only [h0, hlam, p15842_1]
                            · have p15842_0 := h15842c.1
                              have p15842_1 := h15842c.2.1
                              have p15842_2 := h15842c.2.2.1
                              have p15842_3 := h15842c.2.2.2
                              linarith only [h6310, hlam, p15842_0]
                            · have p15842_0 := h15842c.1
                              have p15842_1 := h15842c.2.1
                              have p15842_2 := h15842c.2.2.1
                              have p15842_3 := h15842c.2.2.2
                              linarith only [h9935, hlam, p15842_1]
                            · have p15842_0 := h15842c.1
                              have p15842_1 := h15842c.2.1
                              have p15842_2 := h15842c.2.2.1
                              have p15842_3 := h15842c.2.2.2
                              linarith only [h11282, hlam, p15842_1]
                            · have p15842_0 := h15842c.1
                              have p15842_1 := h15842c.2.1
                              have p15842_2 := h15842c.2.2.1
                              have p15842_3 := h15842c.2.2.2
                              linarith only [h0, h15790, h15796, hc01, hc23, hlam, hphi, ht12, p15842_1]
                            · have p15842_0 := h15842c.1
                              have p15842_1 := h15842c.2.1
                              have p15842_2 := h15842c.2.2.1
                              have p15842_3 := h15842c.2.2.2
                              linarith only [hlam, p15842_0]
                            · have p15842_0 := h15842c.1
                              have p15842_1 := h15842c.2.1
                              have p15842_2 := h15842c.2.2.1
                              have p15842_3 := h15842c.2.2.2
                              linarith only [h11844, hlam, p15842_0]
                            · have p15842_0 := h15842c.1
                              have p15842_1 := h15842c.2.1
                              have p15842_2 := h15842c.2.2.1
                              have p15842_3 := h15842c.2.2.2
                              linarith only [h15274, hlam, p15842_1]
                            · have p15842_0 := h15842c.1
                              have p15842_1 := h15842c.2.1
                              have p15842_2 := h15842c.2.2.1
                              have p15842_3 := h15842c.2.2.2
                              linarith only [h0, h11282, h15790, h15796, hc01, hc23, hlam, hphi, ht12, p15842_1]
                            · have p15842_0 := h15842c.1
                              have p15842_1 := h15842c.2.1
                              have p15842_2 := h15842c.2.2.1
                              have p15842_3 := h15842c.2.2.2
                              rcases p15842_3 (m.d 0 1) (by simp) with h15853 | h15853
                              · linarith only [h15853, h6310, hlam]
                              · rcases p15842_3 (m.d 0 2) (by simp) with h15855 | h15855
                                · linarith only [h11844, h15855, hlam]
                                · linarith only [h0, h15855, hlam]
                            · have p15842_0 := h15842c.1
                              have p15842_1 := h15842c.2.1
                              have p15842_2 := h15842c.2.2.1
                              have p15842_3 := h15842c.2.2.2
                              linarith only [h15741, h15798, h15799, hc34, hlam, hphi, ht0b, ht45, ht5b, p15842_1, u0elo2]
                            · have p15842_0 := h15842c.1
                              have p15842_1 := h15842c.2.1
                              have p15842_2 := h15842c.2.2.1
                              have p15842_3 := h15842c.2.2.2
                              linarith only [hlam, p15842_0]
                            · have p15842_0 := h15842c.1
                              have p15842_1 := h15842c.2.1
                              have p15842_2 := h15842c.2.2.1
                              have p15842_3 := h15842c.2.2.2
                              linarith only [h15274, h15741, h15798, h15799, hc34, hlam, hphi, ht0b, ht45, ht5b, p15842_1, u0elo2]
                            · have p15842_0 := h15842c.1
                              have p15842_1 := h15842c.2.1
                              have p15842_2 := h15842c.2.2.1
                              have p15842_3 := h15842c.2.2.2
                              linarith only [h15741, h15798, h15799, hc34, hlam, hphi, ht0b, ht45, ht5b, p15842_1, u0elo2]
                            · have p15842_0 := h15842c.1
                              have p15842_1 := h15842c.2.1
                              have p15842_2 := h15842c.2.2.1
                              have p15842_3 := h15842c.2.2.2
                              rcases p15842_3 (m.d 0 1) (by simp) with h15862 | h15862
                              · linarith only [h15862, h9935, hlam]
                              · rcases p15842_3 (m.d 0 2) (by simp) with h15864 | h15864
                                · linarith only [h15274, h15864, hlam]
                                · linarith only [h0, h15864, hlam]
                            · have p15842_0 := h15842c.1
                              have p15842_1 := h15842c.2.1
                              have p15842_2 := h15842c.2.2.1
                              have p15842_3 := h15842c.2.2.2
                              linarith only [h15741, h15798, h15799, hc34, hlam, hphi, ht0b, ht45, ht5b, p15842_1, u0elo3]
                            · have p15842_0 := h15842c.1
                              have p15842_1 := h15842c.2.1
                              have p15842_2 := h15842c.2.2.1
                              have p15842_3 := h15842c.2.2.2
                              linarith only [h15742, hlam, p15842_0]
                            · have p15842_0 := h15842c.1
                              have p15842_1 := h15842c.2.1
                              have p15842_2 := h15842c.2.2.1
                              have p15842_3 := h15842c.2.2.2
                              linarith only [hlam, p15842_0]
                            · have p15842_0 := h15842c.1
                              have p15842_1 := h15842c.2.1
                              have p15842_2 := h15842c.2.2.1
                              have p15842_3 := h15842c.2.2.2
                              linarith only [h15741, h15742, h15798, h15799, hc34, hlam, hphi, ht0b, ht45, ht5b, p15842_1, u0elo2]
                            · have p15842_0 := h15842c.1
                              have p15842_1 := h15842c.2.1
                              have p15842_2 := h15842c.2.2.1
                              have p15842_3 := h15842c.2.2.2
                              linarith only [h11282, h15790, h15792, h15796, hc01, hc23, hlam, hphi, ht12, p15842_1]
                            · have p15842_0 := h15842c.1
                              have p15842_1 := h15842c.2.1
                              have p15842_2 := h15842c.2.2.1
                              have p15842_3 := h15842c.2.2.2
                              linarith only [h15741, hlam, p15842_1]
                            · have p15842_0 := h15842c.1
                              have p15842_1 := h15842c.2.1
                              have p15842_2 := h15842c.2.2.1
                              have p15842_3 := h15842c.2.2.2
                              linarith only [h15743, hlam, p15842_0]
                            · have p15842_0 := h15842c.1
                              have p15842_1 := h15842c.2.1
                              have p15842_2 := h15842c.2.2.1
                              have p15842_3 := h15842c.2.2.2
                              linarith only [h15744, hlam, p15842_1]
                            · have p15842_0 := h15842c.1
                              have p15842_1 := h15842c.2.1
                              have p15842_2 := h15842c.2.2.1
                              have p15842_3 := h15842c.2.2.2
                              linarith only [hlam, p15842_0]
                        · linarith only [h0, h15790, h15798, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h15743, h15745, h15797, h6310, hlam]
                    · linarith only [h11282, h15745, h15792, h15796, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h15744, h15795, h9935, hlam]
                · linarith only [h0, h15741, h15743, h15745, h15794, h6310, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h15742, h15793, h6310, hlam]
            · linarith only [h0, h15741, h15792, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
      · linarith only [h15274, h15741, h15744, hlam]
    · linarith only [h15274, h15741, h15742, h15743, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h15885 | h15885
    · rcases m.htr 0 4 5 (by decide) (by decide) with h15886 | h15886
      · rcases m.htr 1 2 3 (by decide) (by decide) with h15887 | h15887
        · rcases m.htr 1 2 4 (by decide) (by decide) with h15888 | h15888
          · rcases m.htr 1 2 5 (by decide) (by decide) with h15889 | h15889
            · rcases m.htr 1 3 4 (by decide) (by decide) with h15890 | h15890
              · rcases m.htr 1 3 5 (by decide) (by decide) with h15891 | h15891
                · rcases m.htr 1 4 5 (by decide) (by decide) with h15892 | h15892
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h15893 | h15893
                    · linarith only [h15742, h15885, h15887, h15893, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h11844, h15741, h15887, h15890, h15893, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h11844, h15741, h15886, h15892, h9935, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h11844, h15742, h15890, h15891, hc02, hc35, hlam, hphi, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h15898 | h15898
                · rcases m.htr 1 4 5 (by decide) (by decide) with h15899 | h15899
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h15900 | h15900
                    · linarith only [h15887, h15890, h15900, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h15902 | h15902
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h15903 | h15903
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h15904 | h15904
                          · rcases h0bigk with h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c
                            · have p15905_0 := h15905c.1
                              have p15905_1 := h15905c.2.1
                              have p15905_2 := h15905c.2.2.1
                              have p15905_3 := h15905c.2.2.2
                              linarith only [hlam, p15905_0]
                            · have p15905_0 := h15905c.1
                              have p15905_1 := h15905c.2.1
                              have p15905_2 := h15905c.2.2.1
                              have p15905_3 := h15905c.2.2.2
                              linarith only [h0, hlam, p15905_1]
                            · have p15905_0 := h15905c.1
                              have p15905_1 := h15905c.2.1
                              have p15905_2 := h15905c.2.2.1
                              have p15905_3 := h15905c.2.2.2
                              linarith only [h6310, hlam, p15905_0]
                            · have p15905_0 := h15905c.1
                              have p15905_1 := h15905c.2.1
                              have p15905_2 := h15905c.2.2.1
                              have p15905_3 := h15905c.2.2.2
                              linarith only [h9935, hlam, p15905_1]
                            · have p15905_0 := h15905c.1
                              have p15905_1 := h15905c.2.1
                              have p15905_2 := h15905c.2.2.1
                              have p15905_3 := h15905c.2.2.2
                              linarith only [h11282, hlam, p15905_1]
                            · have p15905_0 := h15905c.1
                              have p15905_1 := h15905c.2.1
                              have p15905_2 := h15905c.2.2.1
                              have p15905_3 := h15905c.2.2.2
                              linarith only [h11844, h15890, h6310, hc01, hc34, hlam, hphi, ht12, ht23, p15905_1]
                            · have p15905_0 := h15905c.1
                              have p15905_1 := h15905c.2.1
                              have p15905_2 := h15905c.2.2.1
                              have p15905_3 := h15905c.2.2.2
                              linarith only [hlam, p15905_0]
                            · have p15905_0 := h15905c.1
                              have p15905_1 := h15905c.2.1
                              have p15905_2 := h15905c.2.2.1
                              have p15905_3 := h15905c.2.2.2
                              linarith only [h11844, hlam, p15905_0]
                            · have p15905_0 := h15905c.1
                              have p15905_1 := h15905c.2.1
                              have p15905_2 := h15905c.2.2.1
                              have p15905_3 := h15905c.2.2.2
                              linarith only [h15274, hlam, p15905_1]
                            · have p15905_0 := h15905c.1
                              have p15905_1 := h15905c.2.1
                              have p15905_2 := h15905c.2.2.1
                              have p15905_3 := h15905c.2.2.2
                              linarith only [h11282, h11844, h15890, h6310, hc01, hc34, hlam, hphi, ht12, ht23, p15905_1]
                            · have p15905_0 := h15905c.1
                              have p15905_1 := h15905c.2.1
                              have p15905_2 := h15905c.2.2.1
                              have p15905_3 := h15905c.2.2.2
                              linarith only [h15890, h6310, hc01, hc34, hlam, hphi, ht12, ht23, p15905_1]
                            · have p15905_0 := h15905c.1
                              have p15905_1 := h15905c.2.1
                              have p15905_2 := h15905c.2.2.1
                              have p15905_3 := h15905c.2.2.2
                              linarith only [h15890, h6310, hc02, hc34, hlam, hphi, ht23, p15905_1]
                            · have p15905_0 := h15905c.1
                              have p15905_1 := h15905c.2.1
                              have p15905_2 := h15905c.2.2.1
                              have p15905_3 := h15905c.2.2.2
                              linarith only [hlam, p15905_0]
                            · have p15905_0 := h15905c.1
                              have p15905_1 := h15905c.2.1
                              have p15905_2 := h15905c.2.2.1
                              have p15905_3 := h15905c.2.2.2
                              linarith only [h15742, hlam, p15905_1]
                            · have p15905_0 := h15905c.1
                              have p15905_1 := h15905c.2.1
                              have p15905_2 := h15905c.2.2.1
                              have p15905_3 := h15905c.2.2.2
                              linarith only [h11282, h11844, h15887, h15890, hc01, hc34, hlam, hphi, ht12, ht23, p15905_1]
                            · have p15905_0 := h15905c.1
                              have p15905_1 := h15905c.2.1
                              have p15905_2 := h15905c.2.2.1
                              have p15905_3 := h15905c.2.2.2
                              linarith only [h15274, h15888, hc01, hc12, hlam, hphi, p15905_1]
                            · have p15905_0 := h15905c.1
                              have p15905_1 := h15905c.2.1
                              have p15905_2 := h15905c.2.2.1
                              have p15905_3 := h15905c.2.2.2
                              linarith only [h15274, h15741, h15888, h15902, h15904, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p15905_1]
                            · have p15905_0 := h15905c.1
                              have p15905_1 := h15905c.2.1
                              have p15905_2 := h15905c.2.2.1
                              have p15905_3 := h15905c.2.2.2
                              linarith only [h15274, h15888, h6310, hc01, hc12, hlam, hphi, p15905_1]
                            · have p15905_0 := h15905c.1
                              have p15905_1 := h15905c.2.1
                              have p15905_2 := h15905c.2.2.1
                              have p15905_3 := h15905c.2.2.2
                              linarith only [hlam, p15905_0]
                            · have p15905_0 := h15905c.1
                              have p15905_1 := h15905c.2.1
                              have p15905_2 := h15905c.2.2.1
                              have p15905_3 := h15905c.2.2.2
                              linarith only [h11282, h15274, h15888, hc01, hc12, hlam, hphi, p15905_1]
                            · have p15905_0 := h15905c.1
                              have p15905_1 := h15905c.2.1
                              have p15905_2 := h15905c.2.2.1
                              have p15905_3 := h15905c.2.2.2
                              linarith only [h11844, h15741, h15890, h6310, hc01, hc34, hlam, hphi, ht12, ht23, p15905_1]
                            · have p15905_0 := h15905c.1
                              have p15905_1 := h15905c.2.1
                              have p15905_2 := h15905c.2.2.1
                              have p15905_3 := h15905c.2.2.2
                              linarith only [h15741, hlam, p15905_1]
                            · have p15905_0 := h15905c.1
                              have p15905_1 := h15905c.2.1
                              have p15905_2 := h15905c.2.2.1
                              have p15905_3 := h15905c.2.2.2
                              linarith only [h15885, hlam, p15905_0]
                            · have p15905_0 := h15905c.1
                              have p15905_1 := h15905c.2.1
                              have p15905_2 := h15905c.2.2.1
                              have p15905_3 := h15905c.2.2.2
                              linarith only [h15886, hlam, p15905_1]
                            · have p15905_0 := h15905c.1
                              have p15905_1 := h15905c.2.1
                              have p15905_2 := h15905c.2.2.1
                              have p15905_3 := h15905c.2.2.2
                              linarith only [hlam, p15905_0]
                          · linarith only [h11844, h15887, h15890, h15904, hc02, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h15274, h15741, h15886, h15902, h15903, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                      · linarith only [h11844, h15741, h15885, h15902, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                  · linarith only [h11844, h15741, h15886, h15887, h15890, h15899, h9935, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h11844, h15741, h15885, h15887, h15898, hlam]
            · linarith only [h11844, h15741, h15889, hc12, hc23, hlam, hphi]
          · linarith only [h11282, h11844, h15741, h15887, h15888, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h15938 | h15938
          · linarith only [h11282, h15274, h15741, h15887, h15938, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h15940 | h15940
            · rcases m.htr 1 3 4 (by decide) (by decide) with h15941 | h15941
              · rcases m.htr 1 3 5 (by decide) (by decide) with h15942 | h15942
                · rcases m.htr 1 4 5 (by decide) (by decide) with h15943 | h15943
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h15944 | h15944
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h15945 | h15945
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h15946 | h15946
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h15947 | h15947
                          · rcases h0bigk with h15948c | h15948c | h15948c | h15948c | h15948c | h15948c | h15948c | h15948c | h15948c | h15948c | h15948c | h15948c | h15948c | h15948c | h15948c | h15948c | h15948c | h15948c | h15948c | h15948c | h15948c | h15948c | h15948c | h15948c | h15948c
                            · have p15948_0 := h15948c.1
                              have p15948_1 := h15948c.2.1
                              have p15948_2 := h15948c.2.2.1
                              have p15948_3 := h15948c.2.2.2
                              linarith only [hlam, p15948_0]
                            · have p15948_0 := h15948c.1
                              have p15948_1 := h15948c.2.1
                              have p15948_2 := h15948c.2.2.1
                              have p15948_3 := h15948c.2.2.2
                              linarith only [h0, hlam, p15948_1]
                            · have p15948_0 := h15948c.1
                              have p15948_1 := h15948c.2.1
                              have p15948_2 := h15948c.2.2.1
                              have p15948_3 := h15948c.2.2.2
                              linarith only [h6310, hlam, p15948_0]
                            · have p15948_0 := h15948c.1
                              have p15948_1 := h15948c.2.1
                              have p15948_2 := h15948c.2.2.1
                              have p15948_3 := h15948c.2.2.2
                              linarith only [h9935, hlam, p15948_1]
                            · have p15948_0 := h15948c.1
                              have p15948_1 := h15948c.2.1
                              have p15948_2 := h15948c.2.2.1
                              have p15948_3 := h15948c.2.2.2
                              linarith only [h11282, hlam, p15948_1]
                            · have p15948_0 := h15948c.1
                              have p15948_1 := h15948c.2.1
                              have p15948_2 := h15948c.2.2.1
                              have p15948_3 := h15948c.2.2.2
                              linarith only [h0, h15938, h15944, hc01, hc23, hlam, hphi, ht12, p15948_1]
                            · have p15948_0 := h15948c.1
                              have p15948_1 := h15948c.2.1
                              have p15948_2 := h15948c.2.2.1
                              have p15948_3 := h15948c.2.2.2
                              linarith only [hlam, p15948_0]
                            · have p15948_0 := h15948c.1
                              have p15948_1 := h15948c.2.1
                              have p15948_2 := h15948c.2.2.1
                              have p15948_3 := h15948c.2.2.2
                              linarith only [h11844, hlam, p15948_0]
                            · have p15948_0 := h15948c.1
                              have p15948_1 := h15948c.2.1
                              have p15948_2 := h15948c.2.2.1
                              have p15948_3 := h15948c.2.2.2
                              linarith only [h15274, hlam, p15948_1]
                            · have p15948_0 := h15948c.1
                              have p15948_1 := h15948c.2.1
                              have p15948_2 := h15948c.2.2.1
                              have p15948_3 := h15948c.2.2.2
                              linarith only [h0, h11282, h15938, h15944, hc01, hc23, hlam, hphi, ht12, p15948_1]
                            · have p15948_0 := h15948c.1
                              have p15948_1 := h15948c.2.1
                              have p15948_2 := h15948c.2.2.1
                              have p15948_3 := h15948c.2.2.2
                              linarith only [h15742, h15887, h15941, hc01, hc23, hlam, hphi, ht12, p15948_1]
                            · have p15948_0 := h15948c.1
                              have p15948_1 := h15948c.2.1
                              have p15948_2 := h15948c.2.2.1
                              have p15948_3 := h15948c.2.2.2
                              linarith only [h15742, h15887, h15941, hc02, hc23, hlam, hphi, p15948_1]
                            · have p15948_0 := h15948c.1
                              have p15948_1 := h15948c.2.1
                              have p15948_2 := h15948c.2.2.1
                              have p15948_3 := h15948c.2.2.2
                              linarith only [hlam, p15948_0]
                            · have p15948_0 := h15948c.1
                              have p15948_1 := h15948c.2.1
                              have p15948_2 := h15948c.2.2.1
                              have p15948_3 := h15948c.2.2.2
                              linarith only [h15742, hlam, p15948_1]
                            · have p15948_0 := h15948c.1
                              have p15948_1 := h15948c.2.1
                              have p15948_2 := h15948c.2.2.1
                              have p15948_3 := h15948c.2.2.2
                              linarith only [h11282, h15742, h15887, h15941, hc01, hc23, hlam, hphi, ht12, p15948_1]
                            · have p15948_0 := h15948c.1
                              have p15948_1 := h15948c.2.1
                              have p15948_2 := h15948c.2.2.1
                              have p15948_3 := h15948c.2.2.2
                              linarith only [h15742, h15887, h15941, hc01, hc23, hlam, hphi, ht12, p15948_1]
                            · have p15948_0 := h15948c.1
                              have p15948_1 := h15948c.2.1
                              have p15948_2 := h15948c.2.2.1
                              have p15948_3 := h15948c.2.2.2
                              linarith only [h15741, h15742, h15887, h15941, h15945, h15947, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p15948_1]
                            · have p15948_0 := h15948c.1
                              have p15948_1 := h15948c.2.1
                              have p15948_2 := h15948c.2.2.1
                              have p15948_3 := h15948c.2.2.2
                              linarith only [h15742, h15887, h15941, h6310, hc01, hc23, hlam, hphi, ht12, p15948_1]
                            · have p15948_0 := h15948c.1
                              have p15948_1 := h15948c.2.1
                              have p15948_2 := h15948c.2.2.1
                              have p15948_3 := h15948c.2.2.2
                              linarith only [hlam, p15948_0]
                            · have p15948_0 := h15948c.1
                              have p15948_1 := h15948c.2.1
                              have p15948_2 := h15948c.2.2.1
                              have p15948_3 := h15948c.2.2.2
                              linarith only [h11282, h15742, h15887, h15941, hc01, hc23, hlam, hphi, ht12, p15948_1]
                            · have p15948_0 := h15948c.1
                              have p15948_1 := h15948c.2.1
                              have p15948_2 := h15948c.2.2.1
                              have p15948_3 := h15948c.2.2.2
                              linarith only [h0, h15741, h15938, h15944, hc01, hc23, hlam, hphi, ht12, p15948_1]
                            · have p15948_0 := h15948c.1
                              have p15948_1 := h15948c.2.1
                              have p15948_2 := h15948c.2.2.1
                              have p15948_3 := h15948c.2.2.2
                              linarith only [h15741, hlam, p15948_1]
                            · have p15948_0 := h15948c.1
                              have p15948_1 := h15948c.2.1
                              have p15948_2 := h15948c.2.2.1
                              have p15948_3 := h15948c.2.2.2
                              linarith only [h15885, hlam, p15948_0]
                            · have p15948_0 := h15948c.1
                              have p15948_1 := h15948c.2.1
                              have p15948_2 := h15948c.2.2.1
                              have p15948_3 := h15948c.2.2.2
                              linarith only [h15886, hlam, p15948_1]
                            · have p15948_0 := h15948c.1
                              have p15948_1 := h15948c.2.1
                              have p15948_2 := h15948c.2.2.1
                              have p15948_3 := h15948c.2.2.2
                              linarith only [hlam, p15948_0]
                          · linarith only [h15742, h15886, h15947, hlam]
                        · linarith only [h11844, h15741, h15742, h15886, h15938, h15946, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h11844, h15741, h15742, h15887, h15941, h15945, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h15887, h15941, h15944, hlam]
                  · linarith only [h11844, h15741, h15742, h15886, h15941, h15943, hlam]
                · linarith only [h15742, h15885, h15941, h15942, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h15980 | h15980
                · rcases m.htr 1 4 5 (by decide) (by decide) with h15981 | h15981
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h15982 | h15982
                    · linarith only [h11282, h15887, h15940, h15941, h15982, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h11282, h15887, h15940, h15982, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h15741, h15886, h15887, h15981, h9935, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h15742, h15885, h15887, h15980, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
            · linarith only [h0, h15741, h15940, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
      · linarith only [h11844, h15741, h15742, h15886, hlam]
    · linarith only [h11844, h15741, h15885, hlam]

end R2N4
