import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10998000 in
set_option maxHeartbeats 10998000 in
theorem r1l7_11_25_L_0_H_I_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3355 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h1elo := hb1.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h3356 | h3356
  · rcases m.htr 0 2 5 (by decide) (by decide) with h3357 | h3357
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3358 | h3358
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3359 | h3359
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3360 | h3360
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3361 | h3361
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3362 | h3362
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3363 | h3363
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3364 | h3364
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3365 | h3365
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3366 | h3366
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3367 | h3367
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3368 | h3368
                          · rcases h5bigk with h3369c | h3369c | h3369c | h3369c | h3369c | h3369c | h3369c | h3369c | h3369c | h3369c | h3369c | h3369c | h3369c | h3369c | h3369c | h3369c | h3369c | h3369c | h3369c | h3369c | h3369c | h3369c | h3369c | h3369c | h3369c
                            · have p3369_0 := h3369c.1
                              have p3369_1 := h3369c.2.1
                              have p3369_2 := h3369c.2.2.1
                              have p3369_3 := h3369c.2.2.2
                              linarith only [hlam, p3369_0]
                            · have p3369_0 := h3369c.1
                              have p3369_1 := h3369c.2.1
                              have p3369_2 := h3369c.2.2.1
                              have p3369_3 := h3369c.2.2.2
                              linarith only [h0, h3355, h3360, hc15, hlam, hphi, ht01, ht0b, ht5b, p3369_1, u1elo1]
                            · have p3369_0 := h3369c.1
                              have p3369_1 := h3369c.2.1
                              have p3369_2 := h3369c.2.2.1
                              have p3369_3 := h3369c.2.2.2
                              linarith only [h0, h3355, h3360, hc25, hlam, hphi, ht01, ht0b, ht5b, p3369_1, u1elo1]
                            · have p3369_0 := h3369c.1
                              have p3369_1 := h3369c.2.1
                              have p3369_2 := h3369c.2.2.1
                              have p3369_3 := h3369c.2.2.2
                              linarith only [h0, h3355, h3360, hc35, hlam, hphi, ht01, ht0b, ht5b, p3369_1, u1elo1]
                            · have p3369_0 := h3369c.1
                              have p3369_1 := h3369c.2.1
                              have p3369_2 := h3369c.2.2.1
                              have p3369_3 := h3369c.2.2.2
                              linarith only [h0, h3355, h3360, hc45, hlam, hphi, ht01, ht0b, ht5b, p3369_1, u1elo1]
                            · have p3369_0 := h3369c.1
                              have p3369_1 := h3369c.2.1
                              have p3369_2 := h3369c.2.2.1
                              have p3369_3 := h3369c.2.2.2
                              linarith only [h3355, hlam, p3369_0]
                            · have p3369_0 := h3369c.1
                              have p3369_1 := h3369c.2.1
                              have p3369_2 := h3369c.2.2.1
                              have p3369_3 := h3369c.2.2.2
                              linarith only [hlam, p3369_0]
                            · have p3369_0 := h3369c.1
                              have p3369_1 := h3369c.2.1
                              have p3369_2 := h3369c.2.2.1
                              have p3369_3 := h3369c.2.2.2
                              linarith only [hc25, hlam, hphi, ht01, ht0b, ht5b, p3369_1, u1elo4]
                            · have p3369_0 := h3369c.1
                              have p3369_1 := h3369c.2.1
                              have p3369_2 := h3369c.2.2.1
                              have p3369_3 := h3369c.2.2.2
                              linarith only [h0, h3355, h3360, hc35, hlam, hphi, ht01, ht0b, ht5b, p3369_1, u1elo1]
                            · have p3369_0 := h3369c.1
                              have p3369_1 := h3369c.2.1
                              have p3369_2 := h3369c.2.2.1
                              have p3369_3 := h3369c.2.2.2
                              linarith only [h0, h3355, h3360, hc45, hlam, hphi, ht01, ht0b, ht5b, p3369_1, u1elo1]
                            · have p3369_0 := h3369c.1
                              have p3369_1 := h3369c.2.1
                              have p3369_2 := h3369c.2.2.1
                              have p3369_3 := h3369c.2.2.2
                              linarith only [h3357, hlam, p3369_1]
                            · have p3369_0 := h3369c.1
                              have p3369_1 := h3369c.2.1
                              have p3369_2 := h3369c.2.2.1
                              have p3369_3 := h3369c.2.2.2
                              linarith only [h3361, hlam, p3369_1]
                            · have p3369_0 := h3369c.1
                              have p3369_1 := h3369c.2.1
                              have p3369_2 := h3369c.2.2.1
                              have p3369_3 := h3369c.2.2.2
                              linarith only [hlam, p3369_0]
                            · have p3369_0 := h3369c.1
                              have p3369_1 := h3369c.2.1
                              have p3369_2 := h3369c.2.2.1
                              have p3369_3 := h3369c.2.2.2
                              linarith only [h3357, hc02, hc35, hlam, hphi, ht0b, ht5b, p3369_1]
                            · have p3369_0 := h3369c.1
                              have p3369_1 := h3369c.2.1
                              have p3369_2 := h3369c.2.2.1
                              have p3369_3 := h3369c.2.2.2
                              linarith only [h0, h3355, h3360, h3361, hc45, hlam, hphi, ht01, ht0b, ht5b, p3369_1, u1elo1]
                            · have p3369_0 := h3369c.1
                              have p3369_1 := h3369c.2.1
                              have p3369_2 := h3369c.2.2.1
                              have p3369_3 := h3369c.2.2.2
                              linarith only [h3358, hlam, p3369_0]
                            · have p3369_0 := h3369c.1
                              have p3369_1 := h3369c.2.1
                              have p3369_2 := h3369c.2.2.1
                              have p3369_3 := h3369c.2.2.2
                              linarith only [h3363, hlam, p3369_0]
                            · have p3369_0 := h3369c.1
                              have p3369_1 := h3369c.2.1
                              have p3369_2 := h3369c.2.2.1
                              have p3369_3 := h3369c.2.2.2
                              linarith only [h3366, hlam, p3369_0]
                            · have p3369_0 := h3369c.1
                              have p3369_1 := h3369c.2.1
                              have p3369_2 := h3369c.2.2.1
                              have p3369_3 := h3369c.2.2.2
                              linarith only [hlam, p3369_0]
                            · have p3369_0 := h3369c.1
                              have p3369_1 := h3369c.2.1
                              have p3369_2 := h3369c.2.2.1
                              have p3369_3 := h3369c.2.2.2
                              linarith only [h3358, hc03, hc45, hlam, hphi, ht0b, ht5b, p3369_1]
                            · have p3369_0 := h3369c.1
                              have p3369_1 := h3369c.2.1
                              have p3369_2 := h3369c.2.2.1
                              have p3369_3 := h3369c.2.2.2
                              linarith only [h3359, hlam, p3369_0]
                            · have p3369_0 := h3369c.1
                              have p3369_1 := h3369c.2.1
                              have p3369_2 := h3369c.2.2.1
                              have p3369_3 := h3369c.2.2.2
                              linarith only [h3364, hlam, p3369_0]
                            · have p3369_0 := h3369c.1
                              have p3369_1 := h3369c.2.1
                              have p3369_2 := h3369c.2.2.1
                              have p3369_3 := h3369c.2.2.2
                              linarith only [h3367, hlam, p3369_0]
                            · have p3369_0 := h3369c.1
                              have p3369_1 := h3369c.2.1
                              have p3369_2 := h3369c.2.2.1
                              have p3369_3 := h3369c.2.2.2
                              linarith only [h3368, hlam, p3369_0]
                            · have p3369_0 := h3369c.1
                              have p3369_1 := h3369c.2.1
                              have p3369_2 := h3369c.2.2.1
                              have p3369_3 := h3369c.2.2.2
                              linarith only [hlam, p3369_0]
                          · linarith only [h0, h3355, h3360, h3364, h3368, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · linarith only [h0, h3355, h3360, h3364, h3365, h3367, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · linarith only [h0, h3355, h3360, h3363, h3366, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3398 | h3398
                      · linarith only [h3362, h3365, h3398, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                      · linarith only [h0, h3355, h3360, h3363, h3398, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                  · linarith only [h0, h3359, h3364, hlam]
                · linarith only [h0, h3355, h3358, h3360, h3362, h3363, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3403 | h3403
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3404 | h3404
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3405 | h3405
                    · linarith only [h0, h3356, h3362, h3405, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3407 | h3407
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3408 | h3408
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3409 | h3409
                          · rcases h5bigk with h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c | h3410c
                            · have p3410_0 := h3410c.1
                              have p3410_1 := h3410c.2.1
                              have p3410_2 := h3410c.2.2.1
                              have p3410_3 := h3410c.2.2.2
                              linarith only [hlam, p3410_0]
                            · have p3410_0 := h3410c.1
                              have p3410_1 := h3410c.2.1
                              have p3410_2 := h3410c.2.2.1
                              have p3410_3 := h3410c.2.2.2
                              linarith only [h0, h3355, h3360, hc15, hlam, hphi, ht01, ht0b, ht5b, p3410_1, u1elo1]
                            · have p3410_0 := h3410c.1
                              have p3410_1 := h3410c.2.1
                              have p3410_2 := h3410c.2.2.1
                              have p3410_3 := h3410c.2.2.2
                              linarith only [h0, h3355, h3360, h3407, h3409, hc45, hlam, hphi, ht01, ht0b, ht5b, p3410_1, u1elo1]
                            · have p3410_0 := h3410c.1
                              have p3410_1 := h3410c.2.1
                              have p3410_2 := h3410c.2.2.1
                              have p3410_3 := h3410c.2.2.2
                              linarith only [h0, h3355, h3360, h3409, hc45, hlam, hphi, ht01, ht0b, ht5b, p3410_1, u1elo1]
                            · have p3410_0 := h3410c.1
                              have p3410_1 := h3410c.2.1
                              have p3410_2 := h3410c.2.2.1
                              have p3410_3 := h3410c.2.2.2
                              linarith only [h0, h3355, h3360, hc45, hlam, hphi, ht01, ht0b, ht5b, p3410_1, u1elo1]
                            · have p3410_0 := h3410c.1
                              have p3410_1 := h3410c.2.1
                              have p3410_2 := h3410c.2.2.1
                              have p3410_3 := h3410c.2.2.2
                              linarith only [h3355, hlam, p3410_0]
                            · have p3410_0 := h3410c.1
                              have p3410_1 := h3410c.2.1
                              have p3410_2 := h3410c.2.2.1
                              have p3410_3 := h3410c.2.2.2
                              linarith only [hlam, p3410_0]
                            · have p3410_0 := h3410c.1
                              have p3410_1 := h3410c.2.1
                              have p3410_2 := h3410c.2.2.1
                              have p3410_3 := h3410c.2.2.2
                              linarith only [h3407, h3409, hc45, hlam, hphi, ht01, ht0b, ht5b, p3410_1, u1elo4]
                            · have p3410_0 := h3410c.1
                              have p3410_1 := h3410c.2.1
                              have p3410_2 := h3410c.2.2.1
                              have p3410_3 := h3410c.2.2.2
                              linarith only [h0, h3355, h3360, h3409, hc45, hlam, hphi, ht01, ht0b, ht5b, p3410_1, u1elo1]
                            · have p3410_0 := h3410c.1
                              have p3410_1 := h3410c.2.1
                              have p3410_2 := h3410c.2.2.1
                              have p3410_3 := h3410c.2.2.2
                              linarith only [h0, h3355, h3360, hc45, hlam, hphi, ht01, ht0b, ht5b, p3410_1, u1elo1]
                            · have p3410_0 := h3410c.1
                              have p3410_1 := h3410c.2.1
                              have p3410_2 := h3410c.2.2.1
                              have p3410_3 := h3410c.2.2.2
                              linarith only [h3357, hlam, p3410_1]
                            · have p3410_0 := h3410c.1
                              have p3410_1 := h3410c.2.1
                              have p3410_2 := h3410c.2.2.1
                              have p3410_3 := h3410c.2.2.2
                              linarith only [h3361, hlam, p3410_1]
                            · have p3410_0 := h3410c.1
                              have p3410_1 := h3410c.2.1
                              have p3410_2 := h3410c.2.2.1
                              have p3410_3 := h3410c.2.2.2
                              linarith only [hlam, p3410_0]
                            · have p3410_0 := h3410c.1
                              have p3410_1 := h3410c.2.1
                              have p3410_2 := h3410c.2.2.1
                              have p3410_3 := h3410c.2.2.2
                              linarith only [h3357, h3409, hc02, hc45, hlam, hphi, ht0b, ht5b, p3410_1]
                            · have p3410_0 := h3410c.1
                              have p3410_1 := h3410c.2.1
                              have p3410_2 := h3410c.2.2.1
                              have p3410_3 := h3410c.2.2.2
                              linarith only [h0, h3355, h3360, h3361, hc45, hlam, hphi, ht01, ht0b, ht5b, p3410_1, u1elo1]
                            · have p3410_0 := h3410c.1
                              have p3410_1 := h3410c.2.1
                              have p3410_2 := h3410c.2.2.1
                              have p3410_3 := h3410c.2.2.2
                              linarith only [h3358, hlam, p3410_0]
                            · have p3410_0 := h3410c.1
                              have p3410_1 := h3410c.2.1
                              have p3410_2 := h3410c.2.2.1
                              have p3410_3 := h3410c.2.2.2
                              linarith only [h3403, hlam, p3410_0]
                            · have p3410_0 := h3410c.1
                              have p3410_1 := h3410c.2.1
                              have p3410_2 := h3410c.2.2.1
                              have p3410_3 := h3410c.2.2.2
                              linarith only [h3407, hlam, p3410_0]
                            · have p3410_0 := h3410c.1
                              have p3410_1 := h3410c.2.1
                              have p3410_2 := h3410c.2.2.1
                              have p3410_3 := h3410c.2.2.2
                              linarith only [hlam, p3410_0]
                            · have p3410_0 := h3410c.1
                              have p3410_1 := h3410c.2.1
                              have p3410_2 := h3410c.2.2.1
                              have p3410_3 := h3410c.2.2.2
                              linarith only [h3403, hc45, hlam, hphi, ht01, ht0b, ht5b, p3410_1, u1elo2]
                            · have p3410_0 := h3410c.1
                              have p3410_1 := h3410c.2.1
                              have p3410_2 := h3410c.2.2.1
                              have p3410_3 := h3410c.2.2.2
                              linarith only [h3359, hlam, p3410_0]
                            · have p3410_0 := h3410c.1
                              have p3410_1 := h3410c.2.1
                              have p3410_2 := h3410c.2.2.1
                              have p3410_3 := h3410c.2.2.2
                              linarith only [h3404, hlam, p3410_0]
                            · have p3410_0 := h3410c.1
                              have p3410_1 := h3410c.2.1
                              have p3410_2 := h3410c.2.2.1
                              have p3410_3 := h3410c.2.2.2
                              linarith only [h3408, hlam, p3410_0]
                            · have p3410_0 := h3410c.1
                              have p3410_1 := h3410c.2.1
                              have p3410_2 := h3410c.2.2.1
                              have p3410_3 := h3410c.2.2.2
                              linarith only [h3409, hlam, p3410_0]
                            · have p3410_0 := h3410c.1
                              have p3410_1 := h3410c.2.1
                              have p3410_2 := h3410c.2.2.1
                              have p3410_3 := h3410c.2.2.2
                              linarith only [hlam, p3410_0]
                          · linarith only [h0, h3359, h3362, h3409, hlam]
                        · linarith only [h0, h3355, h3360, h3404, h3405, h3408, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · linarith only [h3362, h3403, h3407, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h3359, h3404, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3440 | h3440
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3441 | h3441
                    · linarith only [h0, h3356, h3362, h3441, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3443 | h3443
                      · linarith only [h3360, h3403, h3441, h3443, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3445 | h3445
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3446 | h3446
                          · rcases h5bigk with h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c
                            · have p3447_0 := h3447c.1
                              have p3447_1 := h3447c.2.1
                              have p3447_2 := h3447c.2.2.1
                              have p3447_3 := h3447c.2.2.2
                              linarith only [hlam, p3447_0]
                            · have p3447_0 := h3447c.1
                              have p3447_1 := h3447c.2.1
                              have p3447_2 := h3447c.2.2.1
                              have p3447_3 := h3447c.2.2.2
                              linarith only [h0, h3355, h3360, hc15, hlam, hphi, ht01, ht0b, ht5b, p3447_1, u1elo1]
                            · have p3447_0 := h3447c.1
                              have p3447_1 := h3447c.2.1
                              have p3447_2 := h3447c.2.2.1
                              have p3447_3 := h3447c.2.2.2
                              linarith only [h0, h3355, h3360, h3445, hc45, hlam, hphi, ht01, ht0b, ht5b, p3447_1, u1elo1]
                            · have p3447_0 := h3447c.1
                              have p3447_1 := h3447c.2.1
                              have p3447_2 := h3447c.2.2.1
                              have p3447_3 := h3447c.2.2.2
                              linarith only [h0, h3355, h3360, h3403, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3447_1, u1elo1]
                            · have p3447_0 := h3447c.1
                              have p3447_1 := h3447c.2.1
                              have p3447_2 := h3447c.2.2.1
                              have p3447_3 := h3447c.2.2.2
                              linarith only [h0, h3355, h3360, hc45, hlam, hphi, ht01, ht0b, ht5b, p3447_1, u1elo1]
                            · have p3447_0 := h3447c.1
                              have p3447_1 := h3447c.2.1
                              have p3447_2 := h3447c.2.2.1
                              have p3447_3 := h3447c.2.2.2
                              linarith only [h3355, hlam, p3447_0]
                            · have p3447_0 := h3447c.1
                              have p3447_1 := h3447c.2.1
                              have p3447_2 := h3447c.2.2.1
                              have p3447_3 := h3447c.2.2.2
                              linarith only [hlam, p3447_0]
                            · have p3447_0 := h3447c.1
                              have p3447_1 := h3447c.2.1
                              have p3447_2 := h3447c.2.2.1
                              have p3447_3 := h3447c.2.2.2
                              linarith only [h3445, hc45, hlam, hphi, ht01, ht0b, ht5b, p3447_1, u1elo4]
                            · have p3447_0 := h3447c.1
                              have p3447_1 := h3447c.2.1
                              have p3447_2 := h3447c.2.2.1
                              have p3447_3 := h3447c.2.2.2
                              linarith only [h3403, hlam, p3447_1]
                            · have p3447_0 := h3447c.1
                              have p3447_1 := h3447c.2.1
                              have p3447_2 := h3447c.2.2.1
                              have p3447_3 := h3447c.2.2.2
                              linarith only [h0, h3355, h3360, hc45, hlam, hphi, ht01, ht0b, ht5b, p3447_1, u1elo1]
                            · have p3447_0 := h3447c.1
                              have p3447_1 := h3447c.2.1
                              have p3447_2 := h3447c.2.2.1
                              have p3447_3 := h3447c.2.2.2
                              linarith only [h3357, hlam, p3447_1]
                            · have p3447_0 := h3447c.1
                              have p3447_1 := h3447c.2.1
                              have p3447_2 := h3447c.2.2.1
                              have p3447_3 := h3447c.2.2.2
                              linarith only [h3361, hlam, p3447_1]
                            · have p3447_0 := h3447c.1
                              have p3447_1 := h3447c.2.1
                              have p3447_2 := h3447c.2.2.1
                              have p3447_3 := h3447c.2.2.2
                              linarith only [hlam, p3447_0]
                            · have p3447_0 := h3447c.1
                              have p3447_1 := h3447c.2.1
                              have p3447_2 := h3447c.2.2.1
                              have p3447_3 := h3447c.2.2.2
                              linarith only [h3443, hlam, p3447_1]
                            · have p3447_0 := h3447c.1
                              have p3447_1 := h3447c.2.1
                              have p3447_2 := h3447c.2.2.1
                              have p3447_3 := h3447c.2.2.2
                              linarith only [h3357, hc02, hc45, hlam, hphi, ht0b, ht5b, p3447_1]
                            · have p3447_0 := h3447c.1
                              have p3447_1 := h3447c.2.1
                              have p3447_2 := h3447c.2.2.1
                              have p3447_3 := h3447c.2.2.2
                              linarith only [h3358, hlam, p3447_0]
                            · have p3447_0 := h3447c.1
                              have p3447_1 := h3447c.2.1
                              have p3447_2 := h3447c.2.2.1
                              have p3447_3 := h3447c.2.2.2
                              linarith only [h3358, hc03, hc15, hlam, hphi, ht0b, ht5b, p3447_1]
                            · have p3447_0 := h3447c.1
                              have p3447_1 := h3447c.2.1
                              have p3447_2 := h3447c.2.2.1
                              have p3447_3 := h3447c.2.2.2
                              linarith only [h0, h3355, h3358, h3360, hc25, hlam, hphi, ht01, ht0b, ht5b, p3447_1, u1elo1]
                            · have p3447_0 := h3447c.1
                              have p3447_1 := h3447c.2.1
                              have p3447_2 := h3447c.2.2.1
                              have p3447_3 := h3447c.2.2.2
                              linarith only [hlam, p3447_0]
                            · have p3447_0 := h3447c.1
                              have p3447_1 := h3447c.2.1
                              have p3447_2 := h3447c.2.2.1
                              have p3447_3 := h3447c.2.2.2
                              linarith only [h0, h3355, h3358, h3360, hc45, hlam, hphi, ht01, ht0b, ht5b, p3447_1, u1elo1]
                            · have p3447_0 := h3447c.1
                              have p3447_1 := h3447c.2.1
                              have p3447_2 := h3447c.2.2.1
                              have p3447_3 := h3447c.2.2.2
                              linarith only [h3359, hlam, p3447_0]
                            · have p3447_0 := h3447c.1
                              have p3447_1 := h3447c.2.1
                              have p3447_2 := h3447c.2.2.1
                              have p3447_3 := h3447c.2.2.2
                              linarith only [h3440, hlam, p3447_0]
                            · have p3447_0 := h3447c.1
                              have p3447_1 := h3447c.2.1
                              have p3447_2 := h3447c.2.2.1
                              have p3447_3 := h3447c.2.2.2
                              linarith only [h3445, hlam, p3447_0]
                            · have p3447_0 := h3447c.1
                              have p3447_1 := h3447c.2.1
                              have p3447_2 := h3447c.2.2.1
                              have p3447_3 := h3447c.2.2.2
                              linarith only [h3446, hlam, p3447_0]
                            · have p3447_0 := h3447c.1
                              have p3447_1 := h3447c.2.1
                              have p3447_2 := h3447c.2.2.1
                              have p3447_3 := h3447c.2.2.2
                              linarith only [hlam, p3447_0]
                          · linarith only [h0, h3355, h3358, h3362, h3443, h3446, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h0, h3355, h3360, h3440, h3445, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · linarith only [h0, h3359, h3440, hlam]
            · linarith only [h0, h3355, h3357, h3360, h3361, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
          · linarith only [h0, h3356, h3360, hlam]
        · linarith only [h0, h3355, h3359, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3479 | h3479
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3480 | h3480
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3481 | h3481
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3482 | h3482
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3483 | h3483
                · linarith only [h0, h3355, h3358, h3480, h3483, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                · linarith only [h0, h3355, h3482, h3483, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3486 | h3486
                · linarith only [h3358, h3482, h3486, hc03, hc34, hlam, hphi]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3488 | h3488
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3489 | h3489
                    · linarith only [h0, h3356, h3482, h3489, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3491 | h3491
                      · linarith only [h3486, h3489, h3491, hc13, hc34, hlam, hphi]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3493 | h3493
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3494 | h3494
                          · rcases h5bigk with h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c | h3495c
                            · have p3495_0 := h3495c.1
                              have p3495_1 := h3495c.2.1
                              have p3495_2 := h3495c.2.2.1
                              have p3495_3 := h3495c.2.2.2
                              linarith only [hlam, p3495_0]
                            · have p3495_0 := h3495c.1
                              have p3495_1 := h3495c.2.1
                              have p3495_2 := h3495c.2.2.1
                              have p3495_3 := h3495c.2.2.2
                              linarith only [h0, h3355, h3481, h3491, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3495_1, u1elo3]
                            · have p3495_0 := h3495c.1
                              have p3495_1 := h3495c.2.1
                              have p3495_2 := h3495c.2.2.1
                              have p3495_3 := h3495c.2.2.2
                              linarith only [h0, h3355, h3491, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3495_1, u1elo3]
                            · have p3495_0 := h3495c.1
                              have p3495_1 := h3495c.2.1
                              have p3495_2 := h3495c.2.2.1
                              have p3495_3 := h3495c.2.2.2
                              linarith only [h3358, hlam, p3495_1]
                            · have p3495_0 := h3495c.1
                              have p3495_1 := h3495c.2.1
                              have p3495_2 := h3495c.2.2.1
                              have p3495_3 := h3495c.2.2.2
                              linarith only [h0, h3355, hc45, hlam, hphi, ht01, ht0b, ht5b, p3495_1, u1elo3]
                            · have p3495_0 := h3495c.1
                              have p3495_1 := h3495c.2.1
                              have p3495_2 := h3495c.2.2.1
                              have p3495_3 := h3495c.2.2.2
                              linarith only [h3355, hlam, p3495_0]
                            · have p3495_0 := h3495c.1
                              have p3495_1 := h3495c.2.1
                              have p3495_2 := h3495c.2.2.1
                              have p3495_3 := h3495c.2.2.2
                              linarith only [hlam, p3495_0]
                            · have p3495_0 := h3495c.1
                              have p3495_1 := h3495c.2.1
                              have p3495_2 := h3495c.2.2.1
                              have p3495_3 := h3495c.2.2.2
                              linarith only [h3491, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3495_1, u1elo4]
                            · have p3495_0 := h3495c.1
                              have p3495_1 := h3495c.2.1
                              have p3495_2 := h3495c.2.2.1
                              have p3495_3 := h3495c.2.2.2
                              linarith only [h3486, hlam, p3495_1]
                            · have p3495_0 := h3495c.1
                              have p3495_1 := h3495c.2.1
                              have p3495_2 := h3495c.2.2.1
                              have p3495_3 := h3495c.2.2.2
                              linarith only [h0, h3355, h3480, hc45, hlam, hphi, ht01, ht0b, ht5b, p3495_1, u1elo1]
                            · have p3495_0 := h3495c.1
                              have p3495_1 := h3495c.2.1
                              have p3495_2 := h3495c.2.2.1
                              have p3495_3 := h3495c.2.2.2
                              linarith only [h3357, hlam, p3495_1]
                            · have p3495_0 := h3495c.1
                              have p3495_1 := h3495c.2.1
                              have p3495_2 := h3495c.2.2.1
                              have p3495_3 := h3495c.2.2.2
                              linarith only [h3481, hlam, p3495_1]
                            · have p3495_0 := h3495c.1
                              have p3495_1 := h3495c.2.1
                              have p3495_2 := h3495c.2.2.1
                              have p3495_3 := h3495c.2.2.2
                              linarith only [hlam, p3495_0]
                            · have p3495_0 := h3495c.1
                              have p3495_1 := h3495c.2.1
                              have p3495_2 := h3495c.2.2.1
                              have p3495_3 := h3495c.2.2.2
                              linarith only [h3491, hlam, p3495_1]
                            · have p3495_0 := h3495c.1
                              have p3495_1 := h3495c.2.1
                              have p3495_2 := h3495c.2.2.1
                              have p3495_3 := h3495c.2.2.2
                              linarith only [h3357, hc02, hc45, hlam, hphi, ht0b, ht5b, p3495_1]
                            · have p3495_0 := h3495c.1
                              have p3495_1 := h3495c.2.1
                              have p3495_2 := h3495c.2.2.1
                              have p3495_3 := h3495c.2.2.2
                              linarith only [h3358, hc03, hc35, hlam, hphi, p3495_1]
                            · have p3495_0 := h3495c.1
                              have p3495_1 := h3495c.2.1
                              have p3495_2 := h3495c.2.2.1
                              have p3495_3 := h3495c.2.2.2
                              linarith only [h3486, hc13, hc35, hlam, hphi, p3495_1]
                            · have p3495_0 := h3495c.1
                              have p3495_1 := h3495c.2.1
                              have p3495_2 := h3495c.2.2.1
                              have p3495_3 := h3495c.2.2.2
                              linarith only [h3491, hc23, hc35, hlam, hphi, p3495_1]
                            · have p3495_0 := h3495c.1
                              have p3495_1 := h3495c.2.1
                              have p3495_2 := h3495c.2.2.1
                              have p3495_3 := h3495c.2.2.2
                              linarith only [hlam, p3495_0]
                            · have p3495_0 := h3495c.1
                              have p3495_1 := h3495c.2.1
                              have p3495_2 := h3495c.2.2.1
                              have p3495_3 := h3495c.2.2.2
                              rcases p3495_3 (m.d 0 5) (by simp) with h3515 | h3515
                              · linarith only [h3358, h3515, hlam]
                              · linarith only [h3479, h3515, hlam]
                            · have p3495_0 := h3495c.1
                              have p3495_1 := h3495c.2.1
                              have p3495_2 := h3495c.2.2.1
                              have p3495_3 := h3495c.2.2.2
                              linarith only [h3479, hlam, p3495_0]
                            · have p3495_0 := h3495c.1
                              have p3495_1 := h3495c.2.1
                              have p3495_2 := h3495c.2.2.1
                              have p3495_3 := h3495c.2.2.2
                              linarith only [h3488, hlam, p3495_0]
                            · have p3495_0 := h3495c.1
                              have p3495_1 := h3495c.2.1
                              have p3495_2 := h3495c.2.2.1
                              have p3495_3 := h3495c.2.2.2
                              linarith only [h3493, hlam, p3495_0]
                            · have p3495_0 := h3495c.1
                              have p3495_1 := h3495c.2.1
                              have p3495_2 := h3495c.2.2.1
                              have p3495_3 := h3495c.2.2.2
                              linarith only [h3494, hlam, p3495_0]
                            · have p3495_0 := h3495c.1
                              have p3495_1 := h3495c.2.1
                              have p3495_2 := h3495c.2.2.1
                              have p3495_3 := h3495c.2.2.2
                              linarith only [hlam, p3495_0]
                          · linarith only [h0, h3355, h3479, h3480, h3482, h3494, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                        · linarith only [h0, h3355, h3480, h3488, h3493, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · linarith only [h0, h3479, h3488, hlam]
            · linarith only [h0, h3355, h3357, h3480, h3481, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
          · linarith only [h0, h3356, h3480, hlam]
        · linarith only [h0, h3355, h3479, hlam]
    · linarith only [h0, h3355, h3356, h3357, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h3530 | h3530
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3531 | h3531
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3532 | h3532
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3533 | h3533
          · linarith only [h3356, h3530, h3533, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3535 | h3535
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3536 | h3536
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3537 | h3537
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3538 | h3538
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3539 | h3539
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3540 | h3540
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3541 | h3541
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3542 | h3542
                          · rcases h5bigk with h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c | h3543c
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [hlam, p3543_0]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h0, h3355, h3536, hc15, hlam, hphi, ht01, ht0b, ht5b, p3543_1, u1elo2]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h0, h3355, h3536, h3540, h3542, hc45, hlam, hphi, ht01, ht0b, ht5b, p3543_1, u1elo2]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h0, h3355, h3536, h3542, hc45, hlam, hphi, ht01, ht0b, ht5b, p3543_1, u1elo2]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h0, h3355, h3536, hc45, hlam, hphi, ht01, ht0b, ht5b, p3543_1, u1elo2]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h3355, hlam, p3543_0]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [hlam, p3543_0]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h3540, h3542, hc45, hlam, hphi, ht01, ht0b, ht5b, p3543_1, u1elo4]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h0, h3355, h3536, h3542, hc45, hlam, hphi, ht01, ht0b, ht5b, p3543_1, u1elo2]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h0, h3355, h3536, hc45, hlam, hphi, ht01, ht0b, ht5b, p3543_1, u1elo2]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h3530, hlam, p3543_1]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h3535, hlam, p3543_1]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [hlam, p3543_0]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h3530, h3542, hc02, hc45, hlam, hphi, ht0b, ht5b, p3543_1]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h0, h3355, h3535, h3536, hc45, hlam, hphi, ht01, ht0b, ht5b, p3543_1, u1elo2]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h3531, hlam, p3543_0]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h3537, hlam, p3543_0]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h3540, hlam, p3543_0]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [hlam, p3543_0]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h3531, hc03, hc45, hlam, hphi, ht0b, ht5b, p3543_1]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h3532, hlam, p3543_0]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h3538, hlam, p3543_0]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h3541, hlam, p3543_0]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [h3542, hlam, p3543_0]
                            · have p3543_0 := h3543c.1
                              have p3543_1 := h3543c.2.1
                              have p3543_2 := h3543c.2.2.1
                              have p3543_3 := h3543c.2.2.2
                              linarith only [hlam, p3543_0]
                          · linarith only [h0, h3355, h3536, h3538, h3542, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                        · linarith only [h0, h3355, h3533, h3538, h3541, hlam]
                      · linarith only [h0, h3355, h3531, h3533, h3539, h3540, hc03, hc15, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h3533, h3536, h3539, hc01, hlam, hphi, u1elo2]
                  · linarith only [h0, h3532, h3538, hlam]
                · linarith only [h0, h3355, h3531, h3536, h3537, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3575 | h3575
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3576 | h3576
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3577 | h3577
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3578 | h3578
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3579 | h3579
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3580 | h3580
                          · rcases h5bigk with h3581c | h3581c | h3581c | h3581c | h3581c | h3581c | h3581c | h3581c | h3581c | h3581c | h3581c | h3581c | h3581c | h3581c | h3581c | h3581c | h3581c | h3581c | h3581c | h3581c | h3581c | h3581c | h3581c | h3581c | h3581c
                            · have p3581_0 := h3581c.1
                              have p3581_1 := h3581c.2.1
                              have p3581_2 := h3581c.2.2.1
                              have p3581_3 := h3581c.2.2.2
                              linarith only [hlam, p3581_0]
                            · have p3581_0 := h3581c.1
                              have p3581_1 := h3581c.2.1
                              have p3581_2 := h3581c.2.2.1
                              have p3581_3 := h3581c.2.2.2
                              linarith only [h0, h3355, h3536, h3577, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3581_1]
                            · have p3581_0 := h3581c.1
                              have p3581_1 := h3581c.2.1
                              have p3581_2 := h3581c.2.2.1
                              have p3581_3 := h3581c.2.2.2
                              linarith only [h0, h3355, h3536, h3577, h3578, h3580, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3581_1]
                            · have p3581_0 := h3581c.1
                              have p3581_1 := h3581c.2.1
                              have p3581_2 := h3581c.2.2.1
                              have p3581_3 := h3581c.2.2.2
                              linarith only [h0, h3355, h3536, h3577, h3580, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3581_1]
                            · have p3581_0 := h3581c.1
                              have p3581_1 := h3581c.2.1
                              have p3581_2 := h3581c.2.2.1
                              have p3581_3 := h3581c.2.2.2
                              linarith only [h0, h3355, h3536, h3577, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3581_1]
                            · have p3581_0 := h3581c.1
                              have p3581_1 := h3581c.2.1
                              have p3581_2 := h3581c.2.2.1
                              have p3581_3 := h3581c.2.2.2
                              linarith only [h3355, hlam, p3581_0]
                            · have p3581_0 := h3581c.1
                              have p3581_1 := h3581c.2.1
                              have p3581_2 := h3581c.2.2.1
                              have p3581_3 := h3581c.2.2.2
                              linarith only [hlam, p3581_0]
                            · have p3581_0 := h3581c.1
                              have p3581_1 := h3581c.2.1
                              have p3581_2 := h3581c.2.2.1
                              have p3581_3 := h3581c.2.2.2
                              linarith only [h3578, h3580, hc45, hlam, hphi, ht01, ht0b, ht5b, p3581_1, u1elo4]
                            · have p3581_0 := h3581c.1
                              have p3581_1 := h3581c.2.1
                              have p3581_2 := h3581c.2.2.1
                              have p3581_3 := h3581c.2.2.2
                              linarith only [h0, h3355, h3536, h3577, h3580, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3581_1]
                            · have p3581_0 := h3581c.1
                              have p3581_1 := h3581c.2.1
                              have p3581_2 := h3581c.2.2.1
                              have p3581_3 := h3581c.2.2.2
                              linarith only [h0, h3355, h3536, h3577, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3581_1]
                            · have p3581_0 := h3581c.1
                              have p3581_1 := h3581c.2.1
                              have p3581_2 := h3581c.2.2.1
                              have p3581_3 := h3581c.2.2.2
                              linarith only [h3530, hlam, p3581_1]
                            · have p3581_0 := h3581c.1
                              have p3581_1 := h3581c.2.1
                              have p3581_2 := h3581c.2.2.1
                              have p3581_3 := h3581c.2.2.2
                              linarith only [h3535, hlam, p3581_1]
                            · have p3581_0 := h3581c.1
                              have p3581_1 := h3581c.2.1
                              have p3581_2 := h3581c.2.2.1
                              have p3581_3 := h3581c.2.2.2
                              linarith only [hlam, p3581_0]
                            · have p3581_0 := h3581c.1
                              have p3581_1 := h3581c.2.1
                              have p3581_2 := h3581c.2.2.1
                              have p3581_3 := h3581c.2.2.2
                              linarith only [h3530, h3580, hc02, hc45, hlam, hphi, ht0b, ht5b, p3581_1]
                            · have p3581_0 := h3581c.1
                              have p3581_1 := h3581c.2.1
                              have p3581_2 := h3581c.2.2.1
                              have p3581_3 := h3581c.2.2.2
                              linarith only [h0, h3355, h3535, h3536, h3577, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3581_1]
                            · have p3581_0 := h3581c.1
                              have p3581_1 := h3581c.2.1
                              have p3581_2 := h3581c.2.2.1
                              have p3581_3 := h3581c.2.2.2
                              linarith only [h3531, hlam, p3581_0]
                            · have p3581_0 := h3581c.1
                              have p3581_1 := h3581c.2.1
                              have p3581_2 := h3581c.2.2.1
                              have p3581_3 := h3581c.2.2.2
                              linarith only [h3575, hlam, p3581_0]
                            · have p3581_0 := h3581c.1
                              have p3581_1 := h3581c.2.1
                              have p3581_2 := h3581c.2.2.1
                              have p3581_3 := h3581c.2.2.2
                              linarith only [h3578, hlam, p3581_0]
                            · have p3581_0 := h3581c.1
                              have p3581_1 := h3581c.2.1
                              have p3581_2 := h3581c.2.2.1
                              have p3581_3 := h3581c.2.2.2
                              linarith only [hlam, p3581_0]
                            · have p3581_0 := h3581c.1
                              have p3581_1 := h3581c.2.1
                              have p3581_2 := h3581c.2.2.1
                              have p3581_3 := h3581c.2.2.2
                              linarith only [h3575, hc45, hlam, hphi, ht01, ht0b, ht5b, p3581_1, u1elo2]
                            · have p3581_0 := h3581c.1
                              have p3581_1 := h3581c.2.1
                              have p3581_2 := h3581c.2.2.1
                              have p3581_3 := h3581c.2.2.2
                              linarith only [h3532, hlam, p3581_0]
                            · have p3581_0 := h3581c.1
                              have p3581_1 := h3581c.2.1
                              have p3581_2 := h3581c.2.2.1
                              have p3581_3 := h3581c.2.2.2
                              linarith only [h3576, hlam, p3581_0]
                            · have p3581_0 := h3581c.1
                              have p3581_1 := h3581c.2.1
                              have p3581_2 := h3581c.2.2.1
                              have p3581_3 := h3581c.2.2.2
                              linarith only [h3579, hlam, p3581_0]
                            · have p3581_0 := h3581c.1
                              have p3581_1 := h3581c.2.1
                              have p3581_2 := h3581c.2.2.1
                              have p3581_3 := h3581c.2.2.2
                              linarith only [h3580, hlam, p3581_0]
                            · have p3581_0 := h3581c.1
                              have p3581_1 := h3581c.2.1
                              have p3581_2 := h3581c.2.2.1
                              have p3581_3 := h3581c.2.2.2
                              linarith only [hlam, p3581_0]
                          · linarith only [h0, h3532, h3536, h3580, hlam]
                        · linarith only [h0, h3355, h3576, h3579, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                      · linarith only [h0, h3536, h3577, h3578, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3610 | h3610
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3611 | h3611
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3612 | h3612
                          · rcases h5bigk with h3613c | h3613c | h3613c | h3613c | h3613c | h3613c | h3613c | h3613c | h3613c | h3613c | h3613c | h3613c | h3613c | h3613c | h3613c | h3613c | h3613c | h3613c | h3613c | h3613c | h3613c | h3613c | h3613c | h3613c | h3613c
                            · have p3613_0 := h3613c.1
                              have p3613_1 := h3613c.2.1
                              have p3613_2 := h3613c.2.2.1
                              have p3613_3 := h3613c.2.2.2
                              linarith only [hlam, p3613_0]
                            · have p3613_0 := h3613c.1
                              have p3613_1 := h3613c.2.1
                              have p3613_2 := h3613c.2.2.1
                              have p3613_3 := h3613c.2.2.2
                              linarith only [h0, h3355, hc15, hlam, hphi, ht01, ht0b, ht5b, p3613_1, u1elo3]
                            · have p3613_0 := h3613c.1
                              have p3613_1 := h3613c.2.1
                              have p3613_2 := h3613c.2.2.1
                              have p3613_3 := h3613c.2.2.2
                              linarith only [h0, h3355, h3610, h3612, hc45, hlam, hphi, ht01, ht0b, ht5b, p3613_1, u1elo3]
                            · have p3613_0 := h3613c.1
                              have p3613_1 := h3613c.2.1
                              have p3613_2 := h3613c.2.2.1
                              have p3613_3 := h3613c.2.2.2
                              linarith only [h0, h3355, h3612, hc45, hlam, hphi, ht01, ht0b, ht5b, p3613_1, u1elo3]
                            · have p3613_0 := h3613c.1
                              have p3613_1 := h3613c.2.1
                              have p3613_2 := h3613c.2.2.1
                              have p3613_3 := h3613c.2.2.2
                              linarith only [h0, h3355, hc45, hlam, hphi, ht01, ht0b, ht5b, p3613_1, u1elo3]
                            · have p3613_0 := h3613c.1
                              have p3613_1 := h3613c.2.1
                              have p3613_2 := h3613c.2.2.1
                              have p3613_3 := h3613c.2.2.2
                              linarith only [h3355, hlam, p3613_0]
                            · have p3613_0 := h3613c.1
                              have p3613_1 := h3613c.2.1
                              have p3613_2 := h3613c.2.2.1
                              have p3613_3 := h3613c.2.2.2
                              linarith only [hlam, p3613_0]
                            · have p3613_0 := h3613c.1
                              have p3613_1 := h3613c.2.1
                              have p3613_2 := h3613c.2.2.1
                              have p3613_3 := h3613c.2.2.2
                              linarith only [h3610, h3612, hc45, hlam, hphi, ht01, ht0b, ht5b, p3613_1, u1elo4]
                            · have p3613_0 := h3613c.1
                              have p3613_1 := h3613c.2.1
                              have p3613_2 := h3613c.2.2.1
                              have p3613_3 := h3613c.2.2.2
                              linarith only [h0, h3355, h3612, hc45, hlam, hphi, ht01, ht0b, ht5b, p3613_1, u1elo3]
                            · have p3613_0 := h3613c.1
                              have p3613_1 := h3613c.2.1
                              have p3613_2 := h3613c.2.2.1
                              have p3613_3 := h3613c.2.2.2
                              linarith only [h0, h3355, hc45, hlam, hphi, ht01, ht0b, ht5b, p3613_1, u1elo3]
                            · have p3613_0 := h3613c.1
                              have p3613_1 := h3613c.2.1
                              have p3613_2 := h3613c.2.2.1
                              have p3613_3 := h3613c.2.2.2
                              linarith only [h3530, hlam, p3613_1]
                            · have p3613_0 := h3613c.1
                              have p3613_1 := h3613c.2.1
                              have p3613_2 := h3613c.2.2.1
                              have p3613_3 := h3613c.2.2.2
                              linarith only [h3535, hlam, p3613_1]
                            · have p3613_0 := h3613c.1
                              have p3613_1 := h3613c.2.1
                              have p3613_2 := h3613c.2.2.1
                              have p3613_3 := h3613c.2.2.2
                              linarith only [hlam, p3613_0]
                            · have p3613_0 := h3613c.1
                              have p3613_1 := h3613c.2.1
                              have p3613_2 := h3613c.2.2.1
                              have p3613_3 := h3613c.2.2.2
                              linarith only [h3530, h3612, hc02, hc45, hlam, hphi, ht0b, ht5b, p3613_1]
                            · have p3613_0 := h3613c.1
                              have p3613_1 := h3613c.2.1
                              have p3613_2 := h3613c.2.2.1
                              have p3613_3 := h3613c.2.2.2
                              linarith only [h0, h3355, h3535, hc45, hlam, hphi, ht01, ht0b, ht5b, p3613_1, u1elo3]
                            · have p3613_0 := h3613c.1
                              have p3613_1 := h3613c.2.1
                              have p3613_2 := h3613c.2.2.1
                              have p3613_3 := h3613c.2.2.2
                              linarith only [h3531, hlam, p3613_0]
                            · have p3613_0 := h3613c.1
                              have p3613_1 := h3613c.2.1
                              have p3613_2 := h3613c.2.2.1
                              have p3613_3 := h3613c.2.2.2
                              linarith only [h3575, hlam, p3613_0]
                            · have p3613_0 := h3613c.1
                              have p3613_1 := h3613c.2.1
                              have p3613_2 := h3613c.2.2.1
                              have p3613_3 := h3613c.2.2.2
                              linarith only [h3610, hlam, p3613_0]
                            · have p3613_0 := h3613c.1
                              have p3613_1 := h3613c.2.1
                              have p3613_2 := h3613c.2.2.1
                              have p3613_3 := h3613c.2.2.2
                              linarith only [hlam, p3613_0]
                            · have p3613_0 := h3613c.1
                              have p3613_1 := h3613c.2.1
                              have p3613_2 := h3613c.2.2.1
                              have p3613_3 := h3613c.2.2.2
                              linarith only [h3531, hc03, hc45, hlam, hphi, ht0b, ht5b, p3613_1]
                            · have p3613_0 := h3613c.1
                              have p3613_1 := h3613c.2.1
                              have p3613_2 := h3613c.2.2.1
                              have p3613_3 := h3613c.2.2.2
                              linarith only [h3532, hlam, p3613_0]
                            · have p3613_0 := h3613c.1
                              have p3613_1 := h3613c.2.1
                              have p3613_2 := h3613c.2.2.1
                              have p3613_3 := h3613c.2.2.2
                              linarith only [h3576, hlam, p3613_0]
                            · have p3613_0 := h3613c.1
                              have p3613_1 := h3613c.2.1
                              have p3613_2 := h3613c.2.2.1
                              have p3613_3 := h3613c.2.2.2
                              linarith only [h3611, hlam, p3613_0]
                            · have p3613_0 := h3613c.1
                              have p3613_1 := h3613c.2.1
                              have p3613_2 := h3613c.2.2.1
                              have p3613_3 := h3613c.2.2.2
                              linarith only [h3612, hlam, p3613_0]
                            · have p3613_0 := h3613c.1
                              have p3613_1 := h3613c.2.1
                              have p3613_2 := h3613c.2.2.1
                              have p3613_3 := h3613c.2.2.2
                              linarith only [hlam, p3613_0]
                          · linarith only [h0, h3355, h3532, h3533, h3577, h3612, hc04, hc15, hlam, hphi, ht0b, ht5b]
                        · linarith only [h0, h3355, h3533, h3576, h3611, hlam]
                      · linarith only [h3536, h3575, h3610, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h3532, h3576, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3643 | h3643
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3644 | h3644
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3645 | h3645
                      · linarith only [h0, h3355, h3535, h3536, h3575, h3644, h3645, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · linarith only [h0, h3355, h3531, h3536, h3644, h3645, hc05, hc15, hlam, hphi, ht0b, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3648 | h3648
                      · linarith only [h3575, h3644, h3648, hc13, hc34, hlam, hphi]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3650 | h3650
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3651 | h3651
                          · rcases h5bigk with h3652c | h3652c | h3652c | h3652c | h3652c | h3652c | h3652c | h3652c | h3652c | h3652c | h3652c | h3652c | h3652c | h3652c | h3652c | h3652c | h3652c | h3652c | h3652c | h3652c | h3652c | h3652c | h3652c | h3652c | h3652c
                            · have p3652_0 := h3652c.1
                              have p3652_1 := h3652c.2.1
                              have p3652_2 := h3652c.2.2.1
                              have p3652_3 := h3652c.2.2.2
                              linarith only [hlam, p3652_0]
                            · have p3652_0 := h3652c.1
                              have p3652_1 := h3652c.2.1
                              have p3652_2 := h3652c.2.2.1
                              have p3652_3 := h3652c.2.2.2
                              linarith only [h0, h3355, hc15, hlam, hphi, ht01, ht0b, ht5b, p3652_1, u1elo3]
                            · have p3652_0 := h3652c.1
                              have p3652_1 := h3652c.2.1
                              have p3652_2 := h3652c.2.2.1
                              have p3652_3 := h3652c.2.2.2
                              linarith only [h0, h3355, h3650, hc45, hlam, hphi, ht01, ht0b, ht5b, p3652_1, u1elo3]
                            · have p3652_0 := h3652c.1
                              have p3652_1 := h3652c.2.1
                              have p3652_2 := h3652c.2.2.1
                              have p3652_3 := h3652c.2.2.2
                              linarith only [h0, h3355, h3575, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3652_1, u1elo3]
                            · have p3652_0 := h3652c.1
                              have p3652_1 := h3652c.2.1
                              have p3652_2 := h3652c.2.2.1
                              have p3652_3 := h3652c.2.2.2
                              linarith only [h0, h3355, hc45, hlam, hphi, ht01, ht0b, ht5b, p3652_1, u1elo3]
                            · have p3652_0 := h3652c.1
                              have p3652_1 := h3652c.2.1
                              have p3652_2 := h3652c.2.2.1
                              have p3652_3 := h3652c.2.2.2
                              linarith only [h3355, hlam, p3652_0]
                            · have p3652_0 := h3652c.1
                              have p3652_1 := h3652c.2.1
                              have p3652_2 := h3652c.2.2.1
                              have p3652_3 := h3652c.2.2.2
                              linarith only [hlam, p3652_0]
                            · have p3652_0 := h3652c.1
                              have p3652_1 := h3652c.2.1
                              have p3652_2 := h3652c.2.2.1
                              have p3652_3 := h3652c.2.2.2
                              linarith only [h3650, hc45, hlam, hphi, ht01, ht0b, ht5b, p3652_1, u1elo4]
                            · have p3652_0 := h3652c.1
                              have p3652_1 := h3652c.2.1
                              have p3652_2 := h3652c.2.2.1
                              have p3652_3 := h3652c.2.2.2
                              linarith only [h3575, hlam, p3652_1]
                            · have p3652_0 := h3652c.1
                              have p3652_1 := h3652c.2.1
                              have p3652_2 := h3652c.2.2.1
                              have p3652_3 := h3652c.2.2.2
                              linarith only [h0, h3355, hc45, hlam, hphi, ht01, ht0b, ht5b, p3652_1, u1elo3]
                            · have p3652_0 := h3652c.1
                              have p3652_1 := h3652c.2.1
                              have p3652_2 := h3652c.2.2.1
                              have p3652_3 := h3652c.2.2.2
                              linarith only [h3530, hlam, p3652_1]
                            · have p3652_0 := h3652c.1
                              have p3652_1 := h3652c.2.1
                              have p3652_2 := h3652c.2.2.1
                              have p3652_3 := h3652c.2.2.2
                              linarith only [h3535, hlam, p3652_1]
                            · have p3652_0 := h3652c.1
                              have p3652_1 := h3652c.2.1
                              have p3652_2 := h3652c.2.2.1
                              have p3652_3 := h3652c.2.2.2
                              linarith only [hlam, p3652_0]
                            · have p3652_0 := h3652c.1
                              have p3652_1 := h3652c.2.1
                              have p3652_2 := h3652c.2.2.1
                              have p3652_3 := h3652c.2.2.2
                              linarith only [h3648, hlam, p3652_1]
                            · have p3652_0 := h3652c.1
                              have p3652_1 := h3652c.2.1
                              have p3652_2 := h3652c.2.2.1
                              have p3652_3 := h3652c.2.2.2
                              linarith only [h3356, h3530, h3644, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3652_1]
                            · have p3652_0 := h3652c.1
                              have p3652_1 := h3652c.2.1
                              have p3652_2 := h3652c.2.2.1
                              have p3652_3 := h3652c.2.2.2
                              linarith only [h3531, hlam, p3652_0]
                            · have p3652_0 := h3652c.1
                              have p3652_1 := h3652c.2.1
                              have p3652_2 := h3652c.2.2.1
                              have p3652_3 := h3652c.2.2.2
                              linarith only [h0, h3355, h3531, hc15, hlam, hphi, ht01, ht0b, ht5b, p3652_1, u1elo3]
                            · have p3652_0 := h3652c.1
                              have p3652_1 := h3652c.2.1
                              have p3652_2 := h3652c.2.2.1
                              have p3652_3 := h3652c.2.2.2
                              linarith only [h0, h3355, h3531, hc25, hlam, hphi, ht01, ht0b, ht5b, p3652_1, u1elo3]
                            · have p3652_0 := h3652c.1
                              have p3652_1 := h3652c.2.1
                              have p3652_2 := h3652c.2.2.1
                              have p3652_3 := h3652c.2.2.2
                              linarith only [hlam, p3652_0]
                            · have p3652_0 := h3652c.1
                              have p3652_1 := h3652c.2.1
                              have p3652_2 := h3652c.2.2.1
                              have p3652_3 := h3652c.2.2.2
                              linarith only [h0, h3355, h3531, hc45, hlam, hphi, ht01, ht0b, ht5b, p3652_1, u1elo3]
                            · have p3652_0 := h3652c.1
                              have p3652_1 := h3652c.2.1
                              have p3652_2 := h3652c.2.2.1
                              have p3652_3 := h3652c.2.2.2
                              linarith only [h3532, hlam, p3652_0]
                            · have p3652_0 := h3652c.1
                              have p3652_1 := h3652c.2.1
                              have p3652_2 := h3652c.2.2.1
                              have p3652_3 := h3652c.2.2.2
                              linarith only [h3643, hlam, p3652_0]
                            · have p3652_0 := h3652c.1
                              have p3652_1 := h3652c.2.1
                              have p3652_2 := h3652c.2.2.1
                              have p3652_3 := h3652c.2.2.2
                              linarith only [h3650, hlam, p3652_0]
                            · have p3652_0 := h3652c.1
                              have p3652_1 := h3652c.2.1
                              have p3652_2 := h3652c.2.2.1
                              have p3652_3 := h3652c.2.2.2
                              linarith only [h3651, hlam, p3652_0]
                            · have p3652_0 := h3652c.1
                              have p3652_1 := h3652c.2.1
                              have p3652_2 := h3652c.2.2.1
                              have p3652_3 := h3652c.2.2.2
                              linarith only [hlam, p3652_0]
                          · linarith only [h3356, h3530, h3644, h3648, h3651, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h3355, h3356, h3643, h3650, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h0, h3355, h3532, h3643, hlam]
            · linarith only [h3356, h3530, h3535, hc12, hc24, hlam, hphi]
        · linarith only [h0, h3355, h3532, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3683 | h3683
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3684 | h3684
          · linarith only [h3356, h3530, h3684, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3686 | h3686
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3687 | h3687
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3688 | h3688
                · linarith only [h3355, h3531, h3688, hlam]
                · linarith only [h0, h3355, h3687, h3688, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3691 | h3691
                · linarith only [h3531, h3687, h3691, hc03, hc34, hlam, hphi]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3693 | h3693
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3694 | h3694
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3695 | h3695
                      · linarith only [h3530, h3531, h3695, hlam]
                      · linarith only [h0, h3355, h3687, h3691, h3694, h3695, hc13, hc35, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3698 | h3698
                      · linarith only [h3531, h3694, h3698, hc03, hc34, hlam, hphi]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3700 | h3700
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3701 | h3701
                          · rcases h5bigk with h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c
                            · have p3702_0 := h3702c.1
                              have p3702_1 := h3702c.2.1
                              have p3702_2 := h3702c.2.2.1
                              have p3702_3 := h3702c.2.2.2
                              linarith only [hlam, p3702_0]
                            · have p3702_0 := h3702c.1
                              have p3702_1 := h3702c.2.1
                              have p3702_2 := h3702c.2.2.1
                              have p3702_3 := h3702c.2.2.2
                              linarith only [h0, h3355, h3686, h3698, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3702_1, u1elo3]
                            · have p3702_0 := h3702c.1
                              have p3702_1 := h3702c.2.1
                              have p3702_2 := h3702c.2.2.1
                              have p3702_3 := h3702c.2.2.2
                              linarith only [h0, h3355, h3698, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3702_1, u1elo3]
                            · have p3702_0 := h3702c.1
                              have p3702_1 := h3702c.2.1
                              have p3702_2 := h3702c.2.2.1
                              have p3702_3 := h3702c.2.2.2
                              linarith only [h3531, hlam, p3702_1]
                            · have p3702_0 := h3702c.1
                              have p3702_1 := h3702c.2.1
                              have p3702_2 := h3702c.2.2.1
                              have p3702_3 := h3702c.2.2.2
                              linarith only [h0, h3355, hc45, hlam, hphi, ht01, ht0b, ht5b, p3702_1, u1elo3]
                            · have p3702_0 := h3702c.1
                              have p3702_1 := h3702c.2.1
                              have p3702_2 := h3702c.2.2.1
                              have p3702_3 := h3702c.2.2.2
                              linarith only [h3355, hlam, p3702_0]
                            · have p3702_0 := h3702c.1
                              have p3702_1 := h3702c.2.1
                              have p3702_2 := h3702c.2.2.1
                              have p3702_3 := h3702c.2.2.2
                              linarith only [hlam, p3702_0]
                            · have p3702_0 := h3702c.1
                              have p3702_1 := h3702c.2.1
                              have p3702_2 := h3702c.2.2.1
                              have p3702_3 := h3702c.2.2.2
                              linarith only [h3698, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3702_1, u1elo4]
                            · have p3702_0 := h3702c.1
                              have p3702_1 := h3702c.2.1
                              have p3702_2 := h3702c.2.2.1
                              have p3702_3 := h3702c.2.2.2
                              linarith only [h3691, hlam, p3702_1]
                            · have p3702_0 := h3702c.1
                              have p3702_1 := h3702c.2.1
                              have p3702_2 := h3702c.2.2.1
                              have p3702_3 := h3702c.2.2.2
                              linarith only [h0, h3355, hc45, hlam, hphi, ht01, ht0b, ht5b, p3702_1, u1elo3]
                            · have p3702_0 := h3702c.1
                              have p3702_1 := h3702c.2.1
                              have p3702_2 := h3702c.2.2.1
                              have p3702_3 := h3702c.2.2.2
                              linarith only [h3530, hlam, p3702_1]
                            · have p3702_0 := h3702c.1
                              have p3702_1 := h3702c.2.1
                              have p3702_2 := h3702c.2.2.1
                              have p3702_3 := h3702c.2.2.2
                              linarith only [h3686, hlam, p3702_1]
                            · have p3702_0 := h3702c.1
                              have p3702_1 := h3702c.2.1
                              have p3702_2 := h3702c.2.2.1
                              have p3702_3 := h3702c.2.2.2
                              linarith only [hlam, p3702_0]
                            · have p3702_0 := h3702c.1
                              have p3702_1 := h3702c.2.1
                              have p3702_2 := h3702c.2.2.1
                              have p3702_3 := h3702c.2.2.2
                              linarith only [h3698, hlam, p3702_1]
                            · have p3702_0 := h3702c.1
                              have p3702_1 := h3702c.2.1
                              have p3702_2 := h3702c.2.2.1
                              have p3702_3 := h3702c.2.2.2
                              linarith only [h3356, h3530, h3694, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3702_1]
                            · have p3702_0 := h3702c.1
                              have p3702_1 := h3702c.2.1
                              have p3702_2 := h3702c.2.2.1
                              have p3702_3 := h3702c.2.2.2
                              linarith only [h3531, hc03, hc35, hlam, hphi, p3702_1]
                            · have p3702_0 := h3702c.1
                              have p3702_1 := h3702c.2.1
                              have p3702_2 := h3702c.2.2.1
                              have p3702_3 := h3702c.2.2.2
                              linarith only [h3691, hc13, hc35, hlam, hphi, p3702_1]
                            · have p3702_0 := h3702c.1
                              have p3702_1 := h3702c.2.1
                              have p3702_2 := h3702c.2.2.1
                              have p3702_3 := h3702c.2.2.2
                              linarith only [h3698, hc23, hc35, hlam, hphi, p3702_1]
                            · have p3702_0 := h3702c.1
                              have p3702_1 := h3702c.2.1
                              have p3702_2 := h3702c.2.2.1
                              have p3702_3 := h3702c.2.2.2
                              linarith only [hlam, p3702_0]
                            · have p3702_0 := h3702c.1
                              have p3702_1 := h3702c.2.1
                              have p3702_2 := h3702c.2.2.1
                              have p3702_3 := h3702c.2.2.2
                              rcases p3702_3 (m.d 0 5) (by simp) with h3722 | h3722
                              · linarith only [h3531, h3722, hlam]
                              · linarith only [h3683, h3722, hlam]
                            · have p3702_0 := h3702c.1
                              have p3702_1 := h3702c.2.1
                              have p3702_2 := h3702c.2.2.1
                              have p3702_3 := h3702c.2.2.2
                              linarith only [h3683, hlam, p3702_0]
                            · have p3702_0 := h3702c.1
                              have p3702_1 := h3702c.2.1
                              have p3702_2 := h3702c.2.2.1
                              have p3702_3 := h3702c.2.2.2
                              linarith only [h3693, hlam, p3702_0]
                            · have p3702_0 := h3702c.1
                              have p3702_1 := h3702c.2.1
                              have p3702_2 := h3702c.2.2.1
                              have p3702_3 := h3702c.2.2.2
                              linarith only [h3700, hlam, p3702_0]
                            · have p3702_0 := h3702c.1
                              have p3702_1 := h3702c.2.1
                              have p3702_2 := h3702c.2.2.1
                              have p3702_3 := h3702c.2.2.2
                              linarith only [h3701, hlam, p3702_0]
                            · have p3702_0 := h3702c.1
                              have p3702_1 := h3702c.2.1
                              have p3702_2 := h3702c.2.2.1
                              have p3702_3 := h3702c.2.2.2
                              linarith only [hlam, p3702_0]
                          · linarith only [h3356, h3530, h3694, h3698, h3701, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h0, h3355, h3684, h3693, h3700, hlam]
                  · linarith only [h0, h3355, h3683, h3693, hc04, hc15, hlam, hphi, ht0b, ht5b]
            · linarith only [h3356, h3530, h3686, hc12, hc24, hlam, hphi]
        · linarith only [h0, h3355, h3683, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3735 | h3735
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3736 | h3736
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3737 | h3737
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3738 | h3738
            · linarith only [h0, h3355, h3530, h3738, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
            · linarith only [h3356, h3737, h3738, hc02, hc25, hlam, hphi]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3741 | h3741
            · linarith only [h3530, h3737, h3741, hc02, hc24, hlam, hphi]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3743 | h3743
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3744 | h3744
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3745 | h3745
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3746 | h3746
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3747 | h3747
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3748 | h3748
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3749 | h3749
                          · rcases h5bigk with h3750c | h3750c | h3750c | h3750c | h3750c | h3750c | h3750c | h3750c | h3750c | h3750c | h3750c | h3750c | h3750c | h3750c | h3750c | h3750c | h3750c | h3750c | h3750c | h3750c | h3750c | h3750c | h3750c | h3750c | h3750c
                            · have p3750_0 := h3750c.1
                              have p3750_1 := h3750c.2.1
                              have p3750_2 := h3750c.2.2.1
                              have p3750_3 := h3750c.2.2.2
                              linarith only [hlam, p3750_0]
                            · have p3750_0 := h3750c.1
                              have p3750_1 := h3750c.2.1
                              have p3750_2 := h3750c.2.2.1
                              have p3750_3 := h3750c.2.2.2
                              linarith only [h0, h3355, h3741, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3750_1, u1elo3]
                            · have p3750_0 := h3750c.1
                              have p3750_1 := h3750c.2.1
                              have p3750_2 := h3750c.2.2.1
                              have p3750_3 := h3750c.2.2.2
                              linarith only [h3530, hlam, p3750_0]
                            · have p3750_0 := h3750c.1
                              have p3750_1 := h3750c.2.1
                              have p3750_2 := h3750c.2.2.1
                              have p3750_3 := h3750c.2.2.2
                              linarith only [h0, h3355, h3749, hc45, hlam, hphi, ht01, ht0b, ht5b, p3750_1, u1elo3]
                            · have p3750_0 := h3750c.1
                              have p3750_1 := h3750c.2.1
                              have p3750_2 := h3750c.2.2.1
                              have p3750_3 := h3750c.2.2.2
                              linarith only [h0, h3355, hc45, hlam, hphi, ht01, ht0b, ht5b, p3750_1, u1elo3]
                            · have p3750_0 := h3750c.1
                              have p3750_1 := h3750c.2.1
                              have p3750_2 := h3750c.2.2.1
                              have p3750_3 := h3750c.2.2.2
                              linarith only [h3355, hlam, p3750_0]
                            · have p3750_0 := h3750c.1
                              have p3750_1 := h3750c.2.1
                              have p3750_2 := h3750c.2.2.1
                              have p3750_3 := h3750c.2.2.2
                              linarith only [hlam, p3750_0]
                            · have p3750_0 := h3750c.1
                              have p3750_1 := h3750c.2.1
                              have p3750_2 := h3750c.2.2.1
                              have p3750_3 := h3750c.2.2.2
                              linarith only [h3741, hlam, p3750_0]
                            · have p3750_0 := h3750c.1
                              have p3750_1 := h3750c.2.1
                              have p3750_2 := h3750c.2.2.1
                              have p3750_3 := h3750c.2.2.2
                              linarith only [h3749, hc45, hlam, hphi, ht01, ht0b, ht5b, p3750_1, u1elo4]
                            · have p3750_0 := h3750c.1
                              have p3750_1 := h3750c.2.1
                              have p3750_2 := h3750c.2.2.1
                              have p3750_3 := h3750c.2.2.2
                              linarith only [h0, h3355, h3743, hc45, hlam, hphi, ht01, ht0b, ht5b, p3750_1, u1elo2]
                            · have p3750_0 := h3750c.1
                              have p3750_1 := h3750c.2.1
                              have p3750_2 := h3750c.2.2.1
                              have p3750_3 := h3750c.2.2.2
                              linarith only [h3530, hc02, hc25, hlam, hphi, p3750_1]
                            · have p3750_0 := h3750c.1
                              have p3750_1 := h3750c.2.1
                              have p3750_2 := h3750c.2.2.1
                              have p3750_3 := h3750c.2.2.2
                              linarith only [h3741, hc12, hc25, hlam, hphi, p3750_1]
                            · have p3750_0 := h3750c.1
                              have p3750_1 := h3750c.2.1
                              have p3750_2 := h3750c.2.2.1
                              have p3750_3 := h3750c.2.2.2
                              linarith only [hlam, p3750_0]
                            · have p3750_0 := h3750c.1
                              have p3750_1 := h3750c.2.1
                              have p3750_2 := h3750c.2.2.1
                              have p3750_3 := h3750c.2.2.2
                              rcases p3750_3 (m.d 0 5) (by simp) with h3764 | h3764
                              · linarith only [h3530, h3764, hlam]
                              · linarith only [h3735, h3764, hlam]
                            · have p3750_0 := h3750c.1
                              have p3750_1 := h3750c.2.1
                              have p3750_2 := h3750c.2.2.1
                              have p3750_3 := h3750c.2.2.2
                              rcases p3750_3 (m.d 0 5) (by simp) with h3767 | h3767
                              · linarith only [h3530, h3767, hlam]
                              · linarith only [h3736, h3767, hlam]
                            · have p3750_0 := h3750c.1
                              have p3750_1 := h3750c.2.1
                              have p3750_2 := h3750c.2.2.1
                              have p3750_3 := h3750c.2.2.2
                              linarith only [h3735, hlam, p3750_0]
                            · have p3750_0 := h3750c.1
                              have p3750_1 := h3750c.2.1
                              have p3750_2 := h3750c.2.2.1
                              have p3750_3 := h3750c.2.2.2
                              linarith only [h3744, hlam, p3750_0]
                            · have p3750_0 := h3750c.1
                              have p3750_1 := h3750c.2.1
                              have p3750_2 := h3750c.2.2.1
                              have p3750_3 := h3750c.2.2.2
                              linarith only [h3747, hlam, p3750_0]
                            · have p3750_0 := h3750c.1
                              have p3750_1 := h3750c.2.1
                              have p3750_2 := h3750c.2.2.1
                              have p3750_3 := h3750c.2.2.2
                              linarith only [hlam, p3750_0]
                            · have p3750_0 := h3750c.1
                              have p3750_1 := h3750c.2.1
                              have p3750_2 := h3750c.2.2.1
                              have p3750_3 := h3750c.2.2.2
                              linarith only [h3735, hc03, hc45, hlam, hphi, ht0b, ht5b, p3750_1]
                            · have p3750_0 := h3750c.1
                              have p3750_1 := h3750c.2.1
                              have p3750_2 := h3750c.2.2.1
                              have p3750_3 := h3750c.2.2.2
                              linarith only [h3736, hlam, p3750_0]
                            · have p3750_0 := h3750c.1
                              have p3750_1 := h3750c.2.1
                              have p3750_2 := h3750c.2.2.1
                              have p3750_3 := h3750c.2.2.2
                              linarith only [h3745, hlam, p3750_0]
                            · have p3750_0 := h3750c.1
                              have p3750_1 := h3750c.2.1
                              have p3750_2 := h3750c.2.2.1
                              have p3750_3 := h3750c.2.2.2
                              linarith only [h3748, hlam, p3750_0]
                            · have p3750_0 := h3750c.1
                              have p3750_1 := h3750c.2.1
                              have p3750_2 := h3750c.2.2.1
                              have p3750_3 := h3750c.2.2.2
                              linarith only [h3749, hlam, p3750_0]
                            · have p3750_0 := h3750c.1
                              have p3750_1 := h3750c.2.1
                              have p3750_2 := h3750c.2.2.1
                              have p3750_3 := h3750c.2.2.2
                              linarith only [hlam, p3750_0]
                          · linarith only [h0, h3355, h3743, h3745, h3749, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                        · linarith only [h0, h3355, h3743, h3745, h3748, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · linarith only [h0, h3355, h3743, h3744, h3747, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                    · linarith only [h0, h3355, h3737, h3741, h3743, h3746, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                  · linarith only [h0, h3355, h3741, h3745, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h0, h3355, h3735, h3743, h3744, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3786 | h3786
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3787 | h3787
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3788 | h3788
                    · linarith only [h0, h3355, h3741, h3743, h3788, hc12, hc23, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3790 | h3790
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3791 | h3791
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3792 | h3792
                          · rcases h5bigk with h3793c | h3793c | h3793c | h3793c | h3793c | h3793c | h3793c | h3793c | h3793c | h3793c | h3793c | h3793c | h3793c | h3793c | h3793c | h3793c | h3793c | h3793c | h3793c | h3793c | h3793c | h3793c | h3793c | h3793c | h3793c
                            · have p3793_0 := h3793c.1
                              have p3793_1 := h3793c.2.1
                              have p3793_2 := h3793c.2.2.1
                              have p3793_3 := h3793c.2.2.2
                              linarith only [hlam, p3793_0]
                            · have p3793_0 := h3793c.1
                              have p3793_1 := h3793c.2.1
                              have p3793_2 := h3793c.2.2.1
                              have p3793_3 := h3793c.2.2.2
                              linarith only [h0, h3355, h3741, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3793_1, u1elo3]
                            · have p3793_0 := h3793c.1
                              have p3793_1 := h3793c.2.1
                              have p3793_2 := h3793c.2.2.1
                              have p3793_3 := h3793c.2.2.2
                              linarith only [h3530, hlam, p3793_0]
                            · have p3793_0 := h3793c.1
                              have p3793_1 := h3793c.2.1
                              have p3793_2 := h3793c.2.2.1
                              have p3793_3 := h3793c.2.2.2
                              linarith only [h0, h3355, hc35, hlam, hphi, ht01, ht0b, ht5b, p3793_1, u1elo3]
                            · have p3793_0 := h3793c.1
                              have p3793_1 := h3793c.2.1
                              have p3793_2 := h3793c.2.2.1
                              have p3793_3 := h3793c.2.2.2
                              linarith only [h0, h3355, hc45, hlam, hphi, ht01, ht0b, ht5b, p3793_1, u1elo3]
                            · have p3793_0 := h3793c.1
                              have p3793_1 := h3793c.2.1
                              have p3793_2 := h3793c.2.2.1
                              have p3793_3 := h3793c.2.2.2
                              linarith only [h3355, hlam, p3793_0]
                            · have p3793_0 := h3793c.1
                              have p3793_1 := h3793c.2.1
                              have p3793_2 := h3793c.2.2.1
                              have p3793_3 := h3793c.2.2.2
                              linarith only [hlam, p3793_0]
                            · have p3793_0 := h3793c.1
                              have p3793_1 := h3793c.2.1
                              have p3793_2 := h3793c.2.2.1
                              have p3793_3 := h3793c.2.2.2
                              linarith only [h3741, hlam, p3793_0]
                            · have p3793_0 := h3793c.1
                              have p3793_1 := h3793c.2.1
                              have p3793_2 := h3793c.2.2.1
                              have p3793_3 := h3793c.2.2.2
                              linarith only [h3792, hc45, hlam, hphi, ht01, ht0b, ht5b, p3793_1, u1elo4]
                            · have p3793_0 := h3793c.1
                              have p3793_1 := h3793c.2.1
                              have p3793_2 := h3793c.2.2.1
                              have p3793_3 := h3793c.2.2.2
                              linarith only [h0, h3355, hc45, hlam, hphi, ht01, ht0b, ht5b, p3793_1, u1elo3]
                            · have p3793_0 := h3793c.1
                              have p3793_1 := h3793c.2.1
                              have p3793_2 := h3793c.2.2.1
                              have p3793_3 := h3793c.2.2.2
                              linarith only [h3788, h3790, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3793_1]
                            · have p3793_0 := h3793c.1
                              have p3793_1 := h3793c.2.1
                              have p3793_2 := h3793c.2.2.1
                              have p3793_3 := h3793c.2.2.2
                              linarith only [h3788, h3790, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3793_1]
                            · have p3793_0 := h3793c.1
                              have p3793_1 := h3793c.2.1
                              have p3793_2 := h3793c.2.2.1
                              have p3793_3 := h3793c.2.2.2
                              linarith only [hlam, p3793_0]
                            · have p3793_0 := h3793c.1
                              have p3793_1 := h3793c.2.1
                              have p3793_2 := h3793c.2.2.1
                              have p3793_3 := h3793c.2.2.2
                              linarith only [h0, h3355, h3741, h3788, h3790, h3792, hc12, hc34, hc45, hlam, hphi, ht01, ht0b, ht23, ht5b, p3793_1, u1elo3]
                            · have p3793_0 := h3793c.1
                              have p3793_1 := h3793c.2.1
                              have p3793_2 := h3793c.2.2.1
                              have p3793_3 := h3793c.2.2.2
                              linarith only [h0, h3355, h3741, h3788, h3790, hc12, hc34, hc45, hlam, hphi, ht01, ht0b, ht23, ht5b, p3793_1, u1elo3]
                            · have p3793_0 := h3793c.1
                              have p3793_1 := h3793c.2.1
                              have p3793_2 := h3793c.2.2.1
                              have p3793_3 := h3793c.2.2.2
                              linarith only [h3735, hlam, p3793_0]
                            · have p3793_0 := h3793c.1
                              have p3793_1 := h3793c.2.1
                              have p3793_2 := h3793c.2.2.1
                              have p3793_3 := h3793c.2.2.2
                              linarith only [h3786, hlam, p3793_0]
                            · have p3793_0 := h3793c.1
                              have p3793_1 := h3793c.2.1
                              have p3793_2 := h3793c.2.2.1
                              have p3793_3 := h3793c.2.2.2
                              linarith only [h3790, hlam, p3793_0]
                            · have p3793_0 := h3793c.1
                              have p3793_1 := h3793c.2.1
                              have p3793_2 := h3793c.2.2.1
                              have p3793_3 := h3793c.2.2.2
                              linarith only [hlam, p3793_0]
                            · have p3793_0 := h3793c.1
                              have p3793_1 := h3793c.2.1
                              have p3793_2 := h3793c.2.2.1
                              have p3793_3 := h3793c.2.2.2
                              linarith only [h3786, hc45, hlam, hphi, ht01, ht0b, ht5b, p3793_1, u1elo2]
                            · have p3793_0 := h3793c.1
                              have p3793_1 := h3793c.2.1
                              have p3793_2 := h3793c.2.2.1
                              have p3793_3 := h3793c.2.2.2
                              linarith only [h3736, hlam, p3793_0]
                            · have p3793_0 := h3793c.1
                              have p3793_1 := h3793c.2.1
                              have p3793_2 := h3793c.2.2.1
                              have p3793_3 := h3793c.2.2.2
                              linarith only [h3787, hlam, p3793_0]
                            · have p3793_0 := h3793c.1
                              have p3793_1 := h3793c.2.1
                              have p3793_2 := h3793c.2.2.1
                              have p3793_3 := h3793c.2.2.2
                              linarith only [h3791, hlam, p3793_0]
                            · have p3793_0 := h3793c.1
                              have p3793_1 := h3793c.2.1
                              have p3793_2 := h3793c.2.2.1
                              have p3793_3 := h3793c.2.2.2
                              linarith only [h3792, hlam, p3793_0]
                            · have p3793_0 := h3793c.1
                              have p3793_1 := h3793c.2.1
                              have p3793_2 := h3793c.2.2.1
                              have p3793_3 := h3793c.2.2.2
                              linarith only [hlam, p3793_0]
                          · linarith only [h3530, h3788, h3790, h3792, hc02, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h0, h3355, h3737, h3787, h3791, hlam]
                      · linarith only [h0, h3355, h3786, h3790, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                  · linarith only [h0, h3355, h3736, h3741, h3787, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3823 | h3823
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3824 | h3824
                    · linarith only [h0, h3355, h3741, h3743, h3824, hc12, hc23, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3826 | h3826
                      · linarith only [h3786, h3824, h3826, hc13, hc34, hlam, hphi]
                      · linarith only [h3530, h3735, h3826, hlam]
                  · linarith only [h0, h3355, h3741, h3823, hc12, hc45, hlam, hphi, ht23, ht34]
        · linarith only [h0, h3355, h3736, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3831 | h3831
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3832 | h3832
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3833 | h3833
            · linarith only [h3355, h3530, h3833, hlam]
            · linarith only [h3356, h3832, h3833, hc02, hc25, hlam, hphi]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3836 | h3836
            · linarith only [h3530, h3832, h3836, hc02, hc24, hlam, hphi]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3838 | h3838
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3839 | h3839
                · linarith only [h0, h3355, h3735, h3839, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                · linarith only [h0, h3355, h3836, h3838, h3839, hc12, hc35, hlam, hphi, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3842 | h3842
                · linarith only [h3735, h3838, h3842, hc03, hc34, hlam, hphi]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3844 | h3844
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3845 | h3845
                    · linarith only [h0, h3355, h3836, h3838, h3845, hc12, hc23, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3847 | h3847
                      · linarith only [h3842, h3845, h3847, hc13, hc34, hlam, hphi]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3849 | h3849
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3850 | h3850
                          · rcases h5bigk with h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c
                            · have p3851_0 := h3851c.1
                              have p3851_1 := h3851c.2.1
                              have p3851_2 := h3851c.2.2.1
                              have p3851_3 := h3851c.2.2.2
                              linarith only [hlam, p3851_0]
                            · have p3851_0 := h3851c.1
                              have p3851_1 := h3851c.2.1
                              have p3851_2 := h3851c.2.2.1
                              have p3851_3 := h3851c.2.2.2
                              linarith only [h0, h3355, h3836, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3851_1, u1elo3]
                            · have p3851_0 := h3851c.1
                              have p3851_1 := h3851c.2.1
                              have p3851_2 := h3851c.2.2.1
                              have p3851_3 := h3851c.2.2.2
                              linarith only [h3530, hlam, p3851_0]
                            · have p3851_0 := h3851c.1
                              have p3851_1 := h3851c.2.1
                              have p3851_2 := h3851c.2.2.1
                              have p3851_3 := h3851c.2.2.2
                              linarith only [h3735, hlam, p3851_1]
                            · have p3851_0 := h3851c.1
                              have p3851_1 := h3851c.2.1
                              have p3851_2 := h3851c.2.2.1
                              have p3851_3 := h3851c.2.2.2
                              linarith only [h0, h3355, hc45, hlam, hphi, ht01, ht0b, ht5b, p3851_1, u1elo3]
                            · have p3851_0 := h3851c.1
                              have p3851_1 := h3851c.2.1
                              have p3851_2 := h3851c.2.2.1
                              have p3851_3 := h3851c.2.2.2
                              linarith only [h3355, hlam, p3851_0]
                            · have p3851_0 := h3851c.1
                              have p3851_1 := h3851c.2.1
                              have p3851_2 := h3851c.2.2.1
                              have p3851_3 := h3851c.2.2.2
                              linarith only [hlam, p3851_0]
                            · have p3851_0 := h3851c.1
                              have p3851_1 := h3851c.2.1
                              have p3851_2 := h3851c.2.2.1
                              have p3851_3 := h3851c.2.2.2
                              linarith only [h3836, hlam, p3851_0]
                            · have p3851_0 := h3851c.1
                              have p3851_1 := h3851c.2.1
                              have p3851_2 := h3851c.2.2.1
                              have p3851_3 := h3851c.2.2.2
                              linarith only [h3842, hlam, p3851_1]
                            · have p3851_0 := h3851c.1
                              have p3851_1 := h3851c.2.1
                              have p3851_2 := h3851c.2.2.1
                              have p3851_3 := h3851c.2.2.2
                              linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p3851_1, u1elo4]
                            · have p3851_0 := h3851c.1
                              have p3851_1 := h3851c.2.1
                              have p3851_2 := h3851c.2.2.1
                              have p3851_3 := h3851c.2.2.2
                              linarith only [h3530, h3847, hc02, hc35, hlam, hphi, ht23, p3851_1]
                            · have p3851_0 := h3851c.1
                              have p3851_1 := h3851c.2.1
                              have p3851_2 := h3851c.2.2.1
                              have p3851_3 := h3851c.2.2.2
                              linarith only [h3836, h3847, hc12, hc35, hlam, hphi, ht23, p3851_1]
                            · have p3851_0 := h3851c.1
                              have p3851_1 := h3851c.2.1
                              have p3851_2 := h3851c.2.2.1
                              have p3851_3 := h3851c.2.2.2
                              linarith only [hlam, p3851_0]
                            · have p3851_0 := h3851c.1
                              have p3851_1 := h3851c.2.1
                              have p3851_2 := h3851c.2.2.1
                              have p3851_3 := h3851c.2.2.2
                              linarith only [h3847, hlam, p3851_1]
                            · have p3851_0 := h3851c.1
                              have p3851_1 := h3851c.2.1
                              have p3851_2 := h3851c.2.2.1
                              have p3851_3 := h3851c.2.2.2
                              rcases p3851_3 (m.d 0 5) (by simp) with h3866 | h3866
                              · linarith only [h3530, h3866, hlam]
                              · linarith only [h3831, h3866, hlam]
                            · have p3851_0 := h3851c.1
                              have p3851_1 := h3851c.2.1
                              have p3851_2 := h3851c.2.2.1
                              have p3851_3 := h3851c.2.2.2
                              linarith only [h3355, h3836, h3850, hc12, hc34, hlam, hphi, ht23, p3851_1]
                            · have p3851_0 := h3851c.1
                              have p3851_1 := h3851c.2.1
                              have p3851_2 := h3851c.2.2.1
                              have p3851_3 := h3851c.2.2.2
                              linarith only [h3836, h3850, hc12, hc34, hlam, hphi, ht23, p3851_1]
                            · have p3851_0 := h3851c.1
                              have p3851_1 := h3851c.2.1
                              have p3851_2 := h3851c.2.2.1
                              have p3851_3 := h3851c.2.2.2
                              linarith only [h3530, h3850, hc02, hc34, hlam, hphi, ht23, p3851_1]
                            · have p3851_0 := h3851c.1
                              have p3851_1 := h3851c.2.1
                              have p3851_2 := h3851c.2.2.1
                              have p3851_3 := h3851c.2.2.2
                              linarith only [hlam, p3851_0]
                            · have p3851_0 := h3851c.1
                              have p3851_1 := h3851c.2.1
                              have p3851_2 := h3851c.2.2.1
                              have p3851_3 := h3851c.2.2.2
                              rcases p3851_3 (m.d 0 5) (by simp) with h3873 | h3873
                              · linarith only [h3735, h3873, hlam]
                              · linarith only [h3831, h3873, hlam]
                            · have p3851_0 := h3851c.1
                              have p3851_1 := h3851c.2.1
                              have p3851_2 := h3851c.2.2.1
                              have p3851_3 := h3851c.2.2.2
                              linarith only [h3831, hlam, p3851_0]
                            · have p3851_0 := h3851c.1
                              have p3851_1 := h3851c.2.1
                              have p3851_2 := h3851c.2.2.1
                              have p3851_3 := h3851c.2.2.2
                              linarith only [h3844, hlam, p3851_0]
                            · have p3851_0 := h3851c.1
                              have p3851_1 := h3851c.2.1
                              have p3851_2 := h3851c.2.2.1
                              have p3851_3 := h3851c.2.2.2
                              linarith only [h3849, hlam, p3851_0]
                            · have p3851_0 := h3851c.1
                              have p3851_1 := h3851c.2.1
                              have p3851_2 := h3851c.2.2.1
                              have p3851_3 := h3851c.2.2.2
                              linarith only [h3850, hlam, p3851_0]
                            · have p3851_0 := h3851c.1
                              have p3851_1 := h3851c.2.1
                              have p3851_2 := h3851c.2.2.1
                              have p3851_3 := h3851c.2.2.2
                              linarith only [hlam, p3851_0]
                          · linarith only [h0, h3831, h3838, h3850, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                        · linarith only [h0, h3355, h3832, h3844, h3849, hlam]
                  · linarith only [h0, h3355, h3836, h3844, hc12, hc45, hlam, hphi, ht23, ht34]
        · linarith only [h0, h3355, h3831, hlam]

end R2N4
