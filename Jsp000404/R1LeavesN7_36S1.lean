import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_36S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7634000 in
theorem r1l7_10_12_13_25_L_0_L_I_L_I_M_IR_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h327 | h327
  · rcases m.htr 0 2 5 (by decide) (by decide) with h328 | h328
    · rcases m.htr 0 3 4 (by decide) (by decide) with h329 | h329
      · rcases m.htr 0 3 5 (by decide) (by decide) with h330 | h330
        · rcases m.htr 0 4 5 (by decide) (by decide) with h331 | h331
          · rcases m.htr 1 2 3 (by decide) (by decide) with h332 | h332
            · linarith only [h2, h328, h332, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h334 | h334
              · rcases m.htr 1 2 5 (by decide) (by decide) with h335 | h335
                · linarith only [h1, h332, h335, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                · linarith only [h2, h328, h335, hc12, hc23, hlam, hphi]
              · linarith only [h2, h327, h334, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h339 | h339
            · linarith only [h2, h328, h339, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h341 | h341
              · rcases m.htr 1 2 5 (by decide) (by decide) with h342 | h342
                · linarith only [h1, h339, h342, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                · linarith only [h2, h328, h342, hc12, hc23, hlam, hphi]
              · linarith only [h2, h327, h341, hc12, hc23, hlam, hphi]
        · linarith only [h2, h328, h330, hlam]
      · linarith only [h2, h327, h329, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h348 | h348
      · rcases m.htr 0 3 5 (by decide) (by decide) with h349 | h349
        · rcases m.htr 0 4 5 (by decide) (by decide) with h350 | h350
          · linarith only [h327, h328, h350, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h352 | h352
            · linarith only [h0, h2, h327, h352, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h354 | h354
              · rcases m.htr 1 2 5 (by decide) (by decide) with h355 | h355
                · linarith only [h0, h328, h355, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h357 | h357
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h358 | h358
                    · linarith only [h1, h358, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                    · linarith only [h349, h357, h358, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · linarith only [h1, h348, h352, h354, h357, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · linarith only [h327, h328, h354, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h363 | h363
          · linarith only [h2, h327, h349, h363, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h365 | h365
            · linarith only [h0, h2, h365, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h367 | h367
              · rcases m.htr 1 2 5 (by decide) (by decide) with h368 | h368
                · linarith only [h0, h368, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h370 | h370
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h371 | h371
                    · linarith only [h1, h349, h371, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h373 | h373
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h374 | h374
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h375 | h375
                          · linarith only [h0, h2, h349, h363, h367, h375, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h377 | h377
                            · linarith only [h0, h2, h349, h367, h373, h374, h375, h377, hlam]
                            · rcases h2bigk with h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [hlam, p379_0]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [h2, h349, h367, h373, h374, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p379_1]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [h2, hlam, p379_0]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [h2, h349, h373, h374, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p379_1]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [h328, hlam, p379_0]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [h0, hlam, p379_0]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [hlam, p379_0]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [h365, hlam, p379_0]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [h0, h373, hc34, hlam, hphi, ht0b, ht45, ht5b, p379_1, u0elo0]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [h368, hlam, p379_0]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                rcases p379_3 (m.d 0 2) (by simp) with h390 | h390
                                · linarith only [h390, hlam, p379_0]
                                · rcases p379_3 (m.d 1 2) (by simp) with h392 | h392
                                  · linarith only [h365, h392, hlam]
                                  · rcases p379_3 (m.d 2 3) (by simp) with h394 | h394
                                    · rcases p379_3 (m.d 2 4) (by simp) with h395 | h395
                                      · linarith only [h373, h395, hlam]
                                      · rcases p379_3 (m.d 2 5) (by simp) with h397 | h397
                                        · linarith only [h374, h397, hlam]
                                        · linarith only [h328, h397, hlam]
                                    · linarith only [h394, hlam, p379_0]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                rcases p379_3 (m.d 0 2) (by simp) with h401 | h401
                                · linarith only [h2, h401, hlam]
                                · linarith only [h0, h401, hlam]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [hlam, p379_0]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [h2, h327, h349, h374, hlam, p379_2]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [h2, h349, h374, hc02, hc23, hlam, hphi, p379_1]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [h327, hlam, p379_0]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [h367, hlam, p379_0]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [h373, hlam, p379_1]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [hlam, p379_0]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [h375, hlam, p379_1]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [h0, h367, h375, hc24, hc45, hlam, hphi, p379_1]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [h367, h375, hc24, hc45, hlam, hphi, p379_1]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [h374, hlam, p379_1]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                rcases p379_3 (m.d 0 2) (by simp) with h415 | h415
                                · linarith only [h328, h415, hlam]
                                · linarith only [h327, h415, hlam]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [hlam, p379_0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h419 | h419
                          · linarith only [h0, h367, h419, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h421 | h421
                            · linarith only [h0, h2, h367, h373, h374, h419, h421, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                            · linarith only [h0, h2, h367, h373, h374, h421, hc34, hc45, hlam, hphi]
                      · linarith only [h0, h2, h348, h367, h373, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · linarith only [h348, h349, h370, hc13, hc35, hlam, hphi]
              · linarith only [h2, h327, h367, hc12, hc23, hlam, hphi]
      · linarith only [h2, h327, h348, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h428 | h428
    · rcases m.htr 0 3 4 (by decide) (by decide) with h429 | h429
      · rcases m.htr 0 3 5 (by decide) (by decide) with h430 | h430
        · rcases m.htr 0 4 5 (by decide) (by decide) with h431 | h431
          · rcases m.htr 1 2 3 (by decide) (by decide) with h432 | h432
            · linarith only [h2, h428, h432, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h434 | h434
              · linarith only [h1, h327, h428, h432, h434, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h436 | h436
                · linarith only [h1, h432, h436, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                · linarith only [h2, h428, h436, hc12, hc23, hlam, hphi]
          · linarith only [h327, h428, h431, hlam]
        · linarith only [h327, h428, h429, h430, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h441 | h441
        · rcases m.htr 0 4 5 (by decide) (by decide) with h442 | h442
          · rcases m.htr 1 2 3 (by decide) (by decide) with h443 | h443
            · linarith only [h2, h428, h443, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h445 | h445
              · linarith only [h1, h327, h428, h443, h445, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h447 | h447
                · linarith only [h1, h443, h447, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                · linarith only [h2, h428, h447, hc12, hc23, hlam, hphi]
          · linarith only [h2, h428, h429, h442, hlam]
        · linarith only [h2, h428, h441, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h452 | h452
      · rcases m.htr 0 3 5 (by decide) (by decide) with h453 | h453
        · rcases m.htr 0 4 5 (by decide) (by decide) with h454 | h454
          · rcases m.htr 1 2 3 (by decide) (by decide) with h455 | h455
            · linarith only [h0, h2, h455, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h457 | h457
              · linarith only [h0, h327, h457, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h459 | h459
                · linarith only [h0, h428, h459, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h461 | h461
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h462 | h462
                    · linarith only [h1, h462, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                    · linarith only [h453, h461, h462, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h465 | h465
                    · linarith only [h1, h465, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h467 | h467
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h468 | h468
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h469 | h469
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h470 | h470
                            · linarith only [h1, h452, h470, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                            · linarith only [h1, h452, h454, h455, h461, h470, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h0, h1, h327, h452, h454, h469, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h2, h452, h455, h461, h468, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h2, h452, h467, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h476 | h476
            · linarith only [h0, h2, h453, h476, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h478 | h478
              · linarith only [h0, h327, h478, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h480 | h480
                · linarith only [h0, h480, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h482 | h482
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h483 | h483
                    · linarith only [h1, h483, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                    · linarith only [h1, h453, h482, h483, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h486 | h486
                    · linarith only [h1, h486, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h488 | h488
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h489 | h489
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h490 | h490
                          · linarith only [h452, h454, h476, h482, h488, h490, hc12, hc23, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h492 | h492
                            · linarith only [h1, h452, h492, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                            · rcases h2bigk with h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c
                              · have p494_0 := h494c.1
                                have p494_1 := h494c.2.1
                                have p494_2 := h494c.2.2.1
                                have p494_3 := h494c.2.2.2
                                linarith only [hlam, p494_0]
                              · have p494_0 := h494c.1
                                have p494_1 := h494c.2.1
                                have p494_2 := h494c.2.2.1
                                have p494_3 := h494c.2.2.2
                                linarith only [h2, hc12, hc23, hlam, hphi, p494_1]
                              · have p494_0 := h494c.1
                                have p494_1 := h494c.2.1
                                have p494_2 := h494c.2.2.1
                                have p494_3 := h494c.2.2.2
                                linarith only [h2, hlam, p494_0]
                              · have p494_0 := h494c.1
                                have p494_1 := h494c.2.1
                                have p494_2 := h494c.2.2.1
                                have p494_3 := h494c.2.2.2
                                linarith only [h327, hlam, p494_0]
                              · have p494_0 := h494c.1
                                have p494_1 := h494c.2.1
                                have p494_2 := h494c.2.2.1
                                have p494_3 := h494c.2.2.2
                                linarith only [h428, hlam, p494_0]
                              · have p494_0 := h494c.1
                                have p494_1 := h494c.2.1
                                have p494_2 := h494c.2.2.1
                                have p494_3 := h494c.2.2.2
                                linarith only [h0, hlam, p494_0]
                              · have p494_0 := h494c.1
                                have p494_1 := h494c.2.1
                                have p494_2 := h494c.2.2.1
                                have p494_3 := h494c.2.2.2
                                linarith only [hlam, p494_0]
                              · have p494_0 := h494c.1
                                have p494_1 := h494c.2.1
                                have p494_2 := h494c.2.2.1
                                have p494_3 := h494c.2.2.2
                                linarith only [h476, hlam, p494_0]
                              · have p494_0 := h494c.1
                                have p494_1 := h494c.2.1
                                have p494_2 := h494c.2.2.1
                                have p494_3 := h494c.2.2.2
                                linarith only [h478, hlam, p494_0]
                              · have p494_0 := h494c.1
                                have p494_1 := h494c.2.1
                                have p494_2 := h494c.2.2.1
                                have p494_3 := h494c.2.2.2
                                linarith only [h480, hlam, p494_0]
                              · have p494_0 := h494c.1
                                have p494_1 := h494c.2.1
                                have p494_2 := h494c.2.2.1
                                have p494_3 := h494c.2.2.2
                                rcases p494_3 (m.d 0 2) (by simp) with h505 | h505
                                · linarith only [h505, hlam, p494_0]
                                · rcases p494_3 (m.d 1 2) (by simp) with h507 | h507
                                  · linarith only [h476, h507, hlam]
                                  · rcases p494_3 (m.d 2 3) (by simp) with h509 | h509
                                    · rcases p494_3 (m.d 2 4) (by simp) with h510 | h510
                                      · linarith only [h488, h510, hlam]
                                      · linarith only [h327, h510, hlam]
                                    · linarith only [h509, hlam, p494_0]
                              · have p494_0 := h494c.1
                                have p494_1 := h494c.2.1
                                have p494_2 := h494c.2.2.1
                                have p494_3 := h494c.2.2.2
                                rcases p494_3 (m.d 0 2) (by simp) with h514 | h514
                                · linarith only [h2, h514, hlam]
                                · linarith only [h0, h514, hlam]
                              · have p494_0 := h494c.1
                                have p494_1 := h494c.2.1
                                have p494_2 := h494c.2.2.1
                                have p494_3 := h494c.2.2.2
                                linarith only [hlam, p494_0]
                              · have p494_0 := h494c.1
                                have p494_1 := h494c.2.1
                                have p494_2 := h494c.2.2.1
                                have p494_3 := h494c.2.2.2
                                linarith only [h327, hc02, hc23, hlam, hphi, p494_1]
                              · have p494_0 := h494c.1
                                have p494_1 := h494c.2.1
                                have p494_2 := h494c.2.2.1
                                have p494_3 := h494c.2.2.2
                                linarith only [h428, h452, h454, h476, h482, hc12, hc23, hlam, hphi, p494_1]
                              · have p494_0 := h494c.1
                                have p494_1 := h494c.2.1
                                have p494_2 := h494c.2.2.1
                                have p494_3 := h494c.2.2.2
                                linarith only [h0, h490, hc12, hc45, hlam, hphi, ht23, ht34, p494_1]
                              · have p494_0 := h494c.1
                                have p494_1 := h494c.2.1
                                have p494_2 := h494c.2.2.1
                                have p494_3 := h494c.2.2.2
                                linarith only [h490, hc12, hc45, hlam, hphi, ht23, ht34, p494_1]
                              · have p494_0 := h494c.1
                                have p494_1 := h494c.2.1
                                have p494_2 := h494c.2.2.1
                                have p494_3 := h494c.2.2.2
                                linarith only [h488, hlam, p494_1]
                              · have p494_0 := h494c.1
                                have p494_1 := h494c.2.1
                                have p494_2 := h494c.2.2.1
                                have p494_3 := h494c.2.2.2
                                linarith only [hlam, p494_0]
                              · have p494_0 := h494c.1
                                have p494_1 := h494c.2.1
                                have p494_2 := h494c.2.2.1
                                have p494_3 := h494c.2.2.2
                                linarith only [h490, hlam, p494_1]
                              · have p494_0 := h494c.1
                                have p494_1 := h494c.2.1
                                have p494_2 := h494c.2.2.1
                                have p494_3 := h494c.2.2.2
                                rcases p494_3 (m.d 0 2) (by simp) with h525 | h525
                                · linarith only [h525, hlam, p494_0]
                                · rcases p494_3 (m.d 1 2) (by simp) with h527 | h527
                                  · linarith only [h480, h527, hlam]
                                  · rcases p494_3 (m.d 2 3) (by simp) with h529 | h529
                                    · rcases p494_3 (m.d 2 4) (by simp) with h530 | h530
                                      · linarith only [h490, h530, hlam]
                                      · linarith only [h327, h530, hlam]
                                    · linarith only [h2, h529, hlam]
                              · have p494_0 := h494c.1
                                have p494_1 := h494c.2.1
                                have p494_2 := h494c.2.2.1
                                have p494_3 := h494c.2.2.2
                                rcases p494_3 (m.d 0 2) (by simp) with h534 | h534
                                · linarith only [h428, h534, hlam]
                                · linarith only [h0, h534, hlam]
                              · have p494_0 := h494c.1
                                have p494_1 := h494c.2.1
                                have p494_2 := h494c.2.2.1
                                have p494_3 := h494c.2.2.2
                                linarith only [h489, hlam, p494_1]
                              · have p494_0 := h494c.1
                                have p494_1 := h494c.2.1
                                have p494_2 := h494c.2.2.1
                                have p494_3 := h494c.2.2.2
                                linarith only [h0, h327, hc12, hc25, hlam, hphi, p494_1]
                              · have p494_0 := h494c.1
                                have p494_1 := h494c.2.1
                                have p494_2 := h494c.2.2.1
                                have p494_3 := h494c.2.2.2
                                linarith only [hlam, p494_0]
                        · linarith only [h0, h1, h2, h453, h489, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h2, h452, h488, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h542 | h542
          · linarith only [h452, h453, h542, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h544 | h544
            · linarith only [h0, h2, h452, h544, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h546 | h546
              · linarith only [h0, h327, h546, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h548 | h548
                · linarith only [h0, h548, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h550 | h550
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h551 | h551
                    · linarith only [h1, h551, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h553 | h553
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h554 | h554
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h555 | h555
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h556 | h556
                            · linarith only [h327, h452, h453, h542, h554, h556, hc02, hc23, hlam, hphi]
                            · rcases h2bigk with h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c
                              · have p558_0 := h558c.1
                                have p558_1 := h558c.2.1
                                have p558_2 := h558c.2.2.1
                                have p558_3 := h558c.2.2.2
                                linarith only [hlam, p558_0]
                              · have p558_0 := h558c.1
                                have p558_1 := h558c.2.1
                                have p558_2 := h558c.2.2.1
                                have p558_3 := h558c.2.2.2
                                linarith only [h2, hc12, hc23, hlam, hphi, p558_1]
                              · have p558_0 := h558c.1
                                have p558_1 := h558c.2.1
                                have p558_2 := h558c.2.2.1
                                have p558_3 := h558c.2.2.2
                                linarith only [h2, hlam, p558_0]
                              · have p558_0 := h558c.1
                                have p558_1 := h558c.2.1
                                have p558_2 := h558c.2.2.1
                                have p558_3 := h558c.2.2.2
                                linarith only [h327, hlam, p558_0]
                              · have p558_0 := h558c.1
                                have p558_1 := h558c.2.1
                                have p558_2 := h558c.2.2.1
                                have p558_3 := h558c.2.2.2
                                linarith only [h428, hlam, p558_0]
                              · have p558_0 := h558c.1
                                have p558_1 := h558c.2.1
                                have p558_2 := h558c.2.2.1
                                have p558_3 := h558c.2.2.2
                                linarith only [h0, hlam, p558_0]
                              · have p558_0 := h558c.1
                                have p558_1 := h558c.2.1
                                have p558_2 := h558c.2.2.1
                                have p558_3 := h558c.2.2.2
                                linarith only [hlam, p558_0]
                              · have p558_0 := h558c.1
                                have p558_1 := h558c.2.1
                                have p558_2 := h558c.2.2.1
                                have p558_3 := h558c.2.2.2
                                linarith only [h544, hlam, p558_0]
                              · have p558_0 := h558c.1
                                have p558_1 := h558c.2.1
                                have p558_2 := h558c.2.2.1
                                have p558_3 := h558c.2.2.2
                                linarith only [h546, hlam, p558_0]
                              · have p558_0 := h558c.1
                                have p558_1 := h558c.2.1
                                have p558_2 := h558c.2.2.1
                                have p558_3 := h558c.2.2.2
                                linarith only [h548, hlam, p558_0]
                              · have p558_0 := h558c.1
                                have p558_1 := h558c.2.1
                                have p558_2 := h558c.2.2.1
                                have p558_3 := h558c.2.2.2
                                rcases p558_3 (m.d 0 2) (by simp) with h569 | h569
                                · linarith only [h569, hlam, p558_0]
                                · rcases p558_3 (m.d 1 2) (by simp) with h571 | h571
                                  · linarith only [h544, h571, hlam]
                                  · rcases p558_3 (m.d 2 3) (by simp) with h573 | h573
                                    · rcases p558_3 (m.d 2 4) (by simp) with h574 | h574
                                      · linarith only [h553, h574, hlam]
                                      · linarith only [h327, h574, hlam]
                                    · linarith only [h573, hlam, p558_0]
                              · have p558_0 := h558c.1
                                have p558_1 := h558c.2.1
                                have p558_2 := h558c.2.2.1
                                have p558_3 := h558c.2.2.2
                                rcases p558_3 (m.d 0 2) (by simp) with h578 | h578
                                · linarith only [h2, h578, hlam]
                                · linarith only [h0, h578, hlam]
                              · have p558_0 := h558c.1
                                have p558_1 := h558c.2.1
                                have p558_2 := h558c.2.2.1
                                have p558_3 := h558c.2.2.2
                                linarith only [hlam, p558_0]
                              · have p558_0 := h558c.1
                                have p558_1 := h558c.2.1
                                have p558_2 := h558c.2.2.1
                                have p558_3 := h558c.2.2.2
                                linarith only [h327, h452, h453, h555, h556, hc02, hc23, hlam, hphi, p558_1]
                              · have p558_0 := h558c.1
                                have p558_1 := h558c.2.1
                                have p558_2 := h558c.2.2.1
                                have p558_3 := h558c.2.2.2
                                linarith only [h1, h453, h550, h555, h556, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p558_1]
                              · have p558_0 := h558c.1
                                have p558_1 := h558c.2.1
                                have p558_2 := h558c.2.2.1
                                have p558_3 := h558c.2.2.2
                                rcases p558_3 (m.d 0 2) (by simp) with h584 | h584
                                · linarith only [h584, hlam, p558_0]
                                · rcases p558_3 (m.d 1 2) (by simp) with h586 | h586
                                  · linarith only [h546, h586, hlam]
                                  · rcases p558_3 (m.d 2 3) (by simp) with h588 | h588
                                    · rcases p558_3 (m.d 2 4) (by simp) with h589 | h589
                                      · rcases p558_3 (m.d 2 5) (by simp) with h590 | h590
                                        · linarith only [h555, h590, hlam]
                                        · linarith only [h428, h590, hlam]
                                      · linarith only [h589, hlam, p558_0]
                                    · linarith only [h2, h588, hlam]
                              · have p558_0 := h558c.1
                                have p558_1 := h558c.2.1
                                have p558_2 := h558c.2.2.1
                                have p558_3 := h558c.2.2.2
                                rcases p558_3 (m.d 0 2) (by simp) with h595 | h595
                                · linarith only [h327, h595, hlam]
                                · linarith only [h0, h595, hlam]
                              · have p558_0 := h558c.1
                                have p558_1 := h558c.2.1
                                have p558_2 := h558c.2.2.1
                                have p558_3 := h558c.2.2.2
                                linarith only [h553, hlam, p558_1]
                              · have p558_0 := h558c.1
                                have p558_1 := h558c.2.1
                                have p558_2 := h558c.2.2.1
                                have p558_3 := h558c.2.2.2
                                linarith only [hlam, p558_0]
                              · have p558_0 := h558c.1
                                have p558_1 := h558c.2.1
                                have p558_2 := h558c.2.2.1
                                have p558_3 := h558c.2.2.2
                                linarith only [h1, h453, h550, h555, h556, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p558_1]
                              · have p558_0 := h558c.1
                                have p558_1 := h558c.2.1
                                have p558_2 := h558c.2.2.1
                                have p558_3 := h558c.2.2.2
                                rcases p558_3 (m.d 0 2) (by simp) with h601 | h601
                                · linarith only [h601, hlam, p558_0]
                                · rcases p558_3 (m.d 1 2) (by simp) with h603 | h603
                                  · linarith only [h548, h603, hlam]
                                  · rcases p558_3 (m.d 2 3) (by simp) with h605 | h605
                                    · rcases p558_3 (m.d 2 4) (by simp) with h606 | h606
                                      · rcases p558_3 (m.d 2 5) (by simp) with h607 | h607
                                        · rcases h3bigk with h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c
                                          · have p608_0 := h608c.1
                                            have p608_1 := h608c.2.1
                                            have p608_2 := h608c.2.2.1
                                            have p608_3 := h608c.2.2.2
                                            linarith only [hlam, p608_0]
                                          · have p608_0 := h608c.1
                                            have p608_1 := h608c.2.1
                                            have p608_2 := h608c.2.2.1
                                            have p608_3 := h608c.2.2.2
                                            linarith only [h550, hc34, hlam, hphi, ht0b, ht45, ht5b, p608_1, u0elo2]
                                          · have p608_0 := h608c.1
                                            have p608_1 := h608c.2.1
                                            have p608_2 := h608c.2.2.1
                                            have p608_3 := h608c.2.2.2
                                            linarith only [h2, hlam, p608_1]
                                          · have p608_0 := h608c.1
                                            have p608_1 := h608c.2.1
                                            have p608_2 := h608c.2.2.1
                                            have p608_3 := h608c.2.2.2
                                            linarith only [h453, h556, hc34, hc45, hlam, hphi, p608_1]
                                          · have p608_0 := h608c.1
                                            have p608_1 := h608c.2.1
                                            have p608_2 := h608c.2.2.1
                                            have p608_3 := h608c.2.2.2
                                            linarith only [h453, hlam, p608_0]
                                          · have p608_0 := h608c.1
                                            have p608_1 := h608c.2.1
                                            have p608_2 := h608c.2.2.1
                                            have p608_3 := h608c.2.2.2
                                            linarith only [h1, hlam, p608_0]
                                          · have p608_0 := h608c.1
                                            have p608_1 := h608c.2.1
                                            have p608_2 := h608c.2.2.1
                                            have p608_3 := h608c.2.2.2
                                            linarith only [hlam, p608_0]
                                          · have p608_0 := h608c.1
                                            have p608_1 := h608c.2.1
                                            have p608_2 := h608c.2.2.1
                                            have p608_3 := h608c.2.2.2
                                            linarith only [h544, hlam, p608_1]
                                          · have p608_0 := h608c.1
                                            have p608_1 := h608c.2.1
                                            have p608_2 := h608c.2.2.1
                                            have p608_3 := h608c.2.2.2
                                            linarith only [h1, hc34, hlam, hphi, ht0b, ht45, ht5b, p608_1, u0elo0]
                                          · have p608_0 := h608c.1
                                            have p608_1 := h608c.2.1
                                            have p608_2 := h608c.2.2.1
                                            have p608_3 := h608c.2.2.2
                                            linarith only [h551, hlam, p608_0]
                                          · have p608_0 := h608c.1
                                            have p608_1 := h608c.2.1
                                            have p608_2 := h608c.2.2.1
                                            have p608_3 := h608c.2.2.2
                                            rcases p608_3 (m.d 0 3) (by simp) with h619 | h619
                                            · linarith only [h2, h619, hlam]
                                            · rcases p608_3 (m.d 1 3) (by simp) with h621 | h621
                                              · linarith only [h544, h621, hlam]
                                              · rcases p608_3 (m.d 2 3) (by simp) with h623 | h623
                                                · rcases p608_3 (m.d 3 4) (by simp) with h624 | h624
                                                  · linarith only [h553, h624, hlam]
                                                  · rcases p608_3 (m.d 3 5) (by simp) with h626 | h626
                                                    · linarith only [h554, h626, hlam]
                                                    · linarith only [h453, h626, hlam]
                                                · linarith only [h2, h623, hlam]
                                          · have p608_0 := h608c.1
                                            have p608_1 := h608c.2.1
                                            have p608_2 := h608c.2.2.1
                                            have p608_3 := h608c.2.2.2
                                            rcases p608_3 (m.d 0 3) (by simp) with h630 | h630
                                            · linarith only [h2, h630, hlam]
                                            · linarith only [h1, h630, hlam]
                                          · have p608_0 := h608c.1
                                            have p608_1 := h608c.2.1
                                            have p608_2 := h608c.2.2.1
                                            have p608_3 := h608c.2.2.2
                                            linarith only [hlam, p608_0]
                                          · have p608_0 := h608c.1
                                            have p608_1 := h608c.2.1
                                            have p608_2 := h608c.2.2.1
                                            have p608_3 := h608c.2.2.2
                                            linarith only [h452, h453, h553, h555, h556, hlam, p608_2]
                                          · have p608_0 := h608c.1
                                            have p608_1 := h608c.2.1
                                            have p608_2 := h608c.2.2.1
                                            have p608_3 := h608c.2.2.2
                                            linarith only [h1, h453, h550, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p608_1]
                                          · have p608_0 := h608c.1
                                            have p608_1 := h608c.2.1
                                            have p608_2 := h608c.2.2.1
                                            have p608_3 := h608c.2.2.2
                                            linarith only [h452, hlam, p608_0]
                                          · have p608_0 := h608c.1
                                            have p608_1 := h608c.2.1
                                            have p608_2 := h608c.2.2.1
                                            have p608_3 := h608c.2.2.2
                                            linarith only [h550, hlam, p608_0]
                                          · have p608_0 := h608c.1
                                            have p608_1 := h608c.2.1
                                            have p608_2 := h608c.2.2.1
                                            have p608_3 := h608c.2.2.2
                                            linarith only [h553, hlam, p608_0]
                                          · have p608_0 := h608c.1
                                            have p608_1 := h608c.2.1
                                            have p608_2 := h608c.2.2.1
                                            have p608_3 := h608c.2.2.2
                                            linarith only [hlam, p608_0]
                                          · have p608_0 := h608c.1
                                            have p608_1 := h608c.2.1
                                            have p608_2 := h608c.2.2.1
                                            have p608_3 := h608c.2.2.2
                                            linarith only [h556, hlam, p608_1]
                                          · have p608_0 := h608c.1
                                            have p608_1 := h608c.2.1
                                            have p608_2 := h608c.2.2.1
                                            have p608_3 := h608c.2.2.2
                                            linarith only [h1, h550, h554, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p608_1]
                                          · have p608_0 := h608c.1
                                            have p608_1 := h608c.2.1
                                            have p608_2 := h608c.2.2.1
                                            have p608_3 := h608c.2.2.2
                                            linarith only [h550, h554, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p608_1]
                                          · have p608_0 := h608c.1
                                            have p608_1 := h608c.2.1
                                            have p608_2 := h608c.2.2.1
                                            have p608_3 := h608c.2.2.2
                                            linarith only [h554, hlam, p608_0]
                                          · have p608_0 := h608c.1
                                            have p608_1 := h608c.2.1
                                            have p608_2 := h608c.2.2.1
                                            have p608_3 := h608c.2.2.2
                                            rcases p608_3 (m.d 0 3) (by simp) with h644 | h644
                                            · linarith only [h453, h644, hlam]
                                            · linarith only [h452, h644, hlam]
                                          · have p608_0 := h608c.1
                                            have p608_1 := h608c.2.1
                                            have p608_2 := h608c.2.2.1
                                            have p608_3 := h608c.2.2.2
                                            linarith only [hlam, p608_0]
                                        · linarith only [h607, hlam, p558_0]
                                      · linarith only [h327, h606, hlam]
                                    · linarith only [h2, h605, hlam]
                              · have p558_0 := h558c.1
                                have p558_1 := h558c.2.1
                                have p558_2 := h558c.2.2.1
                                have p558_3 := h558c.2.2.2
                                rcases p558_3 (m.d 0 2) (by simp) with h651 | h651
                                · linarith only [h428, h651, hlam]
                                · linarith only [h0, h651, hlam]
                              · have p558_0 := h558c.1
                                have p558_1 := h558c.2.1
                                have p558_2 := h558c.2.2.1
                                have p558_3 := h558c.2.2.2
                                linarith only [h554, hlam, p558_1]
                              · have p558_0 := h558c.1
                                have p558_1 := h558c.2.1
                                have p558_2 := h558c.2.2.1
                                have p558_3 := h558c.2.2.2
                                linarith only [h555, hlam, p558_0]
                              · have p558_0 := h558c.1
                                have p558_1 := h558c.2.1
                                have p558_2 := h558c.2.2.1
                                have p558_3 := h558c.2.2.2
                                linarith only [hlam, p558_0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h657 | h657
                            · linarith only [h1, h550, h555, h657, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · rcases h2bigk with h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c | h659c
                              · have p659_0 := h659c.1
                                have p659_1 := h659c.2.1
                                have p659_2 := h659c.2.2.1
                                have p659_3 := h659c.2.2.2
                                linarith only [hlam, p659_0]
                              · have p659_0 := h659c.1
                                have p659_1 := h659c.2.1
                                have p659_2 := h659c.2.2.1
                                have p659_3 := h659c.2.2.2
                                linarith only [h327, hc12, hc24, hlam, hphi, p659_1]
                              · have p659_0 := h659c.1
                                have p659_1 := h659c.2.1
                                have p659_2 := h659c.2.2.1
                                have p659_3 := h659c.2.2.2
                                linarith only [h2, hlam, p659_0]
                              · have p659_0 := h659c.1
                                have p659_1 := h659c.2.1
                                have p659_2 := h659c.2.2.1
                                have p659_3 := h659c.2.2.2
                                linarith only [h327, hlam, p659_0]
                              · have p659_0 := h659c.1
                                have p659_1 := h659c.2.1
                                have p659_2 := h659c.2.2.1
                                have p659_3 := h659c.2.2.2
                                linarith only [h428, hlam, p659_0]
                              · have p659_0 := h659c.1
                                have p659_1 := h659c.2.1
                                have p659_2 := h659c.2.2.1
                                have p659_3 := h659c.2.2.2
                                linarith only [h0, hlam, p659_0]
                              · have p659_0 := h659c.1
                                have p659_1 := h659c.2.1
                                have p659_2 := h659c.2.2.1
                                have p659_3 := h659c.2.2.2
                                linarith only [hlam, p659_0]
                              · have p659_0 := h659c.1
                                have p659_1 := h659c.2.1
                                have p659_2 := h659c.2.2.1
                                have p659_3 := h659c.2.2.2
                                linarith only [h544, hlam, p659_0]
                              · have p659_0 := h659c.1
                                have p659_1 := h659c.2.1
                                have p659_2 := h659c.2.2.1
                                have p659_3 := h659c.2.2.2
                                linarith only [h546, hlam, p659_0]
                              · have p659_0 := h659c.1
                                have p659_1 := h659c.2.1
                                have p659_2 := h659c.2.2.1
                                have p659_3 := h659c.2.2.2
                                linarith only [h548, hlam, p659_0]
                              · have p659_0 := h659c.1
                                have p659_1 := h659c.2.1
                                have p659_2 := h659c.2.2.1
                                have p659_3 := h659c.2.2.2
                                rcases p659_3 (m.d 0 2) (by simp) with h670 | h670
                                · linarith only [h670, hlam, p659_0]
                                · rcases p659_3 (m.d 1 2) (by simp) with h672 | h672
                                  · linarith only [h544, h672, hlam]
                                  · rcases p659_3 (m.d 2 3) (by simp) with h674 | h674
                                    · rcases p659_3 (m.d 2 4) (by simp) with h675 | h675
                                      · linarith only [h553, h675, hlam]
                                      · linarith only [h327, h675, hlam]
                                    · linarith only [h674, hlam, p659_0]
                              · have p659_0 := h659c.1
                                have p659_1 := h659c.2.1
                                have p659_2 := h659c.2.2.1
                                have p659_3 := h659c.2.2.2
                                rcases p659_3 (m.d 0 2) (by simp) with h679 | h679
                                · linarith only [h2, h679, hlam]
                                · linarith only [h0, h679, hlam]
                              · have p659_0 := h659c.1
                                have p659_1 := h659c.2.1
                                have p659_2 := h659c.2.2.1
                                have p659_3 := h659c.2.2.2
                                linarith only [hlam, p659_0]
                              · have p659_0 := h659c.1
                                have p659_1 := h659c.2.1
                                have p659_2 := h659c.2.2.1
                                have p659_3 := h659c.2.2.2
                                linarith only [h327, hc02, hc23, hlam, hphi, p659_1]
                              · have p659_0 := h659c.1
                                have p659_1 := h659c.2.1
                                have p659_2 := h659c.2.2.1
                                have p659_3 := h659c.2.2.2
                                linarith only [h0, h428, hc12, hc23, hlam, hphi, p659_1]
                              · have p659_0 := h659c.1
                                have p659_1 := h659c.2.1
                                have p659_2 := h659c.2.2.1
                                have p659_3 := h659c.2.2.2
                                linarith only [h0, h555, hc12, hc45, hlam, hphi, ht23, ht34, p659_1]
                              · have p659_0 := h659c.1
                                have p659_1 := h659c.2.1
                                have p659_2 := h659c.2.2.1
                                have p659_3 := h659c.2.2.2
                                linarith only [h555, hc12, hc45, hlam, hphi, ht23, ht34, p659_1]
                              · have p659_0 := h659c.1
                                have p659_1 := h659c.2.1
                                have p659_2 := h659c.2.2.1
                                have p659_3 := h659c.2.2.2
                                linarith only [h553, hlam, p659_1]
                              · have p659_0 := h659c.1
                                have p659_1 := h659c.2.1
                                have p659_2 := h659c.2.2.1
                                have p659_3 := h659c.2.2.2
                                linarith only [hlam, p659_0]
                              · have p659_0 := h659c.1
                                have p659_1 := h659c.2.1
                                have p659_2 := h659c.2.2.1
                                have p659_3 := h659c.2.2.2
                                linarith only [h555, hlam, p659_1]
                              · have p659_0 := h659c.1
                                have p659_1 := h659c.2.1
                                have p659_2 := h659c.2.2.1
                                have p659_3 := h659c.2.2.2
                                rcases p659_3 (m.d 0 2) (by simp) with h690 | h690
                                · linarith only [h690, hlam, p659_0]
                                · rcases p659_3 (m.d 1 2) (by simp) with h692 | h692
                                  · linarith only [h548, h692, hlam]
                                  · rcases p659_3 (m.d 2 3) (by simp) with h694 | h694
                                    · rcases p659_3 (m.d 2 4) (by simp) with h695 | h695
                                      · linarith only [h555, h695, hlam]
                                      · linarith only [h327, h695, hlam]
                                    · linarith only [h2, h694, hlam]
                              · have p659_0 := h659c.1
                                have p659_1 := h659c.2.1
                                have p659_2 := h659c.2.2.1
                                have p659_3 := h659c.2.2.2
                                rcases p659_3 (m.d 0 2) (by simp) with h699 | h699
                                · linarith only [h428, h699, hlam]
                                · linarith only [h0, h699, hlam]
                              · have p659_0 := h659c.1
                                have p659_1 := h659c.2.1
                                have p659_2 := h659c.2.2.1
                                have p659_3 := h659c.2.2.2
                                linarith only [h554, hlam, p659_1]
                              · have p659_0 := h659c.1
                                have p659_1 := h659c.2.1
                                have p659_2 := h659c.2.2.1
                                have p659_3 := h659c.2.2.2
                                linarith only [h0, h327, hc12, hc25, hlam, hphi, p659_1]
                              · have p659_0 := h659c.1
                                have p659_1 := h659c.2.1
                                have p659_2 := h659c.2.2.1
                                have p659_3 := h659c.2.2.2
                                linarith only [hlam, p659_0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h705 | h705
                          · linarith only [h0, h327, h542, h553, h554, h705, hc12, hc35, hlam, hphi, ht23]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h707 | h707
                            · linarith only [h0, h1, h327, h550, h705, h707, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                            · rcases h2bigk with h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c
                              · have p709_0 := h709c.1
                                have p709_1 := h709c.2.1
                                have p709_2 := h709c.2.2.1
                                have p709_3 := h709c.2.2.2
                                linarith only [hlam, p709_0]
                              · have p709_0 := h709c.1
                                have p709_1 := h709c.2.1
                                have p709_2 := h709c.2.2.1
                                have p709_3 := h709c.2.2.2
                                linarith only [h327, hc12, hc24, hlam, hphi, p709_1]
                              · have p709_0 := h709c.1
                                have p709_1 := h709c.2.1
                                have p709_2 := h709c.2.2.1
                                have p709_3 := h709c.2.2.2
                                linarith only [h2, hlam, p709_0]
                              · have p709_0 := h709c.1
                                have p709_1 := h709c.2.1
                                have p709_2 := h709c.2.2.1
                                have p709_3 := h709c.2.2.2
                                linarith only [h327, hlam, p709_0]
                              · have p709_0 := h709c.1
                                have p709_1 := h709c.2.1
                                have p709_2 := h709c.2.2.1
                                have p709_3 := h709c.2.2.2
                                linarith only [h428, hlam, p709_0]
                              · have p709_0 := h709c.1
                                have p709_1 := h709c.2.1
                                have p709_2 := h709c.2.2.1
                                have p709_3 := h709c.2.2.2
                                linarith only [h0, hlam, p709_0]
                              · have p709_0 := h709c.1
                                have p709_1 := h709c.2.1
                                have p709_2 := h709c.2.2.1
                                have p709_3 := h709c.2.2.2
                                linarith only [hlam, p709_0]
                              · have p709_0 := h709c.1
                                have p709_1 := h709c.2.1
                                have p709_2 := h709c.2.2.1
                                have p709_3 := h709c.2.2.2
                                linarith only [h544, hlam, p709_0]
                              · have p709_0 := h709c.1
                                have p709_1 := h709c.2.1
                                have p709_2 := h709c.2.2.1
                                have p709_3 := h709c.2.2.2
                                linarith only [h546, hlam, p709_0]
                              · have p709_0 := h709c.1
                                have p709_1 := h709c.2.1
                                have p709_2 := h709c.2.2.1
                                have p709_3 := h709c.2.2.2
                                linarith only [h548, hlam, p709_0]
                              · have p709_0 := h709c.1
                                have p709_1 := h709c.2.1
                                have p709_2 := h709c.2.2.1
                                have p709_3 := h709c.2.2.2
                                linarith only [h554, h707, hc02, hc45, hlam, hphi, ht23, ht34, p709_1]
                              · have p709_0 := h709c.1
                                have p709_1 := h709c.2.1
                                have p709_2 := h709c.2.2.1
                                have p709_3 := h709c.2.2.2
                                linarith only [h554, h707, hc12, hc45, hlam, hphi, ht23, ht34, p709_1]
                              · have p709_0 := h709c.1
                                have p709_1 := h709c.2.1
                                have p709_2 := h709c.2.2.1
                                have p709_3 := h709c.2.2.2
                                linarith only [hlam, p709_0]
                              · have p709_0 := h709c.1
                                have p709_1 := h709c.2.1
                                have p709_2 := h709c.2.2.1
                                have p709_3 := h709c.2.2.2
                                linarith only [h554, h707, hc24, hc45, hlam, hphi, p709_1]
                              · have p709_0 := h709c.1
                                have p709_1 := h709c.2.1
                                have p709_2 := h709c.2.2.1
                                have p709_3 := h709c.2.2.2
                                linarith only [h554, hlam, p709_0]
                              · have p709_0 := h709c.1
                                have p709_1 := h709c.2.1
                                have p709_2 := h709c.2.2.1
                                have p709_3 := h709c.2.2.2
                                linarith only [h0, h553, h554, h707, hc12, hc45, hlam, hphi, ht23, ht34, p709_1]
                              · have p709_0 := h709c.1
                                have p709_1 := h709c.2.1
                                have p709_2 := h709c.2.2.1
                                have p709_3 := h709c.2.2.2
                                linarith only [h553, h554, h707, hc12, hc45, hlam, hphi, ht23, ht34, p709_1]
                              · have p709_0 := h709c.1
                                have p709_1 := h709c.2.1
                                have p709_2 := h709c.2.2.1
                                have p709_3 := h709c.2.2.2
                                linarith only [h553, hlam, p709_1]
                              · have p709_0 := h709c.1
                                have p709_1 := h709c.2.1
                                have p709_2 := h709c.2.2.1
                                have p709_3 := h709c.2.2.2
                                linarith only [hlam, p709_0]
                              · have p709_0 := h709c.1
                                have p709_1 := h709c.2.1
                                have p709_2 := h709c.2.2.1
                                have p709_3 := h709c.2.2.2
                                linarith only [h705, hlam, p709_1]
                              · have p709_0 := h709c.1
                                have p709_1 := h709c.2.1
                                have p709_2 := h709c.2.2.1
                                have p709_3 := h709c.2.2.2
                                rcases p709_3 (m.d 0 2) (by simp) with h730 | h730
                                · linarith only [h730, hlam, p709_0]
                                · rcases p709_3 (m.d 1 2) (by simp) with h732 | h732
                                  · linarith only [h548, h732, hlam]
                                  · rcases p709_3 (m.d 2 3) (by simp) with h734 | h734
                                    · linarith only [h554, h734, hlam]
                                    · linarith only [h2, h734, hlam]
                              · have p709_0 := h709c.1
                                have p709_1 := h709c.2.1
                                have p709_2 := h709c.2.2.1
                                have p709_3 := h709c.2.2.2
                                rcases p709_3 (m.d 0 2) (by simp) with h737 | h737
                                · linarith only [h428, h737, hlam]
                                · linarith only [h0, h737, hlam]
                              · have p709_0 := h709c.1
                                have p709_1 := h709c.2.1
                                have p709_2 := h709c.2.2.1
                                have p709_3 := h709c.2.2.2
                                linarith only [h1, h2, h550, h554, h707, hc34, hc45, hlam, hphi, p709_1]
                              · have p709_0 := h709c.1
                                have p709_1 := h709c.2.1
                                have p709_2 := h709c.2.2.1
                                have p709_3 := h709c.2.2.2
                                linarith only [h0, h327, h554, h707, hc12, hc45, hlam, hphi, ht23, ht34, p709_1]
                              · have p709_0 := h709c.1
                                have p709_1 := h709c.2.1
                                have p709_2 := h709c.2.2.1
                                have p709_3 := h709c.2.2.2
                                linarith only [hlam, p709_0]
                      · linarith only [h1, h550, h553, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h452, h453, h550, hc13, hc35, hlam, hphi]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h745 | h745
        · rcases m.htr 0 4 5 (by decide) (by decide) with h746 | h746
          · rcases m.htr 1 2 3 (by decide) (by decide) with h747 | h747
            · linarith only [h0, h2, h745, h747, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h749 | h749
              · linarith only [h0, h327, h749, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h751 | h751
                · linarith only [h0, h751, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h753 | h753
                  · linarith only [h1, h452, h745, h753, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h755 | h755
                    · linarith only [h1, h755, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                    · linarith only [h452, h745, h755, hc13, hc34, hlam, hphi]
          · linarith only [h452, h745, h746, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h759 | h759
          · rcases m.htr 1 2 3 (by decide) (by decide) with h760 | h760
            · linarith only [h0, h2, h760, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h762 | h762
              · linarith only [h0, h327, h759, h762, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h764 | h764
                · linarith only [h1, h760, h764, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h766 | h766
                  · linarith only [h1, h2, h452, h766, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h768 | h768
                    · linarith only [h1, h745, h768, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h770 | h770
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h771 | h771
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h772 | h772
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h773 | h773
                            · rcases h2bigk with h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c
                              · have p774_0 := h774c.1
                                have p774_1 := h774c.2.1
                                have p774_2 := h774c.2.2.1
                                have p774_3 := h774c.2.2.2
                                linarith only [hlam, p774_0]
                              · have p774_0 := h774c.1
                                have p774_1 := h774c.2.1
                                have p774_2 := h774c.2.2.1
                                have p774_3 := h774c.2.2.2
                                linarith only [h2, h745, h771, hc12, hc25, hlam, hphi, p774_1]
                              · have p774_0 := h774c.1
                                have p774_1 := h774c.2.1
                                have p774_2 := h774c.2.2.1
                                have p774_3 := h774c.2.2.2
                                linarith only [h2, hlam, p774_0]
                              · have p774_0 := h774c.1
                                have p774_1 := h774c.2.1
                                have p774_2 := h774c.2.2.1
                                have p774_3 := h774c.2.2.2
                                linarith only [h327, hlam, p774_0]
                              · have p774_0 := h774c.1
                                have p774_1 := h774c.2.1
                                have p774_2 := h774c.2.2.1
                                have p774_3 := h774c.2.2.2
                                linarith only [h428, hlam, p774_0]
                              · have p774_0 := h774c.1
                                have p774_1 := h774c.2.1
                                have p774_2 := h774c.2.2.1
                                have p774_3 := h774c.2.2.2
                                linarith only [h0, hlam, p774_0]
                              · have p774_0 := h774c.1
                                have p774_1 := h774c.2.1
                                have p774_2 := h774c.2.2.1
                                have p774_3 := h774c.2.2.2
                                linarith only [hlam, p774_0]
                              · have p774_0 := h774c.1
                                have p774_1 := h774c.2.1
                                have p774_2 := h774c.2.2.1
                                have p774_3 := h774c.2.2.2
                                linarith only [h760, hlam, p774_0]
                              · have p774_0 := h774c.1
                                have p774_1 := h774c.2.1
                                have p774_2 := h774c.2.2.1
                                have p774_3 := h774c.2.2.2
                                linarith only [h762, hlam, p774_0]
                              · have p774_0 := h774c.1
                                have p774_1 := h774c.2.1
                                have p774_2 := h774c.2.2.1
                                have p774_3 := h774c.2.2.2
                                linarith only [h764, hlam, p774_0]
                              · have p774_0 := h774c.1
                                have p774_1 := h774c.2.1
                                have p774_2 := h774c.2.2.1
                                have p774_3 := h774c.2.2.2
                                rcases p774_3 (m.d 0 2) (by simp) with h785 | h785
                                · linarith only [h785, hlam, p774_0]
                                · rcases p774_3 (m.d 1 2) (by simp) with h787 | h787
                                  · linarith only [h760, h787, hlam]
                                  · rcases p774_3 (m.d 2 3) (by simp) with h789 | h789
                                    · rcases p774_3 (m.d 2 4) (by simp) with h790 | h790
                                      · linarith only [h770, h790, hlam]
                                      · linarith only [h327, h790, hlam]
                                    · linarith only [h789, hlam, p774_0]
                              · have p774_0 := h774c.1
                                have p774_1 := h774c.2.1
                                have p774_2 := h774c.2.2.1
                                have p774_3 := h774c.2.2.2
                                rcases p774_3 (m.d 0 2) (by simp) with h794 | h794
                                · linarith only [h2, h794, hlam]
                                · linarith only [h0, h794, hlam]
                              · have p774_0 := h774c.1
                                have p774_1 := h774c.2.1
                                have p774_2 := h774c.2.2.1
                                have p774_3 := h774c.2.2.2
                                linarith only [hlam, p774_0]
                              · have p774_0 := h774c.1
                                have p774_1 := h774c.2.1
                                have p774_2 := h774c.2.2.1
                                have p774_3 := h774c.2.2.2
                                linarith only [h327, hc02, hc23, hlam, hphi, p774_1]
                              · have p774_0 := h774c.1
                                have p774_1 := h774c.2.1
                                have p774_2 := h774c.2.2.1
                                have p774_3 := h774c.2.2.2
                                linarith only [h0, h428, hc12, hc23, hlam, hphi, p774_1]
                              · have p774_0 := h774c.1
                                have p774_1 := h774c.2.1
                                have p774_2 := h774c.2.2.1
                                have p774_3 := h774c.2.2.2
                                rcases p774_3 (m.d 0 2) (by simp) with h800 | h800
                                · linarith only [h800, hlam, p774_0]
                                · rcases p774_3 (m.d 1 2) (by simp) with h802 | h802
                                  · linarith only [h762, h802, hlam]
                                  · rcases p774_3 (m.d 2 3) (by simp) with h804 | h804
                                    · rcases p774_3 (m.d 2 4) (by simp) with h805 | h805
                                      · rcases p774_3 (m.d 2 5) (by simp) with h806 | h806
                                        · linarith only [h772, h806, hlam]
                                        · linarith only [h428, h806, hlam]
                                      · linarith only [h805, hlam, p774_0]
                                    · linarith only [h2, h804, hlam]
                              · have p774_0 := h774c.1
                                have p774_1 := h774c.2.1
                                have p774_2 := h774c.2.2.1
                                have p774_3 := h774c.2.2.2
                                rcases p774_3 (m.d 0 2) (by simp) with h811 | h811
                                · linarith only [h327, h811, hlam]
                                · linarith only [h0, h811, hlam]
                              · have p774_0 := h774c.1
                                have p774_1 := h774c.2.1
                                have p774_2 := h774c.2.2.1
                                have p774_3 := h774c.2.2.2
                                linarith only [h770, hlam, p774_1]
                              · have p774_0 := h774c.1
                                have p774_1 := h774c.2.1
                                have p774_2 := h774c.2.2.1
                                have p774_3 := h774c.2.2.2
                                linarith only [hlam, p774_0]
                              · have p774_0 := h774c.1
                                have p774_1 := h774c.2.1
                                have p774_2 := h774c.2.2.1
                                have p774_3 := h774c.2.2.2
                                linarith only [h0, h2, h745, h771, hc12, hc24, hlam, hphi, p774_1]
                              · have p774_0 := h774c.1
                                have p774_1 := h774c.2.1
                                have p774_2 := h774c.2.2.1
                                have p774_3 := h774c.2.2.2
                                rcases p774_3 (m.d 0 2) (by simp) with h817 | h817
                                · linarith only [h817, hlam, p774_0]
                                · rcases p774_3 (m.d 1 2) (by simp) with h819 | h819
                                  · linarith only [h764, h819, hlam]
                                  · rcases p774_3 (m.d 2 3) (by simp) with h821 | h821
                                    · rcases p774_3 (m.d 2 4) (by simp) with h822 | h822
                                      · rcases p774_3 (m.d 2 5) (by simp) with h823 | h823
                                        · rcases h3bigk with h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c
                                          · have p824_0 := h824c.1
                                            have p824_1 := h824c.2.1
                                            have p824_2 := h824c.2.2.1
                                            have p824_3 := h824c.2.2.2
                                            linarith only [hlam, p824_0]
                                          · have p824_0 := h824c.1
                                            have p824_1 := h824c.2.1
                                            have p824_2 := h824c.2.2.1
                                            have p824_3 := h824c.2.2.2
                                            linarith only [h745, hc13, hc35, hlam, hphi, p824_1]
                                          · have p824_0 := h824c.1
                                            have p824_1 := h824c.2.1
                                            have p824_2 := h824c.2.2.1
                                            have p824_3 := h824c.2.2.2
                                            linarith only [h2, hlam, p824_1]
                                          · have p824_0 := h824c.1
                                            have p824_1 := h824c.2.1
                                            have p824_2 := h824c.2.2.1
                                            have p824_3 := h824c.2.2.2
                                            linarith only [h452, hlam, p824_0]
                                          · have p824_0 := h824c.1
                                            have p824_1 := h824c.2.1
                                            have p824_2 := h824c.2.2.1
                                            have p824_3 := h824c.2.2.2
                                            linarith only [h745, hlam, p824_0]
                                          · have p824_0 := h824c.1
                                            have p824_1 := h824c.2.1
                                            have p824_2 := h824c.2.2.1
                                            have p824_3 := h824c.2.2.2
                                            linarith only [h1, hlam, p824_0]
                                          · have p824_0 := h824c.1
                                            have p824_1 := h824c.2.1
                                            have p824_2 := h824c.2.2.1
                                            have p824_3 := h824c.2.2.2
                                            linarith only [hlam, p824_0]
                                          · have p824_0 := h824c.1
                                            have p824_1 := h824c.2.1
                                            have p824_2 := h824c.2.2.1
                                            have p824_3 := h824c.2.2.2
                                            linarith only [h760, hlam, p824_1]
                                          · have p824_0 := h824c.1
                                            have p824_1 := h824c.2.1
                                            have p824_2 := h824c.2.2.1
                                            have p824_3 := h824c.2.2.2
                                            linarith only [h766, hlam, p824_0]
                                          · have p824_0 := h824c.1
                                            have p824_1 := h824c.2.1
                                            have p824_2 := h824c.2.2.1
                                            have p824_3 := h824c.2.2.2
                                            linarith only [h768, hlam, p824_0]
                                          · have p824_0 := h824c.1
                                            have p824_1 := h824c.2.1
                                            have p824_2 := h824c.2.2.1
                                            have p824_3 := h824c.2.2.2
                                            rcases p824_3 (m.d 0 3) (by simp) with h835 | h835
                                            · linarith only [h2, h835, hlam]
                                            · rcases p824_3 (m.d 1 3) (by simp) with h837 | h837
                                              · linarith only [h760, h837, hlam]
                                              · rcases p824_3 (m.d 2 3) (by simp) with h839 | h839
                                                · rcases p824_3 (m.d 3 4) (by simp) with h840 | h840
                                                  · linarith only [h770, h840, hlam]
                                                  · linarith only [h452, h840, hlam]
                                                · linarith only [h2, h839, hlam]
                                          · have p824_0 := h824c.1
                                            have p824_1 := h824c.2.1
                                            have p824_2 := h824c.2.2.1
                                            have p824_3 := h824c.2.2.2
                                            rcases p824_3 (m.d 0 3) (by simp) with h844 | h844
                                            · linarith only [h2, h844, hlam]
                                            · linarith only [h1, h844, hlam]
                                          · have p824_0 := h824c.1
                                            have p824_1 := h824c.2.1
                                            have p824_2 := h824c.2.2.1
                                            have p824_3 := h824c.2.2.2
                                            linarith only [hlam, p824_0]
                                          · have p824_0 := h824c.1
                                            have p824_1 := h824c.2.1
                                            have p824_2 := h824c.2.2.1
                                            have p824_3 := h824c.2.2.2
                                            linarith only [h452, h759, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p824_1, u5ehi4]
                                          · have p824_0 := h824c.1
                                            have p824_1 := h824c.2.1
                                            have p824_2 := h824c.2.2.1
                                            have p824_3 := h824c.2.2.2
                                            linarith only [h1, h745, h760, hc12, hc23, hlam, hphi, p824_1]
                                          · have p824_0 := h824c.1
                                            have p824_1 := h824c.2.1
                                            have p824_2 := h824c.2.2.1
                                            have p824_3 := h824c.2.2.2
                                            linarith only [h1, h760, h770, hc12, hc23, hlam, hphi, p824_1]
                                          · have p824_0 := h824c.1
                                            have p824_1 := h824c.2.1
                                            have p824_2 := h824c.2.2.1
                                            have p824_3 := h824c.2.2.2
                                            linarith only [h760, h770, hc12, hc23, hlam, hphi, p824_1]
                                          · have p824_0 := h824c.1
                                            have p824_1 := h824c.2.1
                                            have p824_2 := h824c.2.2.1
                                            have p824_3 := h824c.2.2.2
                                            linarith only [h770, hlam, p824_0]
                                          · have p824_0 := h824c.1
                                            have p824_1 := h824c.2.1
                                            have p824_2 := h824c.2.2.1
                                            have p824_3 := h824c.2.2.2
                                            linarith only [hlam, p824_0]
                                          · have p824_0 := h824c.1
                                            have p824_1 := h824c.2.1
                                            have p824_2 := h824c.2.2.1
                                            have p824_3 := h824c.2.2.2
                                            linarith only [h1, h745, h760, h770, hc12, hc23, hlam, hphi, p824_1]
                                          · have p824_0 := h824c.1
                                            have p824_1 := h824c.2.1
                                            have p824_2 := h824c.2.2.1
                                            have p824_3 := h824c.2.2.2
                                            linarith only [h1, h760, h771, hc12, hc23, hlam, hphi, p824_1]
                                          · have p824_0 := h824c.1
                                            have p824_1 := h824c.2.1
                                            have p824_2 := h824c.2.2.1
                                            have p824_3 := h824c.2.2.2
                                            linarith only [h760, h771, hc12, hc23, hlam, hphi, p824_1]
                                          · have p824_0 := h824c.1
                                            have p824_1 := h824c.2.1
                                            have p824_2 := h824c.2.2.1
                                            have p824_3 := h824c.2.2.2
                                            linarith only [h771, hlam, p824_0]
                                          · have p824_0 := h824c.1
                                            have p824_1 := h824c.2.1
                                            have p824_2 := h824c.2.2.1
                                            have p824_3 := h824c.2.2.2
                                            linarith only [h773, hlam, p824_0]
                                          · have p824_0 := h824c.1
                                            have p824_1 := h824c.2.1
                                            have p824_2 := h824c.2.2.1
                                            have p824_3 := h824c.2.2.2
                                            linarith only [hlam, p824_0]
                                        · linarith only [h823, hlam, p774_0]
                                      · linarith only [h327, h822, hlam]
                                    · linarith only [h2, h821, hlam]
                              · have p774_0 := h774c.1
                                have p774_1 := h774c.2.1
                                have p774_2 := h774c.2.2.1
                                have p774_3 := h774c.2.2.2
                                rcases p774_3 (m.d 0 2) (by simp) with h863 | h863
                                · linarith only [h428, h863, hlam]
                                · linarith only [h0, h863, hlam]
                              · have p774_0 := h774c.1
                                have p774_1 := h774c.2.1
                                have p774_2 := h774c.2.2.1
                                have p774_3 := h774c.2.2.2
                                linarith only [h771, hlam, p774_1]
                              · have p774_0 := h774c.1
                                have p774_1 := h774c.2.1
                                have p774_2 := h774c.2.2.1
                                have p774_3 := h774c.2.2.2
                                linarith only [h772, hlam, p774_0]
                              · have p774_0 := h774c.1
                                have p774_1 := h774c.2.1
                                have p774_2 := h774c.2.2.1
                                have p774_3 := h774c.2.2.2
                                linarith only [hlam, p774_0]
                            · linarith only [h1, h452, h759, h760, h773, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                          · linarith only [h0, h327, h452, h759, h770, h772, hc12, hc23, hlam, hphi]
                        · linarith only [h452, h759, h770, h771, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h872 | h872
                        · linarith only [h1, h745, h760, h770, h872, hc12, hc34, hlam, hphi, ht23]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h874 | h874
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h875 | h875
                            · rcases h2bigk with h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c
                              · have p876_0 := h876c.1
                                have p876_1 := h876c.2.1
                                have p876_2 := h876c.2.2.1
                                have p876_3 := h876c.2.2.2
                                linarith only [hlam, p876_0]
                              · have p876_0 := h876c.1
                                have p876_1 := h876c.2.1
                                have p876_2 := h876c.2.2.1
                                have p876_3 := h876c.2.2.2
                                linarith only [h2, h872, h875, hc12, hc34, hlam, hphi, ht23, p876_1]
                              · have p876_0 := h876c.1
                                have p876_1 := h876c.2.1
                                have p876_2 := h876c.2.2.1
                                have p876_3 := h876c.2.2.2
                                linarith only [h2, hlam, p876_0]
                              · have p876_0 := h876c.1
                                have p876_1 := h876c.2.1
                                have p876_2 := h876c.2.2.1
                                have p876_3 := h876c.2.2.2
                                linarith only [h327, hlam, p876_0]
                              · have p876_0 := h876c.1
                                have p876_1 := h876c.2.1
                                have p876_2 := h876c.2.2.1
                                have p876_3 := h876c.2.2.2
                                linarith only [h428, hlam, p876_0]
                              · have p876_0 := h876c.1
                                have p876_1 := h876c.2.1
                                have p876_2 := h876c.2.2.1
                                have p876_3 := h876c.2.2.2
                                linarith only [h0, hlam, p876_0]
                              · have p876_0 := h876c.1
                                have p876_1 := h876c.2.1
                                have p876_2 := h876c.2.2.1
                                have p876_3 := h876c.2.2.2
                                linarith only [hlam, p876_0]
                              · have p876_0 := h876c.1
                                have p876_1 := h876c.2.1
                                have p876_2 := h876c.2.2.1
                                have p876_3 := h876c.2.2.2
                                linarith only [h760, hlam, p876_0]
                              · have p876_0 := h876c.1
                                have p876_1 := h876c.2.1
                                have p876_2 := h876c.2.2.1
                                have p876_3 := h876c.2.2.2
                                linarith only [h762, hlam, p876_0]
                              · have p876_0 := h876c.1
                                have p876_1 := h876c.2.1
                                have p876_2 := h876c.2.2.1
                                have p876_3 := h876c.2.2.2
                                linarith only [h764, hlam, p876_0]
                              · have p876_0 := h876c.1
                                have p876_1 := h876c.2.1
                                have p876_2 := h876c.2.2.1
                                have p876_3 := h876c.2.2.2
                                linarith only [h872, h875, hc02, hc34, hlam, hphi, ht23, p876_1]
                              · have p876_0 := h876c.1
                                have p876_1 := h876c.2.1
                                have p876_2 := h876c.2.2.1
                                have p876_3 := h876c.2.2.2
                                linarith only [h872, h875, hc12, hc34, hlam, hphi, ht23, p876_1]
                              · have p876_0 := h876c.1
                                have p876_1 := h876c.2.1
                                have p876_2 := h876c.2.2.1
                                have p876_3 := h876c.2.2.2
                                linarith only [hlam, p876_0]
                              · have p876_0 := h876c.1
                                have p876_1 := h876c.2.1
                                have p876_2 := h876c.2.2.1
                                have p876_3 := h876c.2.2.2
                                linarith only [h770, hlam, p876_0]
                              · have p876_0 := h876c.1
                                have p876_1 := h876c.2.1
                                have p876_2 := h876c.2.2.1
                                have p876_3 := h876c.2.2.2
                                linarith only [h872, hlam, p876_0]
                              · have p876_0 := h876c.1
                                have p876_1 := h876c.2.1
                                have p876_2 := h876c.2.2.1
                                have p876_3 := h876c.2.2.2
                                rcases p876_3 (m.d 0 2) (by simp) with h892 | h892
                                · linarith only [h892, hlam, p876_0]
                                · rcases p876_3 (m.d 1 2) (by simp) with h894 | h894
                                  · linarith only [h762, h894, hlam]
                                  · rcases p876_3 (m.d 2 3) (by simp) with h896 | h896
                                    · linarith only [h770, h896, hlam]
                                    · linarith only [h2, h896, hlam]
                              · have p876_0 := h876c.1
                                have p876_1 := h876c.2.1
                                have p876_2 := h876c.2.2.1
                                have p876_3 := h876c.2.2.2
                                rcases p876_3 (m.d 0 2) (by simp) with h899 | h899
                                · linarith only [h327, h899, hlam]
                                · linarith only [h0, h899, hlam]
                              · have p876_0 := h876c.1
                                have p876_1 := h876c.2.1
                                have p876_2 := h876c.2.2.1
                                have p876_3 := h876c.2.2.2
                                linarith only [h0, h2, h770, hc12, hc34, hlam, hphi, ht23, p876_1]
                              · have p876_0 := h876c.1
                                have p876_1 := h876c.2.1
                                have p876_2 := h876c.2.2.1
                                have p876_3 := h876c.2.2.2
                                linarith only [hlam, p876_0]
                              · have p876_0 := h876c.1
                                have p876_1 := h876c.2.1
                                have p876_2 := h876c.2.2.1
                                have p876_3 := h876c.2.2.2
                                linarith only [h0, h428, h770, hc12, hc34, hlam, hphi, ht23, p876_1]
                              · have p876_0 := h876c.1
                                have p876_1 := h876c.2.1
                                have p876_2 := h876c.2.2.1
                                have p876_3 := h876c.2.2.2
                                rcases p876_3 (m.d 0 2) (by simp) with h905 | h905
                                · linarith only [h905, hlam, p876_0]
                                · rcases p876_3 (m.d 1 2) (by simp) with h907 | h907
                                  · linarith only [h764, h907, hlam]
                                  · rcases p876_3 (m.d 2 3) (by simp) with h909 | h909
                                    · linarith only [h872, h909, hlam]
                                    · linarith only [h2, h909, hlam]
                              · have p876_0 := h876c.1
                                have p876_1 := h876c.2.1
                                have p876_2 := h876c.2.2.1
                                have p876_3 := h876c.2.2.2
                                rcases p876_3 (m.d 0 2) (by simp) with h912 | h912
                                · linarith only [h428, h912, hlam]
                                · linarith only [h0, h912, hlam]
                              · have p876_0 := h876c.1
                                have p876_1 := h876c.2.1
                                have p876_2 := h876c.2.2.1
                                have p876_3 := h876c.2.2.2
                                linarith only [h0, h2, hc12, hc25, hlam, hphi, p876_1]
                              · have p876_0 := h876c.1
                                have p876_1 := h876c.2.1
                                have p876_2 := h876c.2.2.1
                                have p876_3 := h876c.2.2.2
                                linarith only [h874, hlam, p876_0]
                              · have p876_0 := h876c.1
                                have p876_1 := h876c.2.1
                                have p876_2 := h876c.2.2.1
                                have p876_3 := h876c.2.2.2
                                linarith only [hlam, p876_0]
                            · linarith only [h0, h327, h759, h770, h875, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                          · linarith only [h327, h759, h874, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h920 | h920
            · linarith only [h0, h2, h920, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h922 | h922
              · linarith only [h0, h327, h922, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h924 | h924
                · linarith only [h0, h924, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h926 | h926
                  · linarith only [h1, h2, h452, h926, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h928 | h928
                    · linarith only [h1, h928, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h930 | h930
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h931 | h931
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h932 | h932
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h933 | h933
                            · linarith only [h2, h452, h759, h930, h933, hc02, hc23, hlam, hphi]
                            · linarith only [h0, h2, h452, h932, h933, hc12, hc24, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h936 | h936
                            · linarith only [h0, h327, h932, h936, hc12, hc34, hlam, hphi, ht23]
                            · rcases h2bigk with h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c
                              · have p938_0 := h938c.1
                                have p938_1 := h938c.2.1
                                have p938_2 := h938c.2.2.1
                                have p938_3 := h938c.2.2.2
                                linarith only [hlam, p938_0]
                              · have p938_0 := h938c.1
                                have p938_1 := h938c.2.1
                                have p938_2 := h938c.2.2.1
                                have p938_3 := h938c.2.2.2
                                linarith only [h2, h452, h930, hc12, hc24, hlam, hphi, p938_1]
                              · have p938_0 := h938c.1
                                have p938_1 := h938c.2.1
                                have p938_2 := h938c.2.2.1
                                have p938_3 := h938c.2.2.2
                                linarith only [h2, hlam, p938_0]
                              · have p938_0 := h938c.1
                                have p938_1 := h938c.2.1
                                have p938_2 := h938c.2.2.1
                                have p938_3 := h938c.2.2.2
                                linarith only [h327, hlam, p938_0]
                              · have p938_0 := h938c.1
                                have p938_1 := h938c.2.1
                                have p938_2 := h938c.2.2.1
                                have p938_3 := h938c.2.2.2
                                linarith only [h428, hlam, p938_0]
                              · have p938_0 := h938c.1
                                have p938_1 := h938c.2.1
                                have p938_2 := h938c.2.2.1
                                have p938_3 := h938c.2.2.2
                                linarith only [h0, hlam, p938_0]
                              · have p938_0 := h938c.1
                                have p938_1 := h938c.2.1
                                have p938_2 := h938c.2.2.1
                                have p938_3 := h938c.2.2.2
                                linarith only [hlam, p938_0]
                              · have p938_0 := h938c.1
                                have p938_1 := h938c.2.1
                                have p938_2 := h938c.2.2.1
                                have p938_3 := h938c.2.2.2
                                linarith only [h920, hlam, p938_0]
                              · have p938_0 := h938c.1
                                have p938_1 := h938c.2.1
                                have p938_2 := h938c.2.2.1
                                have p938_3 := h938c.2.2.2
                                linarith only [h922, hlam, p938_0]
                              · have p938_0 := h938c.1
                                have p938_1 := h938c.2.1
                                have p938_2 := h938c.2.2.1
                                have p938_3 := h938c.2.2.2
                                linarith only [h924, hlam, p938_0]
                              · have p938_0 := h938c.1
                                have p938_1 := h938c.2.1
                                have p938_2 := h938c.2.2.1
                                have p938_3 := h938c.2.2.2
                                rcases p938_3 (m.d 0 2) (by simp) with h949 | h949
                                · linarith only [h949, hlam, p938_0]
                                · rcases p938_3 (m.d 1 2) (by simp) with h951 | h951
                                  · linarith only [h920, h951, hlam]
                                  · rcases p938_3 (m.d 2 3) (by simp) with h953 | h953
                                    · rcases p938_3 (m.d 2 4) (by simp) with h954 | h954
                                      · linarith only [h930, h954, hlam]
                                      · linarith only [h327, h954, hlam]
                                    · linarith only [h953, hlam, p938_0]
                              · have p938_0 := h938c.1
                                have p938_1 := h938c.2.1
                                have p938_2 := h938c.2.2.1
                                have p938_3 := h938c.2.2.2
                                rcases p938_3 (m.d 0 2) (by simp) with h958 | h958
                                · linarith only [h2, h958, hlam]
                                · linarith only [h0, h958, hlam]
                              · have p938_0 := h938c.1
                                have p938_1 := h938c.2.1
                                have p938_2 := h938c.2.2.1
                                have p938_3 := h938c.2.2.2
                                linarith only [hlam, p938_0]
                              · have p938_0 := h938c.1
                                have p938_1 := h938c.2.1
                                have p938_2 := h938c.2.2.1
                                have p938_3 := h938c.2.2.2
                                linarith only [h2, h452, h930, hc02, hc23, hlam, hphi, p938_1]
                              · have p938_0 := h938c.1
                                have p938_1 := h938c.2.1
                                have p938_2 := h938c.2.2.1
                                have p938_3 := h938c.2.2.2
                                linarith only [h0, h428, hc12, hc23, hlam, hphi, p938_1]
                              · have p938_0 := h938c.1
                                have p938_1 := h938c.2.1
                                have p938_2 := h938c.2.2.1
                                have p938_3 := h938c.2.2.2
                                linarith only [h0, h932, hc12, hc45, hlam, hphi, ht23, ht34, p938_1]
                              · have p938_0 := h938c.1
                                have p938_1 := h938c.2.1
                                have p938_2 := h938c.2.2.1
                                have p938_3 := h938c.2.2.2
                                linarith only [h932, hc12, hc45, hlam, hphi, ht23, ht34, p938_1]
                              · have p938_0 := h938c.1
                                have p938_1 := h938c.2.1
                                have p938_2 := h938c.2.2.1
                                have p938_3 := h938c.2.2.2
                                linarith only [h930, hlam, p938_1]
                              · have p938_0 := h938c.1
                                have p938_1 := h938c.2.1
                                have p938_2 := h938c.2.2.1
                                have p938_3 := h938c.2.2.2
                                linarith only [hlam, p938_0]
                              · have p938_0 := h938c.1
                                have p938_1 := h938c.2.1
                                have p938_2 := h938c.2.2.1
                                have p938_3 := h938c.2.2.2
                                linarith only [h932, hlam, p938_1]
                              · have p938_0 := h938c.1
                                have p938_1 := h938c.2.1
                                have p938_2 := h938c.2.2.1
                                have p938_3 := h938c.2.2.2
                                rcases p938_3 (m.d 0 2) (by simp) with h969 | h969
                                · linarith only [h969, hlam, p938_0]
                                · rcases p938_3 (m.d 1 2) (by simp) with h971 | h971
                                  · linarith only [h924, h971, hlam]
                                  · rcases p938_3 (m.d 2 3) (by simp) with h973 | h973
                                    · rcases p938_3 (m.d 2 4) (by simp) with h974 | h974
                                      · linarith only [h932, h974, hlam]
                                      · linarith only [h327, h974, hlam]
                                    · linarith only [h2, h973, hlam]
                              · have p938_0 := h938c.1
                                have p938_1 := h938c.2.1
                                have p938_2 := h938c.2.2.1
                                have p938_3 := h938c.2.2.2
                                rcases p938_3 (m.d 0 2) (by simp) with h978 | h978
                                · linarith only [h428, h978, hlam]
                                · linarith only [h0, h978, hlam]
                              · have p938_0 := h938c.1
                                have p938_1 := h938c.2.1
                                have p938_2 := h938c.2.2.1
                                have p938_3 := h938c.2.2.2
                                linarith only [h931, hlam, p938_1]
                              · have p938_0 := h938c.1
                                have p938_1 := h938c.2.1
                                have p938_2 := h938c.2.2.1
                                have p938_3 := h938c.2.2.2
                                linarith only [h0, h327, hc12, hc25, hlam, hphi, p938_1]
                              · have p938_0 := h938c.1
                                have p938_1 := h938c.2.1
                                have p938_2 := h938c.2.2.1
                                have p938_3 := h938c.2.2.2
                                linarith only [hlam, p938_0]
                        · linarith only [h0, h2, h452, h930, h931, hc12, hc35, hlam, hphi, ht23]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h985 | h985
                        · linarith only [h0, h2, h745, h930, h985, hc12, hc34, hlam, hphi, ht23]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h987 | h987
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h988 | h988
                            · rcases h2bigk with h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c
                              · have p989_0 := h989c.1
                                have p989_1 := h989c.2.1
                                have p989_2 := h989c.2.2.1
                                have p989_3 := h989c.2.2.2
                                linarith only [hlam, p989_0]
                              · have p989_0 := h989c.1
                                have p989_1 := h989c.2.1
                                have p989_2 := h989c.2.2.1
                                have p989_3 := h989c.2.2.2
                                linarith only [h2, h985, h988, hc12, hc34, hlam, hphi, ht23, p989_1]
                              · have p989_0 := h989c.1
                                have p989_1 := h989c.2.1
                                have p989_2 := h989c.2.2.1
                                have p989_3 := h989c.2.2.2
                                linarith only [h2, hlam, p989_0]
                              · have p989_0 := h989c.1
                                have p989_1 := h989c.2.1
                                have p989_2 := h989c.2.2.1
                                have p989_3 := h989c.2.2.2
                                linarith only [h327, hlam, p989_0]
                              · have p989_0 := h989c.1
                                have p989_1 := h989c.2.1
                                have p989_2 := h989c.2.2.1
                                have p989_3 := h989c.2.2.2
                                linarith only [h428, hlam, p989_0]
                              · have p989_0 := h989c.1
                                have p989_1 := h989c.2.1
                                have p989_2 := h989c.2.2.1
                                have p989_3 := h989c.2.2.2
                                linarith only [h0, hlam, p989_0]
                              · have p989_0 := h989c.1
                                have p989_1 := h989c.2.1
                                have p989_2 := h989c.2.2.1
                                have p989_3 := h989c.2.2.2
                                linarith only [hlam, p989_0]
                              · have p989_0 := h989c.1
                                have p989_1 := h989c.2.1
                                have p989_2 := h989c.2.2.1
                                have p989_3 := h989c.2.2.2
                                linarith only [h920, hlam, p989_0]
                              · have p989_0 := h989c.1
                                have p989_1 := h989c.2.1
                                have p989_2 := h989c.2.2.1
                                have p989_3 := h989c.2.2.2
                                linarith only [h922, hlam, p989_0]
                              · have p989_0 := h989c.1
                                have p989_1 := h989c.2.1
                                have p989_2 := h989c.2.2.1
                                have p989_3 := h989c.2.2.2
                                linarith only [h924, hlam, p989_0]
                              · have p989_0 := h989c.1
                                have p989_1 := h989c.2.1
                                have p989_2 := h989c.2.2.1
                                have p989_3 := h989c.2.2.2
                                linarith only [h985, h988, hc02, hc34, hlam, hphi, ht23, p989_1]
                              · have p989_0 := h989c.1
                                have p989_1 := h989c.2.1
                                have p989_2 := h989c.2.2.1
                                have p989_3 := h989c.2.2.2
                                linarith only [h985, h988, hc12, hc34, hlam, hphi, ht23, p989_1]
                              · have p989_0 := h989c.1
                                have p989_1 := h989c.2.1
                                have p989_2 := h989c.2.2.1
                                have p989_3 := h989c.2.2.2
                                linarith only [hlam, p989_0]
                              · have p989_0 := h989c.1
                                have p989_1 := h989c.2.1
                                have p989_2 := h989c.2.2.1
                                have p989_3 := h989c.2.2.2
                                linarith only [h930, hlam, p989_0]
                              · have p989_0 := h989c.1
                                have p989_1 := h989c.2.1
                                have p989_2 := h989c.2.2.1
                                have p989_3 := h989c.2.2.2
                                linarith only [h985, hlam, p989_0]
                              · have p989_0 := h989c.1
                                have p989_1 := h989c.2.1
                                have p989_2 := h989c.2.2.1
                                have p989_3 := h989c.2.2.2
                                rcases p989_3 (m.d 0 2) (by simp) with h1005 | h1005
                                · linarith only [h1005, hlam, p989_0]
                                · rcases p989_3 (m.d 1 2) (by simp) with h1007 | h1007
                                  · linarith only [h1007, h922, hlam]
                                  · rcases p989_3 (m.d 2 3) (by simp) with h1009 | h1009
                                    · linarith only [h1009, h930, hlam]
                                    · linarith only [h1009, h2, hlam]
                              · have p989_0 := h989c.1
                                have p989_1 := h989c.2.1
                                have p989_2 := h989c.2.2.1
                                have p989_3 := h989c.2.2.2
                                rcases p989_3 (m.d 0 2) (by simp) with h1012 | h1012
                                · linarith only [h1012, h327, hlam]
                                · linarith only [h0, h1012, hlam]
                              · have p989_0 := h989c.1
                                have p989_1 := h989c.2.1
                                have p989_2 := h989c.2.2.1
                                have p989_3 := h989c.2.2.2
                                linarith only [h0, h2, h930, hc12, hc34, hlam, hphi, ht23, p989_1]
                              · have p989_0 := h989c.1
                                have p989_1 := h989c.2.1
                                have p989_2 := h989c.2.2.1
                                have p989_3 := h989c.2.2.2
                                linarith only [hlam, p989_0]
                              · have p989_0 := h989c.1
                                have p989_1 := h989c.2.1
                                have p989_2 := h989c.2.2.1
                                have p989_3 := h989c.2.2.2
                                linarith only [h0, h428, h930, hc12, hc34, hlam, hphi, ht23, p989_1]
                              · have p989_0 := h989c.1
                                have p989_1 := h989c.2.1
                                have p989_2 := h989c.2.2.1
                                have p989_3 := h989c.2.2.2
                                rcases p989_3 (m.d 0 2) (by simp) with h1018 | h1018
                                · linarith only [h1018, hlam, p989_0]
                                · rcases p989_3 (m.d 1 2) (by simp) with h1020 | h1020
                                  · linarith only [h1020, h924, hlam]
                                  · rcases p989_3 (m.d 2 3) (by simp) with h1022 | h1022
                                    · linarith only [h1022, h985, hlam]
                                    · linarith only [h1022, h2, hlam]
                              · have p989_0 := h989c.1
                                have p989_1 := h989c.2.1
                                have p989_2 := h989c.2.2.1
                                have p989_3 := h989c.2.2.2
                                rcases p989_3 (m.d 0 2) (by simp) with h1025 | h1025
                                · linarith only [h1025, h428, hlam]
                                · linarith only [h0, h1025, hlam]
                              · have p989_0 := h989c.1
                                have p989_1 := h989c.2.1
                                have p989_2 := h989c.2.2.1
                                have p989_3 := h989c.2.2.2
                                linarith only [h0, h2, hc12, hc25, hlam, hphi, p989_1]
                              · have p989_0 := h989c.1
                                have p989_1 := h989c.2.1
                                have p989_2 := h989c.2.2.1
                                have p989_3 := h989c.2.2.2
                                linarith only [h987, hlam, p989_0]
                              · have p989_0 := h989c.1
                                have p989_1 := h989c.2.1
                                have p989_2 := h989c.2.2.1
                                have p989_3 := h989c.2.2.2
                                linarith only [hlam, p989_0]
                            · linarith only [h930, h987, h988, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1032 | h1032
                            · linarith only [h0, h1032, h327, h987, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h0, h1032, h2, h930, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 7634000 in
theorem r1l7_10_12_13_25_L_0_L_I_L_I_M_IR_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
  · exact r1l7_10_12_13_25_L_0_L_I_L_I_M_IR_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h1 h2
  · exact r1l7_10_12_13_25_L_0_L_I_L_I_M_IR_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h1 h2

end R2N4
