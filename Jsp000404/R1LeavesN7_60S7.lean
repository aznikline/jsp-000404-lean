import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_60S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3472000 in
set_option maxHeartbeats 3472000 in
theorem r1l7_20_12_13_15_H_L_L_I_L_0_L_I_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h394 | h394
  · rcases m.htr 0 1 4 (by decide) (by decide) with h395 | h395
    · rcases m.htr 0 1 5 (by decide) (by decide) with h396 | h396
      · rcases m.htr 0 2 3 (by decide) (by decide) with h397 | h397
        · rcases m.htr 0 2 4 (by decide) (by decide) with h398 | h398
          · rcases m.htr 0 2 5 (by decide) (by decide) with h399 | h399
            · rcases m.htr 0 3 4 (by decide) (by decide) with h400 | h400
              · rcases m.htr 0 3 5 (by decide) (by decide) with h401 | h401
                · rcases m.htr 0 4 5 (by decide) (by decide) with h402 | h402
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h403 | h403
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h404 | h404
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h405 | h405
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h406 | h406
                          · linarith only [h394, h406, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h400, h406, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h399, h405, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h394, h398, h403, h404, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h403, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h412 | h412
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h413 | h413
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h414 | h414
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h415 | h415
                          · linarith only [h394, h415, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h400, h415, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h399, h414, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h394, h398, h412, h413, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h412, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h421 | h421
                  · linarith only [h400, h401, h421, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h423 | h423
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h424 | h424
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h425 | h425
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h426 | h426
                          · linarith only [h394, h426, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h400, h426, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h399, h425, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h396, h398, h400, h401, h424, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h0, h396, h400, h401, h423, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h432 | h432
                · rcases m.htr 0 4 5 (by decide) (by decide) with h433 | h433
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h434 | h434
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h435 | h435
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h436 | h436
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h437 | h437
                          · linarith only [h394, h400, h432, h437, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h439 | h439
                            · linarith only [h0, h395, h437, h439, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                            · linarith only [h432, h439, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h394, h399, h434, h436, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h394, h398, h434, h435, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h434, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h400, h432, h433, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h446 | h446
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h447 | h447
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h448 | h448
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h449 | h449
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h450 | h450
                          · linarith only [h394, h450, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h452 | h452
                            · linarith only [h0, h395, h432, h450, h452, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h454 | h454
                              · linarith only [h0, h395, h454, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                              · linarith only [h0, h395, h446, h454, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h0, h399, h449, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h394, h398, h447, h448, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h447, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h460 | h460
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h461 | h461
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h462 | h462
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h463 | h463
                          · linarith only [h394, h400, h463, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h465 | h465
                            · linarith only [h394, h432, h465, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h467 | h467
                              · linarith only [h395, h446, h467, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h469 | h469
                                · linarith only [h394, h400, h460, h469, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h471 | h471
                                  · linarith only [h0, h396, h432, h460, h463, h467, h471, hc05, hlam, hphi, ht0b, ht5b, u0elo1]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h473 | h473
                                    · linarith only [h395, h446, h461, h473, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h475 | h475
                                      · linarith only [h395, h446, h460, h463, h475, hc23, hlam, hphi, u3elo3]
                                      · rcases h2bigk with h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c
                                        · have p477_0 := h477c.1
                                          have p477_1 := h477c.2.1
                                          have p477_2 := h477c.2.2.1
                                          have p477_3 := h477c.2.2.2
                                          linarith only [hlam, p477_0]
                                        · have p477_0 := h477c.1
                                          have p477_1 := h477c.2.1
                                          have p477_2 := h477c.2.2.1
                                          have p477_3 := h477c.2.2.2
                                          linarith only [h0, hlam, p477_1]
                                        · have p477_0 := h477c.1
                                          have p477_1 := h477c.2.1
                                          have p477_2 := h477c.2.2.1
                                          have p477_3 := h477c.2.2.2
                                          linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p477_1, u0elo1]
                                        · have p477_0 := h477c.1
                                          have p477_1 := h477c.2.1
                                          have p477_2 := h477c.2.2.1
                                          have p477_3 := h477c.2.2.2
                                          linarith only [h469, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p477_1, u0elo1]
                                        · have p477_0 := h477c.1
                                          have p477_1 := h477c.2.1
                                          have p477_2 := h477c.2.2.1
                                          have p477_3 := h477c.2.2.2
                                          linarith only [h469, h473, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p477_1, u0elo1]
                                        · have p477_0 := h477c.1
                                          have p477_1 := h477c.2.1
                                          have p477_2 := h477c.2.2.1
                                          have p477_3 := h477c.2.2.2
                                          rcases p477_3 (m.d 0 2) (by simp) with h483 | h483
                                          · linarith only [h0, h483, hlam]
                                          · rcases p477_3 (m.d 1 2) (by simp) with h485 | h485
                                            · rcases p477_3 (m.d 2 3) (by simp) with h486 | h486
                                              · linarith only [h460, h486, hlam]
                                              · rcases p477_3 (m.d 2 4) (by simp) with h488 | h488
                                                · linarith only [h461, h488, hlam]
                                                · rcases p477_3 (m.d 2 5) (by simp) with h490 | h490
                                                  · linarith only [h462, h490, hlam]
                                                  · rcases h2emin with h492 | h492 | h492 | h492 | h492
                                                    · linarith only [h492, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p477_1]
                                                    · rcases h5bigk with h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c
                                                      · have p494_0 := h494c.1
                                                        have p494_1 := h494c.2.1
                                                        have p494_2 := h494c.2.2.1
                                                        have p494_3 := h494c.2.2.2
                                                        linarith only [hlam, p494_0]
                                                      · have p494_0 := h494c.1
                                                        have p494_1 := h494c.2.1
                                                        have p494_2 := h494c.2.2.1
                                                        have p494_3 := h494c.2.2.2
                                                        linarith only [h460, h463, h467, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p494_1, u0elo4]
                                                      · have p494_0 := h494c.1
                                                        have p494_1 := h494c.2.1
                                                        have p494_2 := h494c.2.2.1
                                                        have p494_3 := h494c.2.2.2
                                                        linarith only [h0, h396, h469, h473, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p477_1, p494_1]
                                                      · have p494_0 := h494c.1
                                                        have p494_1 := h494c.2.1
                                                        have p494_2 := h494c.2.2.1
                                                        have p494_3 := h494c.2.2.2
                                                        linarith only [h432, hlam, p494_1]
                                                      · have p494_0 := h494c.1
                                                        have p494_1 := h494c.2.1
                                                        have p494_2 := h494c.2.2.1
                                                        have p494_3 := h494c.2.2.2
                                                        linarith only [h446, hlam, p494_1]
                                                      · have p494_0 := h494c.1
                                                        have p494_1 := h494c.2.1
                                                        have p494_2 := h494c.2.2.1
                                                        have p494_3 := h494c.2.2.2
                                                        linarith only [h396, hlam, p494_0]
                                                      · have p494_0 := h494c.1
                                                        have p494_1 := h494c.2.1
                                                        have p494_2 := h494c.2.2.1
                                                        have p494_3 := h494c.2.2.2
                                                        linarith only [hlam, p494_0]
                                                      · have p494_0 := h494c.1
                                                        have p494_1 := h494c.2.1
                                                        have p494_2 := h494c.2.2.1
                                                        have p494_3 := h494c.2.2.2
                                                        linarith only [h0, h396, h469, h473, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p477_1, p494_1]
                                                      · have p494_0 := h494c.1
                                                        have p494_1 := h494c.2.1
                                                        have p494_2 := h494c.2.2.1
                                                        have p494_3 := h494c.2.2.2
                                                        linarith only [h465, hlam, p494_1]
                                                      · have p494_0 := h494c.1
                                                        have p494_1 := h494c.2.1
                                                        have p494_2 := h494c.2.2.1
                                                        have p494_3 := h494c.2.2.2
                                                        linarith only [h467, hlam, p494_1]
                                                      · have p494_0 := h494c.1
                                                        have p494_1 := h494c.2.1
                                                        have p494_2 := h494c.2.2.1
                                                        have p494_3 := h494c.2.2.2
                                                        linarith only [h399, hlam, p494_1]
                                                      · have p494_0 := h494c.1
                                                        have p494_1 := h494c.2.1
                                                        have p494_2 := h494c.2.2.1
                                                        have p494_3 := h494c.2.2.2
                                                        linarith only [h462, hlam, p494_1]
                                                      · have p494_0 := h494c.1
                                                        have p494_1 := h494c.2.1
                                                        have p494_2 := h494c.2.2.1
                                                        have p494_3 := h494c.2.2.2
                                                        linarith only [hlam, p494_0]
                                                      · have p494_0 := h494c.1
                                                        have p494_1 := h494c.2.1
                                                        have p494_2 := h494c.2.2.1
                                                        have p494_3 := h494c.2.2.2
                                                        linarith only [h471, hlam, p494_1]
                                                      · have p494_0 := h494c.1
                                                        have p494_1 := h494c.2.1
                                                        have p494_2 := h494c.2.2.1
                                                        have p494_3 := h494c.2.2.2
                                                        linarith only [h473, hlam, p494_1]
                                                      · have p494_0 := h494c.1
                                                        have p494_1 := h494c.2.1
                                                        have p494_2 := h494c.2.2.1
                                                        have p494_3 := h494c.2.2.2
                                                        linarith only [h399, h469, h473, hc23, hlam, hphi, p494_1, u3elo4]
                                                      · have p494_0 := h494c.1
                                                        have p494_1 := h494c.2.1
                                                        have p494_2 := h494c.2.2.1
                                                        have p494_3 := h494c.2.2.2
                                                        linarith only [h462, h469, h473, hc23, hlam, hphi, p494_1, u3elo4]
                                                      · have p494_0 := h494c.1
                                                        have p494_1 := h494c.2.1
                                                        have p494_2 := h494c.2.2.1
                                                        have p494_3 := h494c.2.2.2
                                                        linarith only [h469, h473, hc23, hlam, hphi, p494_1, u3elo4]
                                                      · have p494_0 := h494c.1
                                                        have p494_1 := h494c.2.1
                                                        have p494_2 := h494c.2.2.1
                                                        have p494_3 := h494c.2.2.2
                                                        linarith only [hlam, p494_0]
                                                      · have p494_0 := h494c.1
                                                        have p494_1 := h494c.2.1
                                                        have p494_2 := h494c.2.2.1
                                                        have p494_3 := h494c.2.2.2
                                                        linarith only [h475, hlam, p494_1]
                                                      · have p494_0 := h494c.1
                                                        have p494_1 := h494c.2.1
                                                        have p494_2 := h494c.2.2.1
                                                        have p494_3 := h494c.2.2.2
                                                        rcases p494_3 (m.d 0 5) (by simp) with h515 | h515
                                                        · linarith only [h446, h515, hlam]
                                                        · rcases p494_3 (m.d 1 5) (by simp) with h517 | h517
                                                          · linarith only [h467, h517, hlam]
                                                          · rcases p494_3 (m.d 2 5) (by simp) with h519 | h519
                                                            · linarith only [h473, h519, hlam]
                                                            · rcases p494_3 (m.d 3 5) (by simp) with h521 | h521
                                                              · linarith only [h475, h521, hlam]
                                                              · linarith only [h432, h521, hlam]
                                                      · have p494_0 := h494c.1
                                                        have p494_1 := h494c.2.1
                                                        have p494_2 := h494c.2.2.1
                                                        have p494_3 := h494c.2.2.2
                                                        rcases p494_3 (m.d 0 5) (by simp) with h524 | h524
                                                        · linarith only [h446, h524, hlam]
                                                        · linarith only [h396, h524, hlam]
                                                      · have p494_0 := h494c.1
                                                        have p494_1 := h494c.2.1
                                                        have p494_2 := h494c.2.2.1
                                                        have p494_3 := h494c.2.2.2
                                                        rcases p494_3 (m.d 0 5) (by simp) with h527 | h527
                                                        · linarith only [h446, h527, hlam]
                                                        · linarith only [h399, h527, hlam]
                                                      · have p494_0 := h494c.1
                                                        have p494_1 := h494c.2.1
                                                        have p494_2 := h494c.2.2.1
                                                        have p494_3 := h494c.2.2.2
                                                        linarith only [h394, h432, h460, hc23, hc45, hlam, hphi, ht34, p494_1]
                                                      · have p494_0 := h494c.1
                                                        have p494_1 := h494c.2.1
                                                        have p494_2 := h494c.2.2.1
                                                        have p494_3 := h494c.2.2.2
                                                        linarith only [hlam, p494_0]
                                                    · linarith only [h394, h460, h492, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                                                    · linarith only [h0, h396, h462, h473, h492, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p477_1]
                                                    · linarith only [h0, h396, h462, h492, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p477_1]
                                            · linarith only [h0, h485, hlam]
                                        · have p477_0 := h477c.1
                                          have p477_1 := h477c.2.1
                                          have p477_2 := h477c.2.2.1
                                          have p477_3 := h477c.2.2.2
                                          linarith only [hlam, p477_0]
                                        · have p477_0 := h477c.1
                                          have p477_1 := h477c.2.1
                                          have p477_2 := h477c.2.2.1
                                          have p477_3 := h477c.2.2.2
                                          rcases p477_3 (m.d 0 2) (by simp) with h537 | h537
                                          · linarith only [h0, h537, hlam]
                                          · linarith only [h397, h537, hlam]
                                        · have p477_0 := h477c.1
                                          have p477_1 := h477c.2.1
                                          have p477_2 := h477c.2.2.1
                                          have p477_3 := h477c.2.2.2
                                          rcases p477_3 (m.d 0 2) (by simp) with h540 | h540
                                          · linarith only [h0, h540, hlam]
                                          · linarith only [h398, h540, hlam]
                                        · have p477_0 := h477c.1
                                          have p477_1 := h477c.2.1
                                          have p477_2 := h477c.2.2.1
                                          have p477_3 := h477c.2.2.2
                                          rcases p477_3 (m.d 0 2) (by simp) with h543 | h543
                                          · linarith only [h0, h543, hlam]
                                          · linarith only [h399, h543, hlam]
                                        · have p477_0 := h477c.1
                                          have p477_1 := h477c.2.1
                                          have p477_2 := h477c.2.2.1
                                          have p477_3 := h477c.2.2.2
                                          linarith only [h397, hlam, p477_0]
                                        · have p477_0 := h477c.1
                                          have p477_1 := h477c.2.1
                                          have p477_2 := h477c.2.2.1
                                          have p477_3 := h477c.2.2.2
                                          linarith only [h460, hlam, p477_0]
                                        · have p477_0 := h477c.1
                                          have p477_1 := h477c.2.1
                                          have p477_2 := h477c.2.2.1
                                          have p477_3 := h477c.2.2.2
                                          linarith only [hlam, p477_0]
                                        · have p477_0 := h477c.1
                                          have p477_1 := h477c.2.1
                                          have p477_2 := h477c.2.2.1
                                          have p477_3 := h477c.2.2.2
                                          linarith only [h469, hlam, p477_0]
                                        · have p477_0 := h477c.1
                                          have p477_1 := h477c.2.1
                                          have p477_2 := h477c.2.2.1
                                          have p477_3 := h477c.2.2.2
                                          linarith only [h471, hlam, p477_0]
                                        · have p477_0 := h477c.1
                                          have p477_1 := h477c.2.1
                                          have p477_2 := h477c.2.2.1
                                          have p477_3 := h477c.2.2.2
                                          linarith only [h398, hlam, p477_0]
                                        · have p477_0 := h477c.1
                                          have p477_1 := h477c.2.1
                                          have p477_2 := h477c.2.2.1
                                          have p477_3 := h477c.2.2.2
                                          linarith only [h461, hlam, p477_0]
                                        · have p477_0 := h477c.1
                                          have p477_1 := h477c.2.1
                                          have p477_2 := h477c.2.2.1
                                          have p477_3 := h477c.2.2.2
                                          linarith only [h0, h396, h462, h473, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p477_1, u0elo1]
                                        · have p477_0 := h477c.1
                                          have p477_1 := h477c.2.1
                                          have p477_2 := h477c.2.2.1
                                          have p477_3 := h477c.2.2.2
                                          linarith only [hlam, p477_0]
                                        · have p477_0 := h477c.1
                                          have p477_1 := h477c.2.1
                                          have p477_2 := h477c.2.2.1
                                          have p477_3 := h477c.2.2.2
                                          linarith only [h473, hlam, p477_1]
                                        · have p477_0 := h477c.1
                                          have p477_1 := h477c.2.1
                                          have p477_2 := h477c.2.2.1
                                          have p477_3 := h477c.2.2.2
                                          linarith only [h399, hlam, p477_0]
                                        · have p477_0 := h477c.1
                                          have p477_1 := h477c.2.1
                                          have p477_2 := h477c.2.2.1
                                          have p477_3 := h477c.2.2.2
                                          linarith only [h462, hlam, p477_0]
                                        · have p477_0 := h477c.1
                                          have p477_1 := h477c.2.1
                                          have p477_2 := h477c.2.2.1
                                          have p477_3 := h477c.2.2.2
                                          linarith only [h0, h396, h462, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p477_1, u0elo1]
                                        · have p477_0 := h477c.1
                                          have p477_1 := h477c.2.1
                                          have p477_2 := h477c.2.2.1
                                          have p477_3 := h477c.2.2.2
                                          linarith only [h0, h396, h462, hc24, hlam, hphi, ht0b, ht45, ht5b, p477_1, u0elo1]
                                        · have p477_0 := h477c.1
                                          have p477_1 := h477c.2.1
                                          have p477_2 := h477c.2.2.1
                                          have p477_3 := h477c.2.2.2
                                          linarith only [hlam, p477_0]
                        · linarith only [h0, h399, h462, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h394, h398, h460, h461, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h394, h460, hc13, hlam, hphi, u3elo2]
            · linarith only [h0, h396, h399, hlam]
          · linarith only [h0, h395, h398, hlam]
        · linarith only [h0, h394, h397, hc13, hlam, hphi, u3elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h567 | h567
        · rcases m.htr 0 2 4 (by decide) (by decide) with h568 | h568
          · rcases m.htr 0 2 5 (by decide) (by decide) with h569 | h569
            · rcases m.htr 0 3 4 (by decide) (by decide) with h570 | h570
              · rcases m.htr 0 3 5 (by decide) (by decide) with h571 | h571
                · linarith only [h394, h396, h571, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h573 | h573
                  · linarith only [h394, h396, h570, h573, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h575 | h575
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h576 | h576
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h577 | h577
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h578 | h578
                          · linarith only [h394, h578, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h570, h571, h575, h578, hc23, hlam, hphi, u3elo4]
                        · linarith only [h569, h577, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h394, h568, h575, h576, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h575, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h584 | h584
                · linarith only [h395, h396, h570, h584, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h586 | h586
                  · linarith only [h395, h396, h586, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h588 | h588
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h589 | h589
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h590 | h590
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h591 | h591
                          · linarith only [h394, h570, h591, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h593 | h593
                            · linarith only [h394, h395, h396, h584, h593, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · linarith only [h395, h396, h588, h591, h593, hc23, hlam, hphi, u3elo4]
                        · linarith only [h569, h590, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h568, h589, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h394, h588, hc13, hlam, hphi, u3elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h599 | h599
              · rcases m.htr 0 3 5 (by decide) (by decide) with h600 | h600
                · linarith only [h0, h394, h569, h600, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h602 | h602
                  · linarith only [h0, h394, h569, h599, h602, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h604 | h604
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h605 | h605
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h606 | h606
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h607 | h607
                          · linarith only [h0, h394, h569, h607, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                          · linarith only [h599, h600, h604, h607, hc23, hlam, hphi, u3elo4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h610 | h610
                          · linarith only [h0, h394, h569, h610, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                          · linarith only [h599, h600, h604, h610, hc23, hlam, hphi, u3elo4]
                      · linarith only [h568, h569, h605, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                    · linarith only [h0, h567, h569, h604, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h615 | h615
                · linarith only [h567, h569, h599, h615, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h617 | h617
                  · linarith only [h0, h395, h569, h617, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h619 | h619
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h620 | h620
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h621 | h621
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h622 | h622
                          · linarith only [h599, h622, hc03, hlam, hphi, u3elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h624 | h624
                            · linarith only [h0, h395, h569, h615, h622, h624, hlam]
                            · linarith only [h395, h396, h619, h622, h624, hc23, hlam, hphi, u3elo4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h627 | h627
                          · linarith only [h394, h599, h627, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h629 | h629
                            · linarith only [h0, h394, h569, h629, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                            · linarith only [h0, h395, h619, h621, h627, h629, hc23, hlam, hphi, u3elo4]
                      · linarith only [h0, h568, h569, h620, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                    · linarith only [h0, h394, h619, hc13, hlam, hphi, u3elo2]
          · linarith only [h0, h395, h568, hlam]
        · linarith only [h0, h394, h567, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h636 | h636
      · rcases m.htr 0 2 3 (by decide) (by decide) with h637 | h637
        · rcases m.htr 0 2 4 (by decide) (by decide) with h638 | h638
          · rcases m.htr 0 2 5 (by decide) (by decide) with h639 | h639
            · rcases m.htr 0 3 4 (by decide) (by decide) with h640 | h640
              · linarith only [h394, h395, h640, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h642 | h642
                · rcases m.htr 0 4 5 (by decide) (by decide) with h643 | h643
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h644 | h644
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h645 | h645
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h646 | h646
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h647 | h647
                          · linarith only [h394, h640, h647, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h394, h395, h647, hc13, hlam, hphi, u3elo3]
                        · linarith only [h394, h395, h639, h644, h645, h646, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h638, h645, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h644, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h394, h395, h642, h643, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h654 | h654
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h655 | h655
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h656 | h656
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h657 | h657
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h658 | h658
                          · linarith only [h394, h658, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h394, h395, h658, hc13, hlam, hphi, u3elo3]
                        · linarith only [h394, h395, h639, h655, h656, h657, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h638, h656, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h655, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h395, h636, h654, hlam]
            · linarith only [h395, h636, h638, h639, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h666 | h666
            · rcases m.htr 0 3 4 (by decide) (by decide) with h667 | h667
              · linarith only [h0, h394, h638, h667, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h669 | h669
                · rcases m.htr 0 4 5 (by decide) (by decide) with h670 | h670
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h671 | h671
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h672 | h672
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h673 | h673
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h674 | h674
                          · linarith only [h0, h394, h638, h667, h674, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                          · linarith only [h0, h394, h638, h672, h674, hc13, hlam, hphi, u3elo3]
                        · linarith only [h0, h394, h638, h671, h672, h673, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h678 | h678
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h679 | h679
                          · linarith only [h394, h667, h679, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h0, h394, h672, h679, hc13, hlam, hphi, u3elo3]
                        · linarith only [h0, h394, h638, h666, h671, h678, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h0, h394, h671, hc13, hlam, hphi, u3elo2]
                  · linarith only [h0, h394, h638, h669, h670, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h685 | h685
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h686 | h686
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h687 | h687
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h688 | h688
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h689 | h689
                          · linarith only [h667, h689, hc03, hlam, hphi, u3elo1]
                          · linarith only [h0, h394, h638, h686, h687, h689, hc23, hlam, hphi, u3elo3]
                        · linarith only [h0, h394, h638, h686, h687, h688, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h693 | h693
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h694 | h694
                          · linarith only [h394, h694, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h0, h394, h687, h694, hc13, hlam, hphi, u3elo3]
                        · linarith only [h0, h394, h638, h666, h686, h693, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h0, h394, h686, hc13, hlam, hphi, u3elo2]
                  · linarith only [h0, h636, h638, h685, hlam]
            · linarith only [h0, h636, h666, hlam]
        · linarith only [h0, h394, h637, hc13, hlam, hphi, u3elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h702 | h702
        · rcases m.htr 0 2 4 (by decide) (by decide) with h703 | h703
          · rcases m.htr 0 2 5 (by decide) (by decide) with h704 | h704
            · rcases m.htr 0 3 4 (by decide) (by decide) with h705 | h705
              · linarith only [h394, h395, h705, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h707 | h707
                · linarith only [h394, h636, h707, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h709 | h709
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h710 | h710
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h711 | h711
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h712 | h712
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h713 | h713
                          · linarith only [h394, h705, h713, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h394, h395, h710, h713, hc23, hlam, hphi, u3elo3]
                        · linarith only [h394, h395, h704, h710, h711, h712, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h703, h711, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h710, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h719 | h719
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h720 | h720
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h721 | h721
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h722 | h722
                          · linarith only [h394, h722, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h394, h395, h722, hc13, hlam, hphi, u3elo3]
                        · linarith only [h394, h395, h704, h719, h720, h721, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h703, h720, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h394, h719, hc13, hlam, hphi, u3elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h728 | h728
              · linarith only [h394, h395, h728, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h730 | h730
                · linarith only [h702, h704, h728, h730, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h732 | h732
                  · linarith only [h703, h704, h732, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h734 | h734
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h735 | h735
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h736 | h736
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h737 | h737
                          · linarith only [h394, h728, h737, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h394, h395, h734, h737, hc23, hlam, hphi, u3elo3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h740 | h740
                          · linarith only [h394, h740, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h394, h395, h740, hc13, hlam, hphi, u3elo3]
                      · linarith only [h703, h704, h735, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                    · linarith only [h0, h734, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h745 | h745
            · rcases m.htr 0 3 4 (by decide) (by decide) with h746 | h746
              · linarith only [h394, h636, h703, h745, h746, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h748 | h748
                · linarith only [h394, h636, h746, h748, hc13, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h750 | h750
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h751 | h751
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h752 | h752
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h753 | h753
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h754 | h754
                          · linarith only [h394, h636, h703, h745, h746, h752, h754, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h394, h636, h703, h745, h751, h752, h754, hc23, hlam, hphi, u3elo3]
                        · linarith only [h703, h745, h752, h753, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h758 | h758
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h759 | h759
                          · linarith only [h394, h759, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h394, h636, h751, h752, h758, h759, hc23, hlam, hphi, u3elo3]
                        · linarith only [h745, h758, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h751, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h703, h745, h750, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h765 | h765
              · linarith only [h0, h394, h703, h765, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h767 | h767
                · linarith only [h702, h745, h765, h767, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h769 | h769
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h770 | h770
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h771 | h771
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h772 | h772
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h773 | h773
                          · linarith only [h394, h765, h773, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h0, h394, h703, h770, h771, h773, hc23, hlam, hphi, u3elo3]
                        · linarith only [h0, h394, h703, h770, h771, h772, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h777 | h777
                        · linarith only [h0, h394, h745, h770, h771, h777, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h779 | h779
                          · linarith only [h394, h779, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h0, h394, h771, h779, hc13, hlam, hphi, u3elo3]
                    · linarith only [h0, h394, h770, hc13, hlam, hphi, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h783 | h783
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h784 | h784
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h785 | h785
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h786 | h786
                          · linarith only [h0, h394, h703, h784, h786, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h0, h394, h703, h783, h784, h786, hc23, hlam, hphi, u3elo3]
                        · linarith only [h0, h394, h703, h783, h784, h785, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h790 | h790
                        · linarith only [h0, h394, h745, h783, h784, h790, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h792 | h792
                          · linarith only [h394, h792, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h0, h394, h784, h792, hc13, hlam, hphi, u3elo3]
                    · linarith only [h0, h394, h783, hc13, hlam, hphi, u3elo2]
        · linarith only [h0, h394, h702, hc13, hlam, hphi, u3elo2]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h797 | h797
    · rcases m.htr 0 1 5 (by decide) (by decide) with h798 | h798
      · rcases m.htr 0 2 3 (by decide) (by decide) with h799 | h799
        · rcases m.htr 0 2 4 (by decide) (by decide) with h800 | h800
          · rcases m.htr 0 2 5 (by decide) (by decide) with h801 | h801
            · rcases m.htr 0 3 4 (by decide) (by decide) with h802 | h802
              · rcases m.htr 0 3 5 (by decide) (by decide) with h803 | h803
                · rcases m.htr 0 4 5 (by decide) (by decide) with h804 | h804
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h805 | h805
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h806 | h806
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h807 | h807
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h808 | h808
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h809 | h809
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h810 | h810
                              · linarith only [h394, h797, h810, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                              · linarith only [h394, h797, h804, h806, h810, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · linarith only [h394, h809, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h394, h799, h802, h808, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h394, h797, h801, h806, h807, hc12, hc24, hlam, hphi, ht0b, ht23, ht45, ht5b, u0elo1, u3elo1]
                      · linarith only [h394, h800, h805, h806, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h797, h799, h805, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h818 | h818
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h819 | h819
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h820 | h820
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h821 | h821
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h822 | h822
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h823 | h823
                              · linarith only [h797, h804, h823, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h825 | h825
                                · linarith only [h799, h825, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · linarith only [h799, h802, h825, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · linarith only [h394, h797, h819, h822, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h394, h797, h819, h821, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h394, h797, h801, h818, h819, h820, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h394, h800, h818, h819, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h797, h818, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · linarith only [h394, h798, h803, hlam]
              · linarith only [h394, h797, h802, hlam]
            · linarith only [h394, h798, h799, h801, hc23, hlam, hphi, u3elo1]
          · linarith only [h394, h797, h799, h800, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h837 | h837
          · rcases m.htr 0 2 5 (by decide) (by decide) with h838 | h838
            · rcases m.htr 0 3 4 (by decide) (by decide) with h839 | h839
              · rcases m.htr 0 3 5 (by decide) (by decide) with h840 | h840
                · rcases m.htr 0 4 5 (by decide) (by decide) with h841 | h841
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h842 | h842
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h843 | h843
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h844 | h844
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h845 | h845
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h846 | h846
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h847 | h847
                              · linarith only [h0, h797, h799, h842, h847, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                              · linarith only [h841, h847, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                            · linarith only [h0, h799, h842, h846, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h0, h799, h842, h845, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h797, h799, h838, h842, h843, h844, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                      · linarith only [h0, h797, h799, h842, h843, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h797, h842, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h855 | h855
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h856 | h856
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h857 | h857
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h858 | h858
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h859 | h859
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h860 | h860
                              · linarith only [h797, h841, h860, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h862 | h862
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h863 | h863
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h864 | h864
                                    · linarith only [h0, h797, h799, h841, h855, h856, h864, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h866 | h866
                                      · linarith only [h0, h798, h799, h841, h855, h856, h860, h862, h866, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                      · rcases h2bigk with h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c
                                        · have p868_0 := h868c.1
                                          have p868_1 := h868c.2.1
                                          have p868_2 := h868c.2.2.1
                                          have p868_3 := h868c.2.2.2
                                          linarith only [hlam, p868_0]
                                        · have p868_0 := h868c.1
                                          have p868_1 := h868c.2.1
                                          have p868_2 := h868c.2.2.1
                                          have p868_3 := h868c.2.2.2
                                          linarith only [h0, hlam, p868_1]
                                        · have p868_0 := h868c.1
                                          have p868_1 := h868c.2.1
                                          have p868_2 := h868c.2.2.1
                                          have p868_3 := h868c.2.2.2
                                          linarith only [h799, hlam, p868_0]
                                        · have p868_0 := h868c.1
                                          have p868_1 := h868c.2.1
                                          have p868_2 := h868c.2.2.1
                                          have p868_3 := h868c.2.2.2
                                          linarith only [h799, h855, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p868_1, u3elo1]
                                        · have p868_0 := h868c.1
                                          have p868_1 := h868c.2.1
                                          have p868_2 := h868c.2.2.1
                                          have p868_3 := h868c.2.2.2
                                          linarith only [h799, h855, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p868_1, u3elo1]
                                        · have p868_0 := h868c.1
                                          have p868_1 := h868c.2.1
                                          have p868_2 := h868c.2.2.1
                                          have p868_3 := h868c.2.2.2
                                          rcases p868_3 (m.d 0 2) (by simp) with h874 | h874
                                          · linarith only [h0, h874, hlam]
                                          · rcases p868_3 (m.d 1 2) (by simp) with h876 | h876
                                            · rcases p868_3 (m.d 2 3) (by simp) with h877 | h877
                                              · linarith only [h855, h877, hlam]
                                              · linarith only [h799, h877, hlam]
                                            · linarith only [h0, h876, hlam]
                                        · have p868_0 := h868c.1
                                          have p868_1 := h868c.2.1
                                          have p868_2 := h868c.2.2.1
                                          have p868_3 := h868c.2.2.2
                                          linarith only [hlam, p868_0]
                                        · have p868_0 := h868c.1
                                          have p868_1 := h868c.2.1
                                          have p868_2 := h868c.2.2.1
                                          have p868_3 := h868c.2.2.2
                                          linarith only [h0, h799, hc01, hc12, hlam, hphi, p868_1]
                                        · have p868_0 := h868c.1
                                          have p868_1 := h868c.2.1
                                          have p868_2 := h868c.2.2.1
                                          have p868_3 := h868c.2.2.2
                                          linarith only [h799, h837, h855, hlam, p868_2]
                                        · have p868_0 := h868c.1
                                          have p868_1 := h868c.2.1
                                          have p868_2 := h868c.2.2.1
                                          have p868_3 := h868c.2.2.2
                                          linarith only [h799, h838, h855, hlam, p868_2]
                                        · have p868_0 := h868c.1
                                          have p868_1 := h868c.2.1
                                          have p868_2 := h868c.2.2.1
                                          have p868_3 := h868c.2.2.2
                                          linarith only [h0, h798, h855, h856, h860, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p868_1]
                                        · have p868_0 := h868c.1
                                          have p868_1 := h868c.2.1
                                          have p868_2 := h868c.2.2.1
                                          have p868_3 := h868c.2.2.2
                                          linarith only [h855, hlam, p868_0]
                                        · have p868_0 := h868c.1
                                          have p868_1 := h868c.2.1
                                          have p868_2 := h868c.2.2.1
                                          have p868_3 := h868c.2.2.2
                                          linarith only [hlam, p868_0]
                                        · have p868_0 := h868c.1
                                          have p868_1 := h868c.2.1
                                          have p868_2 := h868c.2.2.1
                                          have p868_3 := h868c.2.2.2
                                          rcases p868_3 (m.d 0 2) (by simp) with h888 | h888
                                          · linarith only [h799, h888, hlam]
                                          · linarith only [h837, h888, hlam]
                                        · have p868_0 := h868c.1
                                          have p868_1 := h868c.2.1
                                          have p868_2 := h868c.2.2.1
                                          have p868_3 := h868c.2.2.2
                                          rcases p868_3 (m.d 0 2) (by simp) with h891 | h891
                                          · linarith only [h799, h891, hlam]
                                          · linarith only [h838, h891, hlam]
                                        · have p868_0 := h868c.1
                                          have p868_1 := h868c.2.1
                                          have p868_2 := h868c.2.2.1
                                          have p868_3 := h868c.2.2.2
                                          linarith only [h837, hlam, p868_0]
                                        · have p868_0 := h868c.1
                                          have p868_1 := h868c.2.1
                                          have p868_2 := h868c.2.2.1
                                          have p868_3 := h868c.2.2.2
                                          linarith only [h856, hlam, p868_0]
                                        · have p868_0 := h868c.1
                                          have p868_1 := h868c.2.1
                                          have p868_2 := h868c.2.2.1
                                          have p868_3 := h868c.2.2.2
                                          linarith only [h862, hlam, p868_1]
                                        · have p868_0 := h868c.1
                                          have p868_1 := h868c.2.1
                                          have p868_2 := h868c.2.2.1
                                          have p868_3 := h868c.2.2.2
                                          linarith only [hlam, p868_0]
                                        · have p868_0 := h868c.1
                                          have p868_1 := h868c.2.1
                                          have p868_2 := h868c.2.2.1
                                          have p868_3 := h868c.2.2.2
                                          linarith only [h864, hlam, p868_1]
                                        · have p868_0 := h868c.1
                                          have p868_1 := h868c.2.1
                                          have p868_2 := h868c.2.2.1
                                          have p868_3 := h868c.2.2.2
                                          linarith only [h838, hlam, p868_0]
                                        · have p868_0 := h868c.1
                                          have p868_1 := h868c.2.1
                                          have p868_2 := h868c.2.2.1
                                          have p868_3 := h868c.2.2.2
                                          linarith only [h857, hlam, p868_0]
                                        · have p868_0 := h868c.1
                                          have p868_1 := h868c.2.1
                                          have p868_2 := h868c.2.2.1
                                          have p868_3 := h868c.2.2.2
                                          linarith only [h863, hlam, p868_1]
                                        · have p868_0 := h868c.1
                                          have p868_1 := h868c.2.1
                                          have p868_2 := h868c.2.2.1
                                          have p868_3 := h868c.2.2.2
                                          linarith only [h798, h857, h862, hc34, hlam, hphi, ht0b, ht45, ht5b, p868_1, u0elo0]
                                        · have p868_0 := h868c.1
                                          have p868_1 := h868c.2.1
                                          have p868_2 := h868c.2.2.1
                                          have p868_3 := h868c.2.2.2
                                          linarith only [hlam, p868_0]
                                  · linarith only [h0, h799, h863, hc01, hlam, hphi, ht12, ht23, u3elo4]
                                · linarith only [h0, h799, h862, hc01, hlam, hphi, ht12, ht23, u3elo3]
                            · linarith only [h394, h797, h856, h859, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h0, h797, h799, h855, h856, h858, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h838, h857, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h799, h855, h856, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h797, h855, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · linarith only [h394, h798, h840, hlam]
              · linarith only [h0, h797, h799, h839, hlam]
            · linarith only [h0, h798, h838, hlam]
          · linarith only [h0, h797, h837, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h915 | h915
        · rcases m.htr 0 2 4 (by decide) (by decide) with h916 | h916
          · rcases m.htr 0 2 5 (by decide) (by decide) with h917 | h917
            · rcases m.htr 0 3 4 (by decide) (by decide) with h918 | h918
              · rcases m.htr 0 3 5 (by decide) (by decide) with h919 | h919
                · rcases m.htr 0 4 5 (by decide) (by decide) with h920 | h920
                  · linarith only [h797, h798, h920, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h922 | h922
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h923 | h923
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h924 | h924
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h925 | h925
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h926 | h926
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h927 | h927
                              · linarith only [h797, h920, h927, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h929 | h929
                                · linarith only [h915, h929, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · linarith only [h915, h918, h929, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · linarith only [h915, h919, h926, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h394, h797, h923, h925, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h394, h797, h917, h922, h923, h924, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h394, h916, h922, h923, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h797, h922, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h937 | h937
                  · linarith only [h394, h797, h919, h937, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h939 | h939
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h940 | h940
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h941 | h941
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h942 | h942
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h943 | h943
                            · linarith only [h394, h919, h943, hc01, hlam, hphi, ht12, ht23, u3elo1]
                            · linarith only [h394, h797, h940, h943, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h394, h797, h940, h942, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h394, h797, h917, h939, h940, h941, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h394, h916, h939, h940, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h915, h939, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h394, h797, h918, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h951 | h951
              · rcases m.htr 0 3 5 (by decide) (by decide) with h952 | h952
                · linarith only [h915, h917, h952, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h954 | h954
                  · linarith only [h394, h797, h915, h917, h954, hc23, hlam, hphi, u3elo1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h956 | h956
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h957 | h957
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h958 | h958
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h959 | h959
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h960 | h960
                            · linarith only [h394, h952, h960, hc01, hlam, hphi, ht12, ht23, u3elo1]
                            · linarith only [h394, h797, h957, h960, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h394, h797, h957, h959, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h964 | h964
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h965 | h965
                            · linarith only [h394, h797, h952, h957, h965, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · linarith only [h394, h797, h957, h965, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h394, h797, h957, h964, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · linarith only [h916, h957, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h797, h956, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · linarith only [h394, h797, h951, hlam]
          · linarith only [h394, h797, h915, h916, hc23, hlam, hphi, u3elo1]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h973 | h973
          · rcases m.htr 0 2 5 (by decide) (by decide) with h974 | h974
            · rcases m.htr 0 3 4 (by decide) (by decide) with h975 | h975
              · rcases m.htr 0 3 5 (by decide) (by decide) with h976 | h976
                · rcases m.htr 0 4 5 (by decide) (by decide) with h977 | h977
                  · linarith only [h797, h798, h977, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h979 | h979
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h980 | h980
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h981 | h981
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h982 | h982
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h983 | h983
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h984 | h984
                              · linarith only [h797, h798, h915, h974, h977, h979, h984, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h986 | h986
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h987 | h987
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h988 | h988
                                    · linarith only [h797, h798, h915, h974, h979, h980, h984, h988, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h990 | h990
                                      · linarith only [h797, h798, h980, h984, h986, h990, hlam]
                                      · rcases h2bigk with h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c
                                        · have p992_0 := h992c.1
                                          have p992_1 := h992c.2.1
                                          have p992_2 := h992c.2.2.1
                                          have p992_3 := h992c.2.2.2
                                          linarith only [hlam, p992_0]
                                        · have p992_0 := h992c.1
                                          have p992_1 := h992c.2.1
                                          have p992_2 := h992c.2.2.1
                                          have p992_3 := h992c.2.2.2
                                          linarith only [h0, hlam, p992_1]
                                        · have p992_0 := h992c.1
                                          have p992_1 := h992c.2.1
                                          have p992_2 := h992c.2.2.1
                                          have p992_3 := h992c.2.2.2
                                          linarith only [h915, hlam, p992_0]
                                        · have p992_0 := h992c.1
                                          have p992_1 := h992c.2.1
                                          have p992_2 := h992c.2.2.1
                                          have p992_3 := h992c.2.2.2
                                          linarith only [h915, h979, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p992_1, u3elo1]
                                        · have p992_0 := h992c.1
                                          have p992_1 := h992c.2.1
                                          have p992_2 := h992c.2.2.1
                                          have p992_3 := h992c.2.2.2
                                          linarith only [h915, h979, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p992_1, u3elo1]
                                        · have p992_0 := h992c.1
                                          have p992_1 := h992c.2.1
                                          have p992_2 := h992c.2.2.1
                                          have p992_3 := h992c.2.2.2
                                          rcases p992_3 (m.d 0 2) (by simp) with h998 | h998
                                          · linarith only [h0, h998, hlam]
                                          · rcases p992_3 (m.d 1 2) (by simp) with h1000 | h1000
                                            · rcases p992_3 (m.d 2 3) (by simp) with h1001 | h1001
                                              · linarith only [h1001, h979, hlam]
                                              · linarith only [h1001, h915, hlam]
                                            · linarith only [h0, h1000, hlam]
                                        · have p992_0 := h992c.1
                                          have p992_1 := h992c.2.1
                                          have p992_2 := h992c.2.2.1
                                          have p992_3 := h992c.2.2.2
                                          linarith only [hlam, p992_0]
                                        · have p992_0 := h992c.1
                                          have p992_1 := h992c.2.1
                                          have p992_2 := h992c.2.2.1
                                          have p992_3 := h992c.2.2.2
                                          linarith only [h798, h915, h974, hc01, hc12, hlam, hphi, p992_1]
                                        · have p992_0 := h992c.1
                                          have p992_1 := h992c.2.1
                                          have p992_2 := h992c.2.2.1
                                          have p992_3 := h992c.2.2.2
                                          linarith only [h915, h973, h979, hlam, p992_2]
                                        · have p992_0 := h992c.1
                                          have p992_1 := h992c.2.1
                                          have p992_2 := h992c.2.2.1
                                          have p992_3 := h992c.2.2.2
                                          linarith only [h915, h974, h979, hlam, p992_2]
                                        · have p992_0 := h992c.1
                                          have p992_1 := h992c.2.1
                                          have p992_2 := h992c.2.2.1
                                          have p992_3 := h992c.2.2.2
                                          linarith only [h797, h798, h974, h979, h980, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p992_1, u3elo1]
                                        · have p992_0 := h992c.1
                                          have p992_1 := h992c.2.1
                                          have p992_2 := h992c.2.2.1
                                          have p992_3 := h992c.2.2.2
                                          linarith only [h979, hlam, p992_0]
                                        · have p992_0 := h992c.1
                                          have p992_1 := h992c.2.1
                                          have p992_2 := h992c.2.2.1
                                          have p992_3 := h992c.2.2.2
                                          linarith only [hlam, p992_0]
                                        · have p992_0 := h992c.1
                                          have p992_1 := h992c.2.1
                                          have p992_2 := h992c.2.2.1
                                          have p992_3 := h992c.2.2.2
                                          rcases p992_3 (m.d 0 2) (by simp) with h1012 | h1012
                                          · linarith only [h1012, h915, hlam]
                                          · linarith only [h1012, h973, hlam]
                                        · have p992_0 := h992c.1
                                          have p992_1 := h992c.2.1
                                          have p992_2 := h992c.2.2.1
                                          have p992_3 := h992c.2.2.2
                                          rcases p992_3 (m.d 0 2) (by simp) with h1015 | h1015
                                          · linarith only [h1015, h915, hlam]
                                          · linarith only [h1015, h974, hlam]
                                        · have p992_0 := h992c.1
                                          have p992_1 := h992c.2.1
                                          have p992_2 := h992c.2.2.1
                                          have p992_3 := h992c.2.2.2
                                          linarith only [h973, hlam, p992_0]
                                        · have p992_0 := h992c.1
                                          have p992_1 := h992c.2.1
                                          have p992_2 := h992c.2.2.1
                                          have p992_3 := h992c.2.2.2
                                          linarith only [h980, hlam, p992_0]
                                        · have p992_0 := h992c.1
                                          have p992_1 := h992c.2.1
                                          have p992_2 := h992c.2.2.1
                                          have p992_3 := h992c.2.2.2
                                          linarith only [h986, hlam, p992_1]
                                        · have p992_0 := h992c.1
                                          have p992_1 := h992c.2.1
                                          have p992_2 := h992c.2.2.1
                                          have p992_3 := h992c.2.2.2
                                          linarith only [hlam, p992_0]
                                        · have p992_0 := h992c.1
                                          have p992_1 := h992c.2.1
                                          have p992_2 := h992c.2.2.1
                                          have p992_3 := h992c.2.2.2
                                          linarith only [h988, hlam, p992_1]
                                        · have p992_0 := h992c.1
                                          have p992_1 := h992c.2.1
                                          have p992_2 := h992c.2.2.1
                                          have p992_3 := h992c.2.2.2
                                          linarith only [h974, hlam, p992_0]
                                        · have p992_0 := h992c.1
                                          have p992_1 := h992c.2.1
                                          have p992_2 := h992c.2.2.1
                                          have p992_3 := h992c.2.2.2
                                          linarith only [h981, hlam, p992_0]
                                        · have p992_0 := h992c.1
                                          have p992_1 := h992c.2.1
                                          have p992_2 := h992c.2.2.1
                                          have p992_3 := h992c.2.2.2
                                          linarith only [h987, hlam, p992_1]
                                        · have p992_0 := h992c.1
                                          have p992_1 := h992c.2.1
                                          have p992_2 := h992c.2.2.1
                                          have p992_3 := h992c.2.2.2
                                          linarith only [h974, h986, hc34, hlam, hphi, ht0b, ht45, ht5b, p992_1, u0elo1]
                                        · have p992_0 := h992c.1
                                          have p992_1 := h992c.2.1
                                          have p992_2 := h992c.2.2.1
                                          have p992_3 := h992c.2.2.2
                                          linarith only [hlam, p992_0]
                                  · linarith only [h915, h987, hc02, hlam, hphi, ht23, u3elo4]
                                · linarith only [h797, h798, h915, h974, h980, h986, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                            · linarith only [h976, h983, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h797, h798, h915, h974, h979, h980, h982, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h797, h798, h915, h974, h979, h980, h981, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h798, h915, h974, h979, h980, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h797, h979, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · linarith only [h915, h974, h976, hlam]
              · linarith only [h797, h798, h915, h974, h975, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1037 | h1037
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1038 | h1038
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1039 | h1039
                  · linarith only [h0, h1039, h797, h974, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1041 | h1041
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1042 | h1042
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1043 | h1043
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1044 | h1044
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1045 | h1045
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1046 | h1046
                              · linarith only [h1039, h1046, h797, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1048 | h1048
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1049 | h1049
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1050 | h1050
                                    · linarith only [h1043, h1046, h1050, h973, h974, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1052 | h1052
                                      · linarith only [h0, h1043, h1046, h1052, h974, hc01, hlam, hphi, ht12, ht23, u3elo3]
                                      · rcases h2bigk with h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c
                                        · have p1054_0 := h1054c.1
                                          have p1054_1 := h1054c.2.1
                                          have p1054_2 := h1054c.2.2.1
                                          have p1054_3 := h1054c.2.2.2
                                          linarith only [hlam, p1054_0]
                                        · have p1054_0 := h1054c.1
                                          have p1054_1 := h1054c.2.1
                                          have p1054_2 := h1054c.2.2.1
                                          have p1054_3 := h1054c.2.2.2
                                          linarith only [h0, hlam, p1054_1]
                                        · have p1054_0 := h1054c.1
                                          have p1054_1 := h1054c.2.1
                                          have p1054_2 := h1054c.2.2.1
                                          have p1054_3 := h1054c.2.2.2
                                          linarith only [h915, hlam, p1054_0]
                                        · have p1054_0 := h1054c.1
                                          have p1054_1 := h1054c.2.1
                                          have p1054_2 := h1054c.2.2.1
                                          have p1054_3 := h1054c.2.2.2
                                          linarith only [h1043, h1045, h974, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1054_1, u3elo1]
                                        · have p1054_0 := h1054c.1
                                          have p1054_1 := h1054c.2.1
                                          have p1054_2 := h1054c.2.2.1
                                          have p1054_3 := h1054c.2.2.2
                                          linarith only [h974, hlam, p1054_0]
                                        · have p1054_0 := h1054c.1
                                          have p1054_1 := h1054c.2.1
                                          have p1054_2 := h1054c.2.2.1
                                          have p1054_3 := h1054c.2.2.2
                                          rcases p1054_3 (m.d 0 2) (by simp) with h1060 | h1060
                                          · linarith only [h0, h1060, hlam]
                                          · rcases p1054_3 (m.d 1 2) (by simp) with h1062 | h1062
                                            · rcases p1054_3 (m.d 2 3) (by simp) with h1063 | h1063
                                              · linarith only [h1041, h1063, hlam]
                                              · linarith only [h1063, h915, hlam]
                                            · linarith only [h0, h1062, hlam]
                                        · have p1054_0 := h1054c.1
                                          have p1054_1 := h1054c.2.1
                                          have p1054_2 := h1054c.2.2.1
                                          have p1054_3 := h1054c.2.2.2
                                          linarith only [hlam, p1054_0]
                                        · have p1054_0 := h1054c.1
                                          have p1054_1 := h1054c.2.1
                                          have p1054_2 := h1054c.2.2.1
                                          have p1054_3 := h1054c.2.2.2
                                          linarith only [h0, h915, hc01, hc12, hlam, hphi, p1054_1]
                                        · have p1054_0 := h1054c.1
                                          have p1054_1 := h1054c.2.1
                                          have p1054_2 := h1054c.2.2.1
                                          have p1054_3 := h1054c.2.2.2
                                          linarith only [h1041, h915, h973, hlam, p1054_2]
                                        · have p1054_0 := h1054c.1
                                          have p1054_1 := h1054c.2.1
                                          have p1054_2 := h1054c.2.2.1
                                          have p1054_3 := h1054c.2.2.2
                                          linarith only [h0, h1042, h797, h974, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1054_1]
                                        · have p1054_0 := h1054c.1
                                          have p1054_1 := h1054c.2.1
                                          have p1054_2 := h1054c.2.2.1
                                          have p1054_3 := h1054c.2.2.2
                                          linarith only [h0, h1042, h797, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1054_1, u3elo2]
                                        · have p1054_0 := h1054c.1
                                          have p1054_1 := h1054c.2.1
                                          have p1054_2 := h1054c.2.2.1
                                          have p1054_3 := h1054c.2.2.2
                                          linarith only [h1041, hlam, p1054_0]
                                        · have p1054_0 := h1054c.1
                                          have p1054_1 := h1054c.2.1
                                          have p1054_2 := h1054c.2.2.1
                                          have p1054_3 := h1054c.2.2.2
                                          linarith only [hlam, p1054_0]
                                        · have p1054_0 := h1054c.1
                                          have p1054_1 := h1054c.2.1
                                          have p1054_2 := h1054c.2.2.1
                                          have p1054_3 := h1054c.2.2.2
                                          rcases p1054_3 (m.d 0 2) (by simp) with h1074 | h1074
                                          · linarith only [h1074, h915, hlam]
                                          · linarith only [h1074, h973, hlam]
                                        · have p1054_0 := h1054c.1
                                          have p1054_1 := h1054c.2.1
                                          have p1054_2 := h1054c.2.2.1
                                          have p1054_3 := h1054c.2.2.2
                                          linarith only [h0, h1041, h1042, h1048, h797, h974, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1054_1, u3elo1]
                                        · have p1054_0 := h1054c.1
                                          have p1054_1 := h1054c.2.1
                                          have p1054_2 := h1054c.2.2.1
                                          have p1054_3 := h1054c.2.2.2
                                          linarith only [h973, hlam, p1054_0]
                                        · have p1054_0 := h1054c.1
                                          have p1054_1 := h1054c.2.1
                                          have p1054_2 := h1054c.2.2.1
                                          have p1054_3 := h1054c.2.2.2
                                          linarith only [h1042, hlam, p1054_0]
                                        · have p1054_0 := h1054c.1
                                          have p1054_1 := h1054c.2.1
                                          have p1054_2 := h1054c.2.2.1
                                          have p1054_3 := h1054c.2.2.2
                                          linarith only [h1048, hlam, p1054_1]
                                        · have p1054_0 := h1054c.1
                                          have p1054_1 := h1054c.2.1
                                          have p1054_2 := h1054c.2.2.1
                                          have p1054_3 := h1054c.2.2.2
                                          linarith only [hlam, p1054_0]
                                        · have p1054_0 := h1054c.1
                                          have p1054_1 := h1054c.2.1
                                          have p1054_2 := h1054c.2.2.1
                                          have p1054_3 := h1054c.2.2.2
                                          linarith only [h1050, hlam, p1054_1]
                                        · have p1054_0 := h1054c.1
                                          have p1054_1 := h1054c.2.1
                                          have p1054_2 := h1054c.2.2.1
                                          have p1054_3 := h1054c.2.2.2
                                          linarith only [h0, h1042, h1043, h1048, h797, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1054_1]
                                        · have p1054_0 := h1054c.1
                                          have p1054_1 := h1054c.2.1
                                          have p1054_2 := h1054c.2.2.1
                                          have p1054_3 := h1054c.2.2.2
                                          linarith only [h1043, hlam, p1054_0]
                                        · have p1054_0 := h1054c.1
                                          have p1054_1 := h1054c.2.1
                                          have p1054_2 := h1054c.2.2.1
                                          have p1054_3 := h1054c.2.2.2
                                          linarith only [h1049, hlam, p1054_1]
                                        · have p1054_0 := h1054c.1
                                          have p1054_1 := h1054c.2.1
                                          have p1054_2 := h1054c.2.2.1
                                          have p1054_3 := h1054c.2.2.2
                                          rcases p1054_3 (m.d 0 2) (by simp) with h1086 | h1086
                                          · linarith only [h1086, h974, hlam]
                                          · linarith only [h1086, h973, hlam]
                                        · have p1054_0 := h1054c.1
                                          have p1054_1 := h1054c.2.1
                                          have p1054_2 := h1054c.2.2.1
                                          have p1054_3 := h1054c.2.2.2
                                          linarith only [hlam, p1054_0]
                                  · linarith only [h1038, h1049, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                                · linarith only [h0, h1042, h1048, h797, h915, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                            · linarith only [h1038, h1045, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h0, h1041, h1042, h1044, h797, h915, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h0, h1041, h1042, h1043, h797, h915, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h1041, h1042, h915, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h1041, h797, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1097 | h1097
                  · linarith only [h1097, h797, h798, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1099 | h1099
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1100 | h1100
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1101 | h1101
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1102 | h1102
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1103 | h1103
                            · linarith only [h1038, h1103, hc03, hlam, hphi, u3elo1]
                            · linarith only [h1100, h1103, h394, h797, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h0, h1099, h1100, h1102, h797, h915, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h0, h1099, h1100, h1101, h797, h915, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h1099, h1100, h797, h915, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h1099, h797, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · linarith only [h0, h1037, h797, h915, hlam]
          · linarith only [h0, h797, h973, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1112 | h1112
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1113 | h1113
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1114 | h1114
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1115 | h1115
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1116 | h1116
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1117 | h1117
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1118 | h1118
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1119 | h1119
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1120 | h1120
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1121 | h1121
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1122 | h1122
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1123 | h1123
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1124 | h1124
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1125 | h1125
                                · linarith only [h1113, h1125, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · linarith only [h1116, h1125, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                              · linarith only [h1118, h1124, h797, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                            · linarith only [h1112, h1121, h1123, h394, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                          · linarith only [h1112, h1113, h1116, h1121, h1122, h394, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                        · linarith only [h1115, h1119, h1121, h394, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h1112, h1114, h1119, h1120, h394, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                    · linarith only [h0, h1112, h1119, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                  · linarith only [h1112, h1118, h797, hlam]
                · linarith only [h1112, h1117, h394, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1136 | h1136
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1137 | h1137
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1138 | h1138
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1139 | h1139
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1140 | h1140
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1141 | h1141
                          · linarith only [h1116, h1141, h394, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h1112, h1140, h1141, h394, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                        · linarith only [h1115, h1138, h1140, h394, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h1112, h1114, h1138, h1139, h394, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                    · linarith only [h0, h1112, h1138, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                  · linarith only [h1112, h1116, h1137, h394, hlam]
                · linarith only [h1112, h1136, h394, hlam]
            · linarith only [h1112, h1113, h1115, h394, hc23, hlam, hphi, u3elo1]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1150 | h1150
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1151 | h1151
              · linarith only [h1113, h1114, h1151, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1153 | h1153
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1154 | h1154
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1155 | h1155
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1156 | h1156
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1157 | h1157
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1158 | h1158
                          · linarith only [h1151, h1158, h394, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h1112, h1157, h1158, h394, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                        · linarith only [h1113, h1114, h1156, h1157, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1162 | h1162
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1163 | h1163
                          · linarith only [h1112, h1151, h1162, h1163, h394, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                          · linarith only [h1112, h1162, h1163, h394, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                        · linarith only [h1114, h1150, h1162, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h0, h1112, h1113, h1114, h1155, hc15, hlam, hphi, ht0b, ht5b, u0elo3]
                  · linarith only [h1112, h1113, h1114, h1151, h1154, h394, hc23, hlam, hphi, u3elo3]
                · linarith only [h1112, h1153, h394, hlam]
            · linarith only [h1112, h1113, h1150, h394, hc23, hlam, hphi, u3elo1]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1171 | h1171
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1172 | h1172
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1173 | h1173
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1174 | h1174
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1175 | h1175
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1176 | h1176
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1177 | h1177
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1178 | h1178
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1179 | h1179
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1180 | h1180
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1181 | h1181
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1182 | h1182
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1183 | h1183
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1184 | h1184
                                    · linarith only [h1113, h1171, h1176, h1184, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                                    · linarith only [h1113, h1171, h1175, h1176, h1184, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                  · linarith only [h1113, h1171, h1183, h797, hc01, hlam, hphi, ht12, ht23, u3elo4]
                                · linarith only [h1113, h1171, h1182, h797, hc01, hlam, hphi, ht12, ht23, u3elo3]
                              · linarith only [h1112, h1171, h1175, h1178, h1181, h797, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                            · linarith only [h1113, h1176, h1180, hc02, hlam, hphi, ht23, u3elo4]
                          · linarith only [h1112, h1113, h1171, h1173, h1176, h1178, h1179, h797, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                        · linarith only [h1113, h1171, h1176, h1178, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h1113, h1171, h1176, h1177, hlam]
                    · linarith only [h0, h1112, h1176, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                  · linarith only [h1112, h1175, h797, hlam]
                · linarith only [h1112, h1174, h394, hlam]
              · linarith only [h1113, h1171, h1173, hlam]
            · linarith only [h1112, h1171, h1172, h797, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1199 | h1199
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1200 | h1200
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1201 | h1201
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1202 | h1202
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1203 | h1203
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1204 | h1204
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1205 | h1205
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1206 | h1206
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1207 | h1207
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1208 | h1208
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1209 | h1209
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1210 | h1210
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1211 | h1211
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1212 | h1212
                                      · linarith only [h1200, h1212, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                                      · linarith only [h1202, h1212, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                                    · linarith only [h1112, h1171, h1208, h1211, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                                  · linarith only [h0, h1171, h1209, h1210, hc01, hlam, hphi, ht12, ht23, u3elo4]
                                · linarith only [h0, h1113, h1209, hc01, hlam, hphi, ht12, ht23, u3elo3]
                              · linarith only [h1200, h1202, h1208, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · linarith only [h1112, h1205, h1207, h394, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                          · linarith only [h0, h1112, h1113, h1200, h1203, h1205, h1206, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                        · linarith only [h1199, h1205, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h1113, h1203, h1204, hc02, hc24, hlam, hphi]
                    · linarith only [h0, h1203, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h1112, h1202, h797, hlam]
                · linarith only [h1112, h1201, h394, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1226 | h1226
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1227 | h1227
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1228 | h1228
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1229 | h1229
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1230 | h1230
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1231 | h1231
                          · linarith only [h0, h1113, h1200, h1231, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h1112, h1230, h1231, h394, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                        · linarith only [h0, h1113, h1228, h1230, hc01, hc25, hlam, hphi, ht12]
                      · linarith only [h0, h1112, h1113, h1228, h1229, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h0, h1112, h1228, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                  · linarith only [h1112, h1227, h797, hlam]
                · linarith only [h0, h1112, h1113, h1226, hlam]
            · linarith only [h0, h1112, h1199, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1240 | h1240
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1241 | h1241
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1242 | h1242
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1243 | h1243
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1244 | h1244
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1245 | h1245
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1246 | h1246
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1247 | h1247
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1248 | h1248
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1249 | h1249
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1250 | h1250
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1251 | h1251
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1252 | h1252
                                · linarith only [h1240, h1252, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · linarith only [h1243, h1252, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                              · linarith only [h1245, h1251, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                            · linarith only [h1249, h1250, h797, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h1243, h1249, h394, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h1242, h1246, h1248, h394, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h1241, h1247, hlam]
                    · linarith only [h0, h1246, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1261 | h1261
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1262 | h1262
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1263 | h1263
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1264 | h1264
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1265 | h1265
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1266 | h1266
                              · linarith only [h1245, h1264, h1266, h797, hc01, hlam, hphi, ht12, ht23, u3elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1268 | h1268
                                · linarith only [h1240, h1268, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · linarith only [h1243, h1268, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h1240, h1244, h1265, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h1243, h1244, h1264, h394, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                        · linarith only [h0, h1242, h1263, hlam]
                      · linarith only [h0, h1241, h1262, hlam]
                    · linarith only [h0, h1261, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1276 | h1276
                  · linarith only [h1243, h1244, h1276, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1278 | h1278
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1279 | h1279
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1280 | h1280
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1281 | h1281
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1282 | h1282
                            · linarith only [h1244, h1282, hc03, hlam, hphi, u3elo1]
                            · linarith only [h1282, h394, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h1243, h1281, h394, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h1242, h1280, hlam]
                      · linarith only [h0, h1240, h1241, h1279, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h0, h1240, h1278, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1289 | h1289
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1290 | h1290
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1291 | h1291
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1292 | h1292
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1293 | h1293
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1294 | h1294
                          · linarith only [h1243, h1294, hc03, hlam, hphi, u3elo1]
                          · linarith only [h1294, h394, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h1242, h1293, hlam]
                      · linarith only [h0, h1241, h1292, hlam]
                    · linarith only [h0, h1240, h1291, hlam]
                  · linarith only [h1243, h1289, h1290, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1301 | h1301
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1302 | h1302
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1303 | h1303
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1304 | h1304
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1305 | h1305
                          · linarith only [h1243, h1305, hc03, hlam, hphi, u3elo1]
                          · linarith only [h1305, h394, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h1241, h1242, h1304, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                      · linarith only [h1241, h1302, h1303, h394, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1302, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1311 | h1311
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1312 | h1312
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1313 | h1313
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1314 | h1314
                          · linarith only [h1243, h1314, h394, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h1314, h394, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h1242, h1313, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h1241, h1312, hlam]
                    · linarith only [h0, h1240, h1241, h1311, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1320 | h1320
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1321 | h1321
                · linarith only [h1240, h1242, h1321, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1323 | h1323
                  · linarith only [h1241, h1242, h1323, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1325 | h1325
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1326 | h1326
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1327 | h1327
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1328 | h1328
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1329 | h1329
                            · linarith only [h1321, h1329, hc03, hlam, hphi, u3elo1]
                            · linarith only [h1329, h394, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h1320, h1328, h394, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1333 | h1333
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1334 | h1334
                            · linarith only [h1321, h1334, hc03, hlam, hphi, u3elo1]
                            · linarith only [h1334, h394, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h1333, h394, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h1241, h1326, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1325, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1340 | h1340
                · linarith only [h1241, h1242, h1320, h1340, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1342 | h1342
                  · linarith only [h1241, h1242, h1342, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1344 | h1344
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1345 | h1345
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1346 | h1346
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1347 | h1347
                          · linarith only [h1320, h1347, hc03, hlam, hphi, u3elo1]
                          · linarith only [h1347, h394, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1350 | h1350
                          · linarith only [h1320, h1350, h394, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h1350, h394, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h1241, h1345, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1344, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1355 | h1355
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1356 | h1356
              · linarith only [h1240, h1241, h1356, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1358 | h1358
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1359 | h1359
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1360 | h1360
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1361 | h1361
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1362 | h1362
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1363 | h1363
                          · linarith only [h1356, h1363, hc03, hlam, hphi, u3elo1]
                          · linarith only [h1363, h394, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h1241, h1355, h1361, h1362, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1367 | h1367
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1368 | h1368
                          · linarith only [h1356, h1358, h1368, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                          · linarith only [h1368, h394, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h1355, h1367, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1360, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h1240, h1241, h1358, h1359, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1374 | h1374
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1375 | h1375
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1376 | h1376
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1377 | h1377
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1378 | h1378
                          · linarith only [h1356, h1378, hc03, hlam, hphi, u3elo1]
                          · linarith only [h1378, h394, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h1240, h1241, h1376, h1377, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1382 | h1382
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1383 | h1383
                          · linarith only [h1356, h1383, h394, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h1383, h394, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h1355, h1382, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1375, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h1241, h1355, h1374, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1389 | h1389
              · linarith only [h1240, h1241, h1389, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1391 | h1391
                · linarith only [h1240, h1355, h1391, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1393 | h1393
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1394 | h1394
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1395 | h1395
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1396 | h1396
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1397 | h1397
                          · linarith only [h1389, h1397, hc03, hlam, hphi, u3elo1]
                          · linarith only [h1397, h394, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h1240, h1241, h1395, h1396, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1401 | h1401
                        · linarith only [h1240, h1355, h1395, h1401, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1403 | h1403
                          · linarith only [h1389, h1403, h394, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h1403, h394, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h1240, h1394, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1407 | h1407
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1408 | h1408
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1409 | h1409
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1410 | h1410
                          · linarith only [h1389, h1410, h394, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h1410, h394, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h1241, h1408, h1409, hc02, hc25, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1414 | h1414
                        · linarith only [h1240, h1355, h1408, h1414, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1416 | h1416
                          · linarith only [h1389, h1416, h394, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h1416, h394, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h1240, h1407, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1420 | h1420
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1421 | h1421
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1422 | h1422
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1423 | h1423
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1424 | h1424
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1425 | h1425
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1426 | h1426
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1427 | h1427
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1428 | h1428
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1429 | h1429
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1430 | h1430
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1431 | h1431
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1432 | h1432
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1433 | h1433
                                    · linarith only [h1240, h1420, h1425, h1433, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                                    · linarith only [h1240, h1420, h1424, h1425, h1431, h1433, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                  · linarith only [h1240, h1432, hc02, hlam, hphi, ht23, u3elo4]
                                · linarith only [h1240, h1431, hc02, hlam, hphi, ht23, u3elo3]
                              · linarith only [h1240, h1420, h1424, h1425, h1430, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · linarith only [h1240, h1423, h1425, h1429, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h1240, h1420, h1422, h1425, h1428, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h1240, h1421, h1425, h1427, hlam]
                      · linarith only [h1240, h1420, h1425, h1426, hlam]
                    · linarith only [h0, h1425, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1444 | h1444
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1445 | h1445
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1446 | h1446
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1447 | h1447
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1448 | h1448
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1449 | h1449
                              · linarith only [h1424, h1447, h1449, h797, hc01, hlam, hphi, ht12, ht23, u3elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1451 | h1451
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1452 | h1452
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1453 | h1453
                                    · linarith only [h1420, h1449, h1453, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1455 | h1455
                                      · linarith only [h1449, h1455, h797, hc01, hlam, hphi, ht12, ht23, u3elo3]
                                      · rcases h2bigk with h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c
                                        · have p1457_0 := h1457c.1
                                          have p1457_1 := h1457c.2.1
                                          have p1457_2 := h1457c.2.2.1
                                          have p1457_3 := h1457c.2.2.2
                                          linarith only [hlam, p1457_0]
                                        · have p1457_0 := h1457c.1
                                          have p1457_1 := h1457c.2.1
                                          have p1457_2 := h1457c.2.2.1
                                          have p1457_3 := h1457c.2.2.2
                                          linarith only [h0, hlam, p1457_1]
                                        · have p1457_0 := h1457c.1
                                          have p1457_1 := h1457c.2.1
                                          have p1457_2 := h1457c.2.2.1
                                          have p1457_3 := h1457c.2.2.2
                                          linarith only [h1240, hlam, p1457_0]
                                        · have p1457_0 := h1457c.1
                                          have p1457_1 := h1457c.2.1
                                          have p1457_2 := h1457c.2.2.1
                                          have p1457_3 := h1457c.2.2.2
                                          linarith only [h1240, h1444, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1457_1, u3elo1]
                                        · have p1457_0 := h1457c.1
                                          have p1457_1 := h1457c.2.1
                                          have p1457_2 := h1457c.2.2.1
                                          have p1457_3 := h1457c.2.2.2
                                          linarith only [h1240, h1444, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1457_1, u3elo1]
                                        · have p1457_0 := h1457c.1
                                          have p1457_1 := h1457c.2.1
                                          have p1457_2 := h1457c.2.2.1
                                          have p1457_3 := h1457c.2.2.2
                                          rcases p1457_3 (m.d 0 2) (by simp) with h1463 | h1463
                                          · linarith only [h0, h1463, hlam]
                                          · rcases p1457_3 (m.d 1 2) (by simp) with h1465 | h1465
                                            · rcases p1457_3 (m.d 2 3) (by simp) with h1466 | h1466
                                              · linarith only [h1444, h1466, hlam]
                                              · linarith only [h1240, h1466, hlam]
                                            · linarith only [h0, h1465, hlam]
                                        · have p1457_0 := h1457c.1
                                          have p1457_1 := h1457c.2.1
                                          have p1457_2 := h1457c.2.2.1
                                          have p1457_3 := h1457c.2.2.2
                                          linarith only [hlam, p1457_0]
                                        · have p1457_0 := h1457c.1
                                          have p1457_1 := h1457c.2.1
                                          have p1457_2 := h1457c.2.2.1
                                          have p1457_3 := h1457c.2.2.2
                                          linarith only [h0, h1240, hc01, hc12, hlam, hphi, p1457_1]
                                        · have p1457_0 := h1457c.1
                                          have p1457_1 := h1457c.2.1
                                          have p1457_2 := h1457c.2.2.1
                                          have p1457_3 := h1457c.2.2.2
                                          linarith only [h1240, h1421, h1444, h1453, hlam, p1457_2]
                                        · have p1457_0 := h1457c.1
                                          have p1457_1 := h1457c.2.1
                                          have p1457_2 := h1457c.2.2.1
                                          have p1457_3 := h1457c.2.2.2
                                          linarith only [h1240, h1421, h1444, hlam, p1457_2]
                                        · have p1457_0 := h1457c.1
                                          have p1457_1 := h1457c.2.1
                                          have p1457_2 := h1457c.2.2.1
                                          have p1457_3 := h1457c.2.2.2
                                          linarith only [h1421, h1444, h1451, h1453, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1457_1]
                                        · have p1457_0 := h1457c.1
                                          have p1457_1 := h1457c.2.1
                                          have p1457_2 := h1457c.2.2.1
                                          have p1457_3 := h1457c.2.2.2
                                          linarith only [h1444, hlam, p1457_0]
                                        · have p1457_0 := h1457c.1
                                          have p1457_1 := h1457c.2.1
                                          have p1457_2 := h1457c.2.2.1
                                          have p1457_3 := h1457c.2.2.2
                                          linarith only [hlam, p1457_0]
                                        · have p1457_0 := h1457c.1
                                          have p1457_1 := h1457c.2.1
                                          have p1457_2 := h1457c.2.2.1
                                          have p1457_3 := h1457c.2.2.2
                                          rcases p1457_3 (m.d 0 2) (by simp) with h1477 | h1477
                                          · linarith only [h1240, h1477, hlam]
                                          · linarith only [h1420, h1477, hlam]
                                        · have p1457_0 := h1457c.1
                                          have p1457_1 := h1457c.2.1
                                          have p1457_2 := h1457c.2.2.1
                                          have p1457_3 := h1457c.2.2.2
                                          rcases p1457_3 (m.d 0 2) (by simp) with h1480 | h1480
                                          · linarith only [h1240, h1480, hlam]
                                          · linarith only [h1421, h1480, hlam]
                                        · have p1457_0 := h1457c.1
                                          have p1457_1 := h1457c.2.1
                                          have p1457_2 := h1457c.2.2.1
                                          have p1457_3 := h1457c.2.2.2
                                          linarith only [h1420, hlam, p1457_0]
                                        · have p1457_0 := h1457c.1
                                          have p1457_1 := h1457c.2.1
                                          have p1457_2 := h1457c.2.2.1
                                          have p1457_3 := h1457c.2.2.2
                                          linarith only [h1445, hlam, p1457_0]
                                        · have p1457_0 := h1457c.1
                                          have p1457_1 := h1457c.2.1
                                          have p1457_2 := h1457c.2.2.1
                                          have p1457_3 := h1457c.2.2.2
                                          linarith only [h1451, hlam, p1457_1]
                                        · have p1457_0 := h1457c.1
                                          have p1457_1 := h1457c.2.1
                                          have p1457_2 := h1457c.2.2.1
                                          have p1457_3 := h1457c.2.2.2
                                          linarith only [hlam, p1457_0]
                                        · have p1457_0 := h1457c.1
                                          have p1457_1 := h1457c.2.1
                                          have p1457_2 := h1457c.2.2.1
                                          have p1457_3 := h1457c.2.2.2
                                          linarith only [h1453, hlam, p1457_1]
                                        · have p1457_0 := h1457c.1
                                          have p1457_1 := h1457c.2.1
                                          have p1457_2 := h1457c.2.2.1
                                          have p1457_3 := h1457c.2.2.2
                                          linarith only [h1421, hlam, p1457_0]
                                        · have p1457_0 := h1457c.1
                                          have p1457_1 := h1457c.2.1
                                          have p1457_2 := h1457c.2.2.1
                                          have p1457_3 := h1457c.2.2.2
                                          linarith only [h1446, hlam, p1457_0]
                                        · have p1457_0 := h1457c.1
                                          have p1457_1 := h1457c.2.1
                                          have p1457_2 := h1457c.2.2.1
                                          have p1457_3 := h1457c.2.2.2
                                          linarith only [h1452, hlam, p1457_1]
                                        · have p1457_0 := h1457c.1
                                          have p1457_1 := h1457c.2.1
                                          have p1457_2 := h1457c.2.2.1
                                          have p1457_3 := h1457c.2.2.2
                                          linarith only [h1421, h1451, hc34, hlam, hphi, ht0b, ht45, ht5b, p1457_1, u0elo1]
                                        · have p1457_0 := h1457c.1
                                          have p1457_1 := h1457c.2.1
                                          have p1457_2 := h1457c.2.2.1
                                          have p1457_3 := h1457c.2.2.2
                                          linarith only [hlam, p1457_0]
                                  · linarith only [h1240, h1452, hc02, hlam, hphi, ht23, u3elo4]
                                · linarith only [h1240, h1420, h1451, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                            · linarith only [h1423, h1448, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h1240, h1420, h1422, h1444, h1447, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h1240, h1421, h1444, h1446, hc12, hlam, hphi, ht23, u3elo1]
                      · linarith only [h1240, h1420, h1444, h1445, hlam]
                    · linarith only [h0, h1444, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h1240, h1421, h1423, hlam]
              · linarith only [h1240, h1420, h1422, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1502 | h1502
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1503 | h1503
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1504 | h1504
                  · linarith only [h1420, h1421, h1504, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1506 | h1506
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1507 | h1507
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1508 | h1508
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1509 | h1509
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1510 | h1510
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1511 | h1511
                              · linarith only [h1504, h1509, h1511, h797, hc01, hlam, hphi, ht12, ht23, u3elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1513 | h1513
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1514 | h1514
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1515 | h1515
                                    · linarith only [h1420, h1511, h1515, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1517 | h1517
                                      · linarith only [h1511, h1517, h797, hc01, hlam, hphi, ht12, ht23, u3elo3]
                                      · rcases h2bigk with h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c | h1519c
                                        · have p1519_0 := h1519c.1
                                          have p1519_1 := h1519c.2.1
                                          have p1519_2 := h1519c.2.2.1
                                          have p1519_3 := h1519c.2.2.2
                                          linarith only [hlam, p1519_0]
                                        · have p1519_0 := h1519c.1
                                          have p1519_1 := h1519c.2.1
                                          have p1519_2 := h1519c.2.2.1
                                          have p1519_3 := h1519c.2.2.2
                                          linarith only [h0, hlam, p1519_1]
                                        · have p1519_0 := h1519c.1
                                          have p1519_1 := h1519c.2.1
                                          have p1519_2 := h1519c.2.2.1
                                          have p1519_3 := h1519c.2.2.2
                                          linarith only [h1240, hlam, p1519_0]
                                        · have p1519_0 := h1519c.1
                                          have p1519_1 := h1519c.2.1
                                          have p1519_2 := h1519c.2.2.1
                                          have p1519_3 := h1519c.2.2.2
                                          linarith only [h1421, h1508, h1510, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1519_1, u3elo1]
                                        · have p1519_0 := h1519c.1
                                          have p1519_1 := h1519c.2.1
                                          have p1519_2 := h1519c.2.2.1
                                          have p1519_3 := h1519c.2.2.2
                                          linarith only [h1421, hlam, p1519_0]
                                        · have p1519_0 := h1519c.1
                                          have p1519_1 := h1519c.2.1
                                          have p1519_2 := h1519c.2.2.1
                                          have p1519_3 := h1519c.2.2.2
                                          rcases p1519_3 (m.d 0 2) (by simp) with h1525 | h1525
                                          · linarith only [h0, h1525, hlam]
                                          · rcases p1519_3 (m.d 1 2) (by simp) with h1527 | h1527
                                            · rcases p1519_3 (m.d 2 3) (by simp) with h1528 | h1528
                                              · linarith only [h1506, h1528, hlam]
                                              · linarith only [h1240, h1528, hlam]
                                            · linarith only [h0, h1527, hlam]
                                        · have p1519_0 := h1519c.1
                                          have p1519_1 := h1519c.2.1
                                          have p1519_2 := h1519c.2.2.1
                                          have p1519_3 := h1519c.2.2.2
                                          linarith only [hlam, p1519_0]
                                        · have p1519_0 := h1519c.1
                                          have p1519_1 := h1519c.2.1
                                          have p1519_2 := h1519c.2.2.1
                                          have p1519_3 := h1519c.2.2.2
                                          linarith only [h0, h1240, hc01, hc12, hlam, hphi, p1519_1]
                                        · have p1519_0 := h1519c.1
                                          have p1519_1 := h1519c.2.1
                                          have p1519_2 := h1519c.2.2.1
                                          have p1519_3 := h1519c.2.2.2
                                          linarith only [h1240, h1420, h1506, hlam, p1519_2]
                                        · have p1519_0 := h1519c.1
                                          have p1519_1 := h1519c.2.1
                                          have p1519_2 := h1519c.2.2.1
                                          have p1519_3 := h1519c.2.2.2
                                          linarith only [h1420, h1421, h1513, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1519_1]
                                        · have p1519_0 := h1519c.1
                                          have p1519_1 := h1519c.2.1
                                          have p1519_2 := h1519c.2.2.1
                                          have p1519_3 := h1519c.2.2.2
                                          linarith only [h1420, h1513, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1519_1, u3elo2]
                                        · have p1519_0 := h1519c.1
                                          have p1519_1 := h1519c.2.1
                                          have p1519_2 := h1519c.2.2.1
                                          have p1519_3 := h1519c.2.2.2
                                          linarith only [h1506, hlam, p1519_0]
                                        · have p1519_0 := h1519c.1
                                          have p1519_1 := h1519c.2.1
                                          have p1519_2 := h1519c.2.2.1
                                          have p1519_3 := h1519c.2.2.2
                                          linarith only [hlam, p1519_0]
                                        · have p1519_0 := h1519c.1
                                          have p1519_1 := h1519c.2.1
                                          have p1519_2 := h1519c.2.2.1
                                          have p1519_3 := h1519c.2.2.2
                                          rcases p1519_3 (m.d 0 2) (by simp) with h1539 | h1539
                                          · linarith only [h1240, h1539, hlam]
                                          · linarith only [h1420, h1539, hlam]
                                        · have p1519_0 := h1519c.1
                                          have p1519_1 := h1519c.2.1
                                          have p1519_2 := h1519c.2.2.1
                                          have p1519_3 := h1519c.2.2.2
                                          linarith only [h1420, h1421, h1506, h1513, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1519_1, u3elo1]
                                        · have p1519_0 := h1519c.1
                                          have p1519_1 := h1519c.2.1
                                          have p1519_2 := h1519c.2.2.1
                                          have p1519_3 := h1519c.2.2.2
                                          linarith only [h1420, hlam, p1519_0]
                                        · have p1519_0 := h1519c.1
                                          have p1519_1 := h1519c.2.1
                                          have p1519_2 := h1519c.2.2.1
                                          have p1519_3 := h1519c.2.2.2
                                          linarith only [h1507, hlam, p1519_0]
                                        · have p1519_0 := h1519c.1
                                          have p1519_1 := h1519c.2.1
                                          have p1519_2 := h1519c.2.2.1
                                          have p1519_3 := h1519c.2.2.2
                                          linarith only [h1513, hlam, p1519_1]
                                        · have p1519_0 := h1519c.1
                                          have p1519_1 := h1519c.2.1
                                          have p1519_2 := h1519c.2.2.1
                                          have p1519_3 := h1519c.2.2.2
                                          linarith only [hlam, p1519_0]
                                        · have p1519_0 := h1519c.1
                                          have p1519_1 := h1519c.2.1
                                          have p1519_2 := h1519c.2.2.1
                                          have p1519_3 := h1519c.2.2.2
                                          linarith only [h1515, hlam, p1519_1]
                                        · have p1519_0 := h1519c.1
                                          have p1519_1 := h1519c.2.1
                                          have p1519_2 := h1519c.2.2.1
                                          have p1519_3 := h1519c.2.2.2
                                          linarith only [h1420, h1508, h1513, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1519_1]
                                        · have p1519_0 := h1519c.1
                                          have p1519_1 := h1519c.2.1
                                          have p1519_2 := h1519c.2.2.1
                                          have p1519_3 := h1519c.2.2.2
                                          linarith only [h1508, hlam, p1519_0]
                                        · have p1519_0 := h1519c.1
                                          have p1519_1 := h1519c.2.1
                                          have p1519_2 := h1519c.2.2.1
                                          have p1519_3 := h1519c.2.2.2
                                          linarith only [h1514, hlam, p1519_1]
                                        · have p1519_0 := h1519c.1
                                          have p1519_1 := h1519c.2.1
                                          have p1519_2 := h1519c.2.2.1
                                          have p1519_3 := h1519c.2.2.2
                                          rcases p1519_3 (m.d 0 2) (by simp) with h1551 | h1551
                                          · linarith only [h1421, h1551, hlam]
                                          · linarith only [h1420, h1551, hlam]
                                        · have p1519_0 := h1519c.1
                                          have p1519_1 := h1519c.2.1
                                          have p1519_2 := h1519c.2.2.1
                                          have p1519_3 := h1519c.2.2.2
                                          linarith only [hlam, p1519_0]
                                  · linarith only [h1240, h1420, h1513, h1514, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                                · linarith only [h1240, h1513, hc02, hlam, hphi, ht23, u3elo3]
                            · linarith only [h1503, h1510, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h1240, h1420, h1502, h1506, h1509, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h1240, h1420, h1506, h1508, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h1240, h1420, h1506, h1507, hlam]
                    · linarith only [h0, h1506, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1562 | h1562
                  · linarith only [h1240, h1420, h1503, h1562, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1564 | h1564
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1565 | h1565
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1566 | h1566
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1567 | h1567
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1568 | h1568
                            · linarith only [h1240, h1503, h1568, hc02, hlam, hphi, ht23, u3elo1]
                            · linarith only [h1568, h394, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h1240, h1420, h1564, h1567, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h1240, h1420, h1564, h1566, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h1240, h1420, h1564, h1565, hlam]
                    · linarith only [h0, h1564, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · linarith only [h1240, h1420, h1502, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1576 | h1576
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1577 | h1577
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1578 | h1578
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1579 | h1579
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1580 | h1580
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1581 | h1581
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1582 | h1582
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1583 | h1583
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1584 | h1584
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1585 | h1585
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1586 | h1586
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1587 | h1587
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1588 | h1588
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1589 | h1589
                                      · linarith only [h1577, h1589, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                                      · linarith only [h1579, h1589, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                                    · linarith only [h1420, h1576, h1577, h1579, h1587, h1588, hc35, hlam, hphi, ht0b, ht5b, u0elo2]
                                  · linarith only [h1240, h1587, hc02, hlam, hphi, ht23, u3elo4]
                                · linarith only [h1240, h1576, h1586, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                              · linarith only [h1420, h1576, h1577, h1579, h1581, h1585, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                            · linarith only [h1578, h1584, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h1240, h1576, h1577, h1580, h1583, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                        · linarith only [h1240, h1576, h1580, h1582, hlam]
                      · linarith only [h1240, h1576, h1580, h1581, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h0, h1580, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h1420, h1576, h1579, hlam]
                · linarith only [h1240, h1576, h1578, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1603 | h1603
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1604 | h1604
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1605 | h1605
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1606 | h1606
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1607 | h1607
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1608 | h1608
                          · linarith only [h1240, h1577, h1608, hc02, hlam, hphi, ht23, u3elo1]
                          · linarith only [h1608, h394, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h1240, h1576, h1605, h1607, hlam]
                      · linarith only [h1240, h1576, h1605, h1606, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h0, h1605, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h1240, h1576, h1577, h1604, hlam]
                · linarith only [h1240, h1576, h1603, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1616 | h1616
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1617 | h1617
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1618 | h1618
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1619 | h1619
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1620 | h1620
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1621 | h1621
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1622 | h1622
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1623 | h1623
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1624 | h1624
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1625 | h1625
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1626 | h1626
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1627 | h1627
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1628 | h1628
                                      · linarith only [h1616, h1628, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                                      · linarith only [h1618, h1628, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                                    · linarith only [h1616, h1618, h1627, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                  · linarith only [h1617, h1626, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                                · linarith only [h0, h1240, h1625, hc01, hlam, hphi, ht12, ht23, u3elo3]
                              · linarith only [h1616, h1618, h1624, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · linarith only [h0, h1420, h1617, h1620, h1622, h1623, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h1240, h1616, h1619, h1622, hlam]
                        · linarith only [h0, h1240, h1619, h1621, hc01, hc25, hlam, hphi, ht12]
                      · linarith only [h0, h1240, h1619, h1620, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h1619, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1640 | h1640
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1641 | h1641
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1642 | h1642
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1643 | h1643
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1644 | h1644
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1645 | h1645
                              · linarith only [h0, h1420, h1618, h1643, h1645, hc01, hlam, hphi, ht12, ht23, u3elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1647 | h1647
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1648 | h1648
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1649 | h1649
                                    · linarith only [h1645, h1649, h797, hc01, hc24, hlam, hphi, ht12]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1651 | h1651
                                      · linarith only [h0, h1420, h1616, h1641, h1645, h1651, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                                      · rcases h2bigk with h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c
                                        · have p1653_0 := h1653c.1
                                          have p1653_1 := h1653c.2.1
                                          have p1653_2 := h1653c.2.2.1
                                          have p1653_3 := h1653c.2.2.2
                                          linarith only [hlam, p1653_0]
                                        · have p1653_0 := h1653c.1
                                          have p1653_1 := h1653c.2.1
                                          have p1653_2 := h1653c.2.2.1
                                          have p1653_3 := h1653c.2.2.2
                                          linarith only [h0, hlam, p1653_1]
                                        · have p1653_0 := h1653c.1
                                          have p1653_1 := h1653c.2.1
                                          have p1653_2 := h1653c.2.2.1
                                          have p1653_3 := h1653c.2.2.2
                                          linarith only [h1240, hlam, p1653_0]
                                        · have p1653_0 := h1653c.1
                                          have p1653_1 := h1653c.2.1
                                          have p1653_2 := h1653c.2.2.1
                                          have p1653_3 := h1653c.2.2.2
                                          linarith only [h1420, hlam, p1653_0]
                                        · have p1653_0 := h1653c.1
                                          have p1653_1 := h1653c.2.1
                                          have p1653_2 := h1653c.2.2.1
                                          have p1653_3 := h1653c.2.2.2
                                          linarith only [h1576, hlam, p1653_0]
                                        · have p1653_0 := h1653c.1
                                          have p1653_1 := h1653c.2.1
                                          have p1653_2 := h1653c.2.2.1
                                          have p1653_3 := h1653c.2.2.2
                                          rcases p1653_3 (m.d 0 2) (by simp) with h1659 | h1659
                                          · linarith only [h0, h1659, hlam]
                                          · rcases p1653_3 (m.d 1 2) (by simp) with h1661 | h1661
                                            · rcases p1653_3 (m.d 2 3) (by simp) with h1662 | h1662
                                              · linarith only [h1640, h1662, hlam]
                                              · linarith only [h1240, h1662, hlam]
                                            · linarith only [h0, h1661, hlam]
                                        · have p1653_0 := h1653c.1
                                          have p1653_1 := h1653c.2.1
                                          have p1653_2 := h1653c.2.2.1
                                          have p1653_3 := h1653c.2.2.2
                                          linarith only [hlam, p1653_0]
                                        · have p1653_0 := h1653c.1
                                          have p1653_1 := h1653c.2.1
                                          have p1653_2 := h1653c.2.2.1
                                          have p1653_3 := h1653c.2.2.2
                                          linarith only [h0, h1240, hc01, hc12, hlam, hphi, p1653_1]
                                        · have p1653_0 := h1653c.1
                                          have p1653_1 := h1653c.2.1
                                          have p1653_2 := h1653c.2.2.1
                                          have p1653_3 := h1653c.2.2.2
                                          linarith only [h0, h1420, hc01, hc12, hlam, hphi, p1653_1]
                                        · have p1653_0 := h1653c.1
                                          have p1653_1 := h1653c.2.1
                                          have p1653_2 := h1653c.2.2.1
                                          have p1653_3 := h1653c.2.2.2
                                          linarith only [h0, h1576, hc01, hc12, hlam, hphi, p1653_1]
                                        · have p1653_0 := h1653c.1
                                          have p1653_1 := h1653c.2.1
                                          have p1653_2 := h1653c.2.2.1
                                          have p1653_3 := h1653c.2.2.2
                                          linarith only [h0, hc01, hlam, hphi, ht12, ht23, p1653_1, u3elo2]
                                        · have p1653_0 := h1653c.1
                                          have p1653_1 := h1653c.2.1
                                          have p1653_2 := h1653c.2.2.1
                                          have p1653_3 := h1653c.2.2.2
                                          linarith only [h1640, hlam, p1653_0]
                                        · have p1653_0 := h1653c.1
                                          have p1653_1 := h1653c.2.1
                                          have p1653_2 := h1653c.2.2.1
                                          have p1653_3 := h1653c.2.2.2
                                          linarith only [hlam, p1653_0]
                                        · have p1653_0 := h1653c.1
                                          have p1653_1 := h1653c.2.1
                                          have p1653_2 := h1653c.2.2.1
                                          have p1653_3 := h1653c.2.2.2
                                          linarith only [h0, h1420, h1640, hc01, hc13, hlam, hphi, p1653_1]
                                        · have p1653_0 := h1653c.1
                                          have p1653_1 := h1653c.2.1
                                          have p1653_2 := h1653c.2.2.1
                                          have p1653_3 := h1653c.2.2.2
                                          linarith only [h0, h1576, h1640, hc01, hlam, hphi, ht12, ht23, p1653_1, u3elo1]
                                        · have p1653_0 := h1653c.1
                                          have p1653_1 := h1653c.2.1
                                          have p1653_2 := h1653c.2.2.1
                                          have p1653_3 := h1653c.2.2.2
                                          linarith only [h0, h1641, h1645, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1653_1]
                                        · have p1653_0 := h1653c.1
                                          have p1653_1 := h1653c.2.1
                                          have p1653_2 := h1653c.2.2.1
                                          have p1653_3 := h1653c.2.2.2
                                          linarith only [h1641, hlam, p1653_0]
                                        · have p1653_0 := h1653c.1
                                          have p1653_1 := h1653c.2.1
                                          have p1653_2 := h1653c.2.2.1
                                          have p1653_3 := h1653c.2.2.2
                                          linarith only [h1647, hlam, p1653_1]
                                        · have p1653_0 := h1653c.1
                                          have p1653_1 := h1653c.2.1
                                          have p1653_2 := h1653c.2.2.1
                                          have p1653_3 := h1653c.2.2.2
                                          linarith only [hlam, p1653_0]
                                        · have p1653_0 := h1653c.1
                                          have p1653_1 := h1653c.2.1
                                          have p1653_2 := h1653c.2.2.1
                                          have p1653_3 := h1653c.2.2.2
                                          linarith only [h1649, hlam, p1653_1]
                                        · have p1653_0 := h1653c.1
                                          have p1653_1 := h1653c.2.1
                                          have p1653_2 := h1653c.2.2.1
                                          have p1653_3 := h1653c.2.2.2
                                          linarith only [h0, h1642, hc01, hc12, hlam, hphi, p1653_1]
                                        · have p1653_0 := h1653c.1
                                          have p1653_1 := h1653c.2.1
                                          have p1653_2 := h1653c.2.2.1
                                          have p1653_3 := h1653c.2.2.2
                                          linarith only [h1642, hlam, p1653_0]
                                        · have p1653_0 := h1653c.1
                                          have p1653_1 := h1653c.2.1
                                          have p1653_2 := h1653c.2.2.1
                                          have p1653_3 := h1653c.2.2.2
                                          linarith only [h1648, hlam, p1653_1]
                                        · have p1653_0 := h1653c.1
                                          have p1653_1 := h1653c.2.1
                                          have p1653_2 := h1653c.2.2.1
                                          have p1653_3 := h1653c.2.2.2
                                          linarith only [h0, h1420, h1642, h1644, hc01, hlam, hphi, ht12, ht23, p1653_1, u3elo1]
                                        · have p1653_0 := h1653c.1
                                          have p1653_1 := h1653c.2.1
                                          have p1653_2 := h1653c.2.2.1
                                          have p1653_3 := h1653c.2.2.2
                                          linarith only [hlam, p1653_0]
                                  · linarith only [h0, h1240, h1648, hc01, hlam, hphi, ht12, ht23, u3elo4]
                                · linarith only [h0, h1240, h1647, hc01, hlam, hphi, ht12, ht23, u3elo3]
                            · linarith only [h1617, h1644, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h1643, h394, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h1240, h1640, h1642, hc01, hc25, hlam, hphi, ht12]
                      · linarith only [h0, h1240, h1640, h1641, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h1640, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1692 | h1692
                  · linarith only [h1616, h1617, h1692, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1694 | h1694
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1695 | h1695
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1696 | h1696
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1697 | h1697
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1698 | h1698
                            · linarith only [h1617, h1698, hc03, hlam, hphi, u3elo1]
                            · linarith only [h1698, h394, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h0, h1240, h1616, h1694, h1697, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h1240, h1694, h1696, hc01, hc25, hlam, hphi, ht12]
                      · linarith only [h0, h1240, h1694, h1695, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h1694, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1705 | h1705
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1706 | h1706
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1707 | h1707
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1708 | h1708
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1709 | h1709
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1710 | h1710
                          · linarith only [h1616, h1710, hc03, hlam, hphi, u3elo1]
                          · linarith only [h1710, h394, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h1240, h1707, h1709, hc01, hc25, hlam, hphi, ht12]
                      · linarith only [h0, h1240, h1707, h1708, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h1707, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h1616, h1705, h1706, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1717 | h1717
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1718 | h1718
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1719 | h1719
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1720 | h1720
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1721 | h1721
                          · linarith only [h0, h1240, h1616, h1721, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h1721, h394, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h1240, h1718, h1720, hc01, hc25, hlam, hphi, ht12]
                      · linarith only [h0, h1240, h1718, h1719, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h1718, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1727 | h1727
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1728 | h1728
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1729 | h1729
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1730 | h1730
                          · linarith only [h0, h1240, h1616, h1730, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h1730, h394, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h1240, h1727, h1729, hc01, hc25, hlam, hphi, ht12]
                      · linarith only [h0, h1240, h1727, h1728, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h1727, hc01, hlam, hphi, ht12, ht23, u3elo2]

set_option maxHeartbeats 3472000 in
set_option maxHeartbeats 3472000 in
theorem r1l7_20_12_13_15_H_L_L_I_L_0_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_13_15_H_L_L_I_L_0_L_I_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_20_12_13_15_H_L_L_I_L_0_L_I_x1 m hb0 hb2 hb3 hb5 h0

end R2N4
