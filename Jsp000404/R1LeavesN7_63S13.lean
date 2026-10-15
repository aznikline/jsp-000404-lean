import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_63S12

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_13_15_M_LI_L_I_L_0_L_0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h423 | h423
  · rcases m.htr 0 1 4 (by decide) (by decide) with h424 | h424
    · rcases m.htr 0 1 5 (by decide) (by decide) with h425 | h425
      · rcases m.htr 0 2 3 (by decide) (by decide) with h426 | h426
        · rcases m.htr 0 2 4 (by decide) (by decide) with h427 | h427
          · rcases m.htr 0 2 5 (by decide) (by decide) with h428 | h428
            · rcases m.htr 0 3 4 (by decide) (by decide) with h429 | h429
              · rcases m.htr 0 3 5 (by decide) (by decide) with h430 | h430
                · rcases m.htr 0 4 5 (by decide) (by decide) with h431 | h431
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h432 | h432
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h433 | h433
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h434 | h434
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h435 | h435
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h436 | h436
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h437 | h437
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h438 | h438
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h439 | h439
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h440 | h440
                                    · linarith only [h423, h432, h437, h440, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                    · linarith only [h0, h423, h435, h436, h440, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                  · linarith only [h0, h423, h435, h436, h439, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · linarith only [h430, h438, hc23, hlam, hphi, u3elo0]
                              · linarith only [h429, h437, hc23, hlam, hphi, u3elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h446 | h446
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h447 | h447
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h448 | h448
                                  · linarith only [h433, h436, h448, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h450 | h450
                                    · linarith only [h433, h436, h446, h450, hlam]
                                    · rcases h0bigk with h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c
                                      · have p452_0 := h452c.1
                                        have p452_1 := h452c.2.1
                                        have p452_2 := h452c.2.2.1
                                        have p452_3 := h452c.2.2.2
                                        linarith only [hlam, p452_0]
                                      · have p452_0 := h452c.1
                                        have p452_1 := h452c.2.1
                                        have p452_2 := h452c.2.2.1
                                        have p452_3 := h452c.2.2.2
                                        linarith only [h0, hlam, p452_1]
                                      · have p452_0 := h452c.1
                                        have p452_1 := h452c.2.1
                                        have p452_2 := h452c.2.2.1
                                        have p452_3 := h452c.2.2.2
                                        linarith only [h0, h429, h431, h433, h436, h446, hc34, hlam, hphi, ht0b, ht45, ht5b, p452_1, u0elo1]
                                      · have p452_0 := h452c.1
                                        have p452_1 := h452c.2.1
                                        have p452_2 := h452c.2.2.1
                                        have p452_3 := h452c.2.2.2
                                        linarith only [h0, h431, h433, h436, h446, hc34, hlam, hphi, ht0b, ht45, ht5b, p452_1, u0elo1]
                                      · have p452_0 := h452c.1
                                        have p452_1 := h452c.2.1
                                        have p452_2 := h452c.2.2.1
                                        have p452_3 := h452c.2.2.2
                                        linarith only [h0, h431, h433, h436, h446, hc34, hlam, hphi, ht0b, ht45, ht5b, p452_1, u0elo1]
                                      · have p452_0 := h452c.1
                                        have p452_1 := h452c.2.1
                                        have p452_2 := h452c.2.2.1
                                        have p452_3 := h452c.2.2.2
                                        linarith only [h423, h429, h431, h433, h436, h446, hc13, hc34, hlam, hphi, ht0b, ht45, ht5b, p452_1, u0elo1, u3elo0]
                                      · have p452_0 := h452c.1
                                        have p452_1 := h452c.2.1
                                        have p452_2 := h452c.2.2.1
                                        have p452_3 := h452c.2.2.2
                                        linarith only [hlam, p452_0]
                                      · have p452_0 := h452c.1
                                        have p452_1 := h452c.2.1
                                        have p452_2 := h452c.2.2.1
                                        have p452_3 := h452c.2.2.2
                                        linarith only [h429, h431, h433, h436, h446, hc34, hlam, hphi, ht0b, ht45, ht5b, p452_1, u0elo1]
                                      · have p452_0 := h452c.1
                                        have p452_1 := h452c.2.1
                                        have p452_2 := h452c.2.2.1
                                        have p452_3 := h452c.2.2.2
                                        linarith only [h431, h433, h436, h446, hc34, hlam, hphi, ht0b, ht45, ht5b, p452_1, u0elo1]
                                      · have p452_0 := h452c.1
                                        have p452_1 := h452c.2.1
                                        have p452_2 := h452c.2.2.1
                                        have p452_3 := h452c.2.2.2
                                        linarith only [h431, h433, h436, h446, hc34, hlam, hphi, ht0b, ht45, ht5b, p452_1, u0elo1]
                                      · have p452_0 := h452c.1
                                        have p452_1 := h452c.2.1
                                        have p452_2 := h452c.2.2.1
                                        have p452_3 := h452c.2.2.2
                                        linarith only [h423, hlam, p452_1]
                                      · have p452_0 := h452c.1
                                        have p452_1 := h452c.2.1
                                        have p452_2 := h452c.2.2.1
                                        have p452_3 := h452c.2.2.2
                                        linarith only [h426, hlam, p452_1]
                                      · have p452_0 := h452c.1
                                        have p452_1 := h452c.2.1
                                        have p452_2 := h452c.2.2.1
                                        have p452_3 := h452c.2.2.2
                                        linarith only [hlam, p452_0]
                                      · have p452_0 := h452c.1
                                        have p452_1 := h452c.2.1
                                        have p452_2 := h452c.2.2.1
                                        have p452_3 := h452c.2.2.2
                                        linarith only [h431, h433, h436, h446, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p452_1, u3elo0]
                                      · have p452_0 := h452c.1
                                        have p452_1 := h452c.2.1
                                        have p452_2 := h452c.2.2.1
                                        have p452_3 := h452c.2.2.2
                                        linarith only [h431, h433, h436, h446, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p452_1, u3elo0]
                                      · have p452_0 := h452c.1
                                        have p452_1 := h452c.2.1
                                        have p452_2 := h452c.2.2.1
                                        have p452_3 := h452c.2.2.2
                                        linarith only [h424, hlam, p452_0]
                                      · have p452_0 := h452c.1
                                        have p452_1 := h452c.2.1
                                        have p452_2 := h452c.2.2.1
                                        have p452_3 := h452c.2.2.2
                                        linarith only [h427, hlam, p452_0]
                                      · have p452_0 := h452c.1
                                        have p452_1 := h452c.2.1
                                        have p452_2 := h452c.2.2.1
                                        have p452_3 := h452c.2.2.2
                                        linarith only [h429, hlam, p452_0]
                                      · have p452_0 := h452c.1
                                        have p452_1 := h452c.2.1
                                        have p452_2 := h452c.2.2.1
                                        have p452_3 := h452c.2.2.2
                                        linarith only [hlam, p452_0]
                                      · have p452_0 := h452c.1
                                        have p452_1 := h452c.2.1
                                        have p452_2 := h452c.2.2.1
                                        have p452_3 := h452c.2.2.2
                                        linarith only [h431, h433, h436, h446, hc34, hlam, hphi, ht0b, ht45, ht5b, p452_1, u0elo3]
                                      · have p452_0 := h452c.1
                                        have p452_1 := h452c.2.1
                                        have p452_2 := h452c.2.2.1
                                        have p452_3 := h452c.2.2.2
                                        linarith only [h425, hlam, p452_0]
                                      · have p452_0 := h452c.1
                                        have p452_1 := h452c.2.1
                                        have p452_2 := h452c.2.2.1
                                        have p452_3 := h452c.2.2.2
                                        linarith only [h428, hlam, p452_1]
                                      · have p452_0 := h452c.1
                                        have p452_1 := h452c.2.1
                                        have p452_2 := h452c.2.2.1
                                        have p452_3 := h452c.2.2.2
                                        linarith only [h430, hlam, p452_0]
                                      · have p452_0 := h452c.1
                                        have p452_1 := h452c.2.1
                                        have p452_2 := h452c.2.2.1
                                        have p452_3 := h452c.2.2.2
                                        linarith only [h431, hlam, p452_1]
                                      · have p452_0 := h452c.1
                                        have p452_1 := h452c.2.1
                                        have p452_2 := h452c.2.2.1
                                        have p452_3 := h452c.2.2.2
                                        linarith only [hlam, p452_0]
                                · linarith only [h430, h447, hc23, hlam, hphi, u3elo0]
                              · linarith only [h435, h446, hc23, hlam, hphi, u3elo1]
                          · linarith only [h429, h435, hc13, hlam, hphi, u3elo0]
                        · linarith only [h0, h434, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h427, h433, hlam]
                    · linarith only [h0, h432, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h484 | h484
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h485 | h485
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h486 | h486
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h487 | h487
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h488 | h488
                            · linarith only [h424, h431, h488, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h490 | h490
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h491 | h491
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h492 | h492
                                  · linarith only [h424, h431, h485, h492, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h494 | h494
                                    · linarith only [h429, h431, h494, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                                    · rcases h0bigk with h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c
                                      · have p496_0 := h496c.1
                                        have p496_1 := h496c.2.1
                                        have p496_2 := h496c.2.2.1
                                        have p496_3 := h496c.2.2.2
                                        linarith only [hlam, p496_0]
                                      · have p496_0 := h496c.1
                                        have p496_1 := h496c.2.1
                                        have p496_2 := h496c.2.2.1
                                        have p496_3 := h496c.2.2.2
                                        linarith only [h0, hlam, p496_1]
                                      · have p496_0 := h496c.1
                                        have p496_1 := h496c.2.1
                                        have p496_2 := h496c.2.2.1
                                        have p496_3 := h496c.2.2.2
                                        linarith only [h0, h423, h484, h491, h494, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p496_1]
                                      · have p496_0 := h496c.1
                                        have p496_1 := h496c.2.1
                                        have p496_2 := h496c.2.2.1
                                        have p496_3 := h496c.2.2.2
                                        rcases p496_3 (m.d 0 1) (by simp) with h500 | h500
                                        · rcases p496_3 (m.d 0 2) (by simp) with h501 | h501
                                          · rcases p496_3 (m.d 0 3) (by simp) with h502 | h502
                                            · linarith only [h423, h502, hlam]
                                            · linarith only [h429, h502, hlam]
                                          · linarith only [h427, h501, hlam]
                                        · linarith only [h424, h500, hlam]
                                      · have p496_0 := h496c.1
                                        have p496_1 := h496c.2.1
                                        have p496_2 := h496c.2.2.1
                                        have p496_3 := h496c.2.2.2
                                        rcases p496_3 (m.d 0 1) (by simp) with h507 | h507
                                        · rcases p496_3 (m.d 0 2) (by simp) with h508 | h508
                                          · rcases p496_3 (m.d 0 3) (by simp) with h509 | h509
                                            · linarith only [h423, h509, hlam]
                                            · linarith only [h430, h509, hlam]
                                          · linarith only [h428, h508, hlam]
                                        · linarith only [h425, h507, hlam]
                                      · have p496_0 := h496c.1
                                        have p496_1 := h496c.2.1
                                        have p496_2 := h496c.2.2.1
                                        have p496_3 := h496c.2.2.2
                                        linarith only [h423, h484, h491, h494, hc34, hlam, hphi, ht0b, ht45, ht5b, p496_1, u0elo1]
                                      · have p496_0 := h496c.1
                                        have p496_1 := h496c.2.1
                                        have p496_2 := h496c.2.2.1
                                        have p496_3 := h496c.2.2.2
                                        linarith only [hlam, p496_0]
                                      · have p496_0 := h496c.1
                                        have p496_1 := h496c.2.1
                                        have p496_2 := h496c.2.2.1
                                        have p496_3 := h496c.2.2.2
                                        linarith only [h423, h484, h491, h494, hc34, hlam, hphi, ht0b, ht45, ht5b, p496_1, u0elo1]
                                      · have p496_0 := h496c.1
                                        have p496_1 := h496c.2.1
                                        have p496_2 := h496c.2.2.1
                                        have p496_3 := h496c.2.2.2
                                        rcases p496_3 (m.d 0 1) (by simp) with h517 | h517
                                        · linarith only [h0, h517, hlam]
                                        · linarith only [h424, h517, hlam]
                                      · have p496_0 := h496c.1
                                        have p496_1 := h496c.2.1
                                        have p496_2 := h496c.2.2.1
                                        have p496_3 := h496c.2.2.2
                                        rcases p496_3 (m.d 0 1) (by simp) with h520 | h520
                                        · linarith only [h0, h520, hlam]
                                        · linarith only [h425, h520, hlam]
                                      · have p496_0 := h496c.1
                                        have p496_1 := h496c.2.1
                                        have p496_2 := h496c.2.2.1
                                        have p496_3 := h496c.2.2.2
                                        linarith only [h423, hlam, p496_1]
                                      · have p496_0 := h496c.1
                                        have p496_1 := h496c.2.1
                                        have p496_2 := h496c.2.2.1
                                        have p496_3 := h496c.2.2.2
                                        linarith only [h426, hlam, p496_1]
                                      · have p496_0 := h496c.1
                                        have p496_1 := h496c.2.1
                                        have p496_2 := h496c.2.2.1
                                        have p496_3 := h496c.2.2.2
                                        linarith only [hlam, p496_0]
                                      · have p496_0 := h496c.1
                                        have p496_1 := h496c.2.1
                                        have p496_2 := h496c.2.2.1
                                        have p496_3 := h496c.2.2.2
                                        rcases p496_3 (m.d 0 1) (by simp) with h526 | h526
                                        · rcases p496_3 (m.d 0 2) (by simp) with h527 | h527
                                          · rcases p496_3 (m.d 0 3) (by simp) with h528 | h528
                                            · rcases p496_3 (m.d 0 4) (by simp) with h529 | h529
                                              · linarith only [h429, h529, hlam]
                                              · rcases p496_3 (m.d 0 5) (by simp) with h531 | h531
                                                · linarith only [h430, h531, hlam]
                                                · linarith only [h431, h531, hlam]
                                            · linarith only [h429, h528, hlam]
                                          · linarith only [h427, h527, hlam]
                                        · linarith only [h424, h526, hlam]
                                      · have p496_0 := h496c.1
                                        have p496_1 := h496c.2.1
                                        have p496_2 := h496c.2.2.1
                                        have p496_3 := h496c.2.2.2
                                        rcases p496_3 (m.d 0 1) (by simp) with h537 | h537
                                        · rcases p496_3 (m.d 0 2) (by simp) with h538 | h538
                                          · rcases p496_3 (m.d 0 3) (by simp) with h539 | h539
                                            · rcases p496_3 (m.d 0 4) (by simp) with h540 | h540
                                              · linarith only [h429, h540, hlam]
                                              · rcases p496_3 (m.d 0 5) (by simp) with h542 | h542
                                                · linarith only [h430, h542, hlam]
                                                · rcases h2bigk with h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c
                                                  · have p544_0 := h544c.1
                                                    have p544_1 := h544c.2.1
                                                    have p544_2 := h544c.2.2.1
                                                    have p544_3 := h544c.2.2.2
                                                    linarith only [hlam, p544_0]
                                                  · have p544_0 := h544c.1
                                                    have p544_1 := h544c.2.1
                                                    have p544_2 := h544c.2.2.1
                                                    have p544_3 := h544c.2.2.2
                                                    linarith only [h0, hlam, p544_1]
                                                  · have p544_0 := h544c.1
                                                    have p544_1 := h544c.2.1
                                                    have p544_2 := h544c.2.2.1
                                                    have p544_3 := h544c.2.2.2
                                                    linarith only [h491, h494, hc34, hlam, hphi, ht0b, ht45, ht5b, p544_1, u0elo1]
                                                  · have p544_0 := h544c.1
                                                    have p544_1 := h544c.2.1
                                                    have p544_2 := h544c.2.2.1
                                                    have p544_3 := h544c.2.2.2
                                                    rcases p544_3 (m.d 0 2) (by simp) with h548 | h548
                                                    · rcases p544_3 (m.d 1 2) (by simp) with h549 | h549
                                                      · rcases p544_3 (m.d 2 3) (by simp) with h550 | h550
                                                        · linarith only [h426, h550, hlam]
                                                        · linarith only [h490, h550, hlam]
                                                      · linarith only [h485, h549, hlam]
                                                    · linarith only [h548, hlam, p544_0]
                                                  · have p544_0 := h544c.1
                                                    have p544_1 := h544c.2.1
                                                    have p544_2 := h544c.2.2.1
                                                    have p544_3 := h544c.2.2.2
                                                    rcases p544_3 (m.d 0 2) (by simp) with h555 | h555
                                                    · rcases p544_3 (m.d 1 2) (by simp) with h556 | h556
                                                      · rcases p544_3 (m.d 2 3) (by simp) with h557 | h557
                                                        · linarith only [h426, h557, hlam]
                                                        · linarith only [h491, h557, hlam]
                                                      · linarith only [h486, h556, hlam]
                                                    · linarith only [h555, hlam, p544_0]
                                                  · have p544_0 := h544c.1
                                                    have p544_1 := h544c.2.1
                                                    have p544_2 := h544c.2.2.1
                                                    have p544_3 := h544c.2.2.2
                                                    linarith only [h0, h423, h424, h431, h485, h490, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p496_1, p544_1]
                                                  · have p544_0 := h544c.1
                                                    have p544_1 := h544c.2.1
                                                    have p544_2 := h544c.2.2.1
                                                    have p544_3 := h544c.2.2.2
                                                    linarith only [hlam, p544_0]
                                                  · have p544_0 := h544c.1
                                                    have p544_1 := h544c.2.1
                                                    have p544_2 := h544c.2.2.1
                                                    have p544_3 := h544c.2.2.2
                                                    rcases p544_3 (m.d 0 2) (by simp) with h564 | h564
                                                    · linarith only [h0, h564, hlam]
                                                    · linarith only [h426, h564, hlam]
                                                  · have p544_0 := h544c.1
                                                    have p544_1 := h544c.2.1
                                                    have p544_2 := h544c.2.2.1
                                                    have p544_3 := h544c.2.2.2
                                                    linarith only [h0, h423, h424, h431, h485, hlam, p496_1, p544_2]
                                                  · have p544_0 := h544c.1
                                                    have p544_1 := h544c.2.1
                                                    have p544_2 := h544c.2.2.1
                                                    have p544_3 := h544c.2.2.2
                                                    linarith only [h0, h423, h425, h486, hlam, p496_1, p544_2]
                                                  · have p544_0 := h544c.1
                                                    have p544_1 := h544c.2.1
                                                    have p544_2 := h544c.2.2.1
                                                    have p544_3 := h544c.2.2.2
                                                    linarith only [h426, hlam, p544_0]
                                                  · have p544_0 := h544c.1
                                                    have p544_1 := h544c.2.1
                                                    have p544_2 := h544c.2.2.1
                                                    have p544_3 := h544c.2.2.2
                                                    linarith only [h484, hlam, p544_0]
                                                  · have p544_0 := h544c.1
                                                    have p544_1 := h544c.2.1
                                                    have p544_2 := h544c.2.2.1
                                                    have p544_3 := h544c.2.2.2
                                                    linarith only [hlam, p544_0]
                                                  · have p544_0 := h544c.1
                                                    have p544_1 := h544c.2.1
                                                    have p544_2 := h544c.2.2.1
                                                    have p544_3 := h544c.2.2.2
                                                    linarith only [h423, h484, h490, hc34, hlam, hphi, ht0b, ht45, ht5b, p544_1, u0elo0]
                                                  · have p544_0 := h544c.1
                                                    have p544_1 := h544c.2.1
                                                    have p544_2 := h544c.2.2.1
                                                    have p544_3 := h544c.2.2.2
                                                    linarith only [h0, h423, h484, hc25, hlam, hphi, ht0b, ht5b, p544_1, u0elo1]
                                                  · have p544_0 := h544c.1
                                                    have p544_1 := h544c.2.1
                                                    have p544_2 := h544c.2.2.1
                                                    have p544_3 := h544c.2.2.2
                                                    linarith only [h427, hlam, p544_0]
                                                  · have p544_0 := h544c.1
                                                    have p544_1 := h544c.2.1
                                                    have p544_2 := h544c.2.2.1
                                                    have p544_3 := h544c.2.2.2
                                                    linarith only [h485, hlam, p544_0]
                                                  · have p544_0 := h544c.1
                                                    have p544_1 := h544c.2.1
                                                    have p544_2 := h544c.2.2.1
                                                    have p544_3 := h544c.2.2.2
                                                    linarith only [h490, hlam, p544_1]
                                                  · have p544_0 := h544c.1
                                                    have p544_1 := h544c.2.1
                                                    have p544_2 := h544c.2.2.1
                                                    have p544_3 := h544c.2.2.2
                                                    linarith only [hlam, p544_0]
                                                  · have p544_0 := h544c.1
                                                    have p544_1 := h544c.2.1
                                                    have p544_2 := h544c.2.2.1
                                                    have p544_3 := h544c.2.2.2
                                                    linarith only [h492, hlam, p544_1]
                                                  · have p544_0 := h544c.1
                                                    have p544_1 := h544c.2.1
                                                    have p544_2 := h544c.2.2.1
                                                    have p544_3 := h544c.2.2.2
                                                    linarith only [h428, hlam, p544_0]
                                                  · have p544_0 := h544c.1
                                                    have p544_1 := h544c.2.1
                                                    have p544_2 := h544c.2.2.1
                                                    have p544_3 := h544c.2.2.2
                                                    linarith only [h486, hlam, p544_0]
                                                  · have p544_0 := h544c.1
                                                    have p544_1 := h544c.2.1
                                                    have p544_2 := h544c.2.2.1
                                                    have p544_3 := h544c.2.2.2
                                                    linarith only [h491, hlam, p544_1]
                                                  · have p544_0 := h544c.1
                                                    have p544_1 := h544c.2.1
                                                    have p544_2 := h544c.2.2.1
                                                    have p544_3 := h544c.2.2.2
                                                    linarith only [h490, hc34, hlam, hphi, ht45, p544_1, u5elo2]
                                                  · have p544_0 := h544c.1
                                                    have p544_1 := h544c.2.1
                                                    have p544_2 := h544c.2.2.1
                                                    have p544_3 := h544c.2.2.2
                                                    linarith only [hlam, p544_0]
                                            · linarith only [h430, h539, hlam]
                                          · linarith only [h428, h538, hlam]
                                        · linarith only [h425, h537, hlam]
                                      · have p496_0 := h496c.1
                                        have p496_1 := h496c.2.1
                                        have p496_2 := h496c.2.2.1
                                        have p496_3 := h496c.2.2.2
                                        linarith only [h424, hlam, p496_0]
                                      · have p496_0 := h496c.1
                                        have p496_1 := h496c.2.1
                                        have p496_2 := h496c.2.2.1
                                        have p496_3 := h496c.2.2.2
                                        linarith only [h427, hlam, p496_0]
                                      · have p496_0 := h496c.1
                                        have p496_1 := h496c.2.1
                                        have p496_2 := h496c.2.2.1
                                        have p496_3 := h496c.2.2.2
                                        linarith only [h429, hlam, p496_0]
                                      · have p496_0 := h496c.1
                                        have p496_1 := h496c.2.1
                                        have p496_2 := h496c.2.2.1
                                        have p496_3 := h496c.2.2.2
                                        linarith only [hlam, p496_0]
                                      · have p496_0 := h496c.1
                                        have p496_1 := h496c.2.1
                                        have p496_2 := h496c.2.2.1
                                        have p496_3 := h496c.2.2.2
                                        linarith only [h431, hlam, p496_0]
                                      · have p496_0 := h496c.1
                                        have p496_1 := h496c.2.1
                                        have p496_2 := h496c.2.2.1
                                        have p496_3 := h496c.2.2.2
                                        linarith only [h425, hlam, p496_0]
                                      · have p496_0 := h496c.1
                                        have p496_1 := h496c.2.1
                                        have p496_2 := h496c.2.2.1
                                        have p496_3 := h496c.2.2.2
                                        linarith only [h428, hlam, p496_1]
                                      · have p496_0 := h496c.1
                                        have p496_1 := h496c.2.1
                                        have p496_2 := h496c.2.2.1
                                        have p496_3 := h496c.2.2.2
                                        linarith only [h430, hlam, p496_0]
                                      · have p496_0 := h496c.1
                                        have p496_1 := h496c.2.1
                                        have p496_2 := h496c.2.2.1
                                        have p496_3 := h496c.2.2.2
                                        linarith only [h424, h485, h490, hc34, hlam, hphi, ht45, p496_1, u5elo0]
                                      · have p496_0 := h496c.1
                                        have p496_1 := h496c.2.1
                                        have p496_2 := h496c.2.2.1
                                        have p496_3 := h496c.2.2.2
                                        linarith only [hlam, p496_0]
                                · linarith only [h430, h491, hc23, hlam, hphi, u3elo0]
                              · linarith only [h429, h490, hc23, hlam, hphi, u3elo0]
                          · linarith only [h429, h487, hc13, hlam, hphi, u3elo0]
                        · linarith only [h0, h486, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h427, h485, hlam]
                    · linarith only [h0, h484, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h429, h430, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h604 | h604
                · rcases m.htr 0 4 5 (by decide) (by decide) with h605 | h605
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h606 | h606
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h607 | h607
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h608 | h608
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h609 | h609
                          · linarith only [h423, h429, h609, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h611 | h611
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h612 | h612
                              · linarith only [h423, h429, h606, h612, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h614 | h614
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h615 | h615
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h616 | h616
                                    · rcases h0bigk with h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c
                                      · have p617_0 := h617c.1
                                        have p617_1 := h617c.2.1
                                        have p617_2 := h617c.2.2.1
                                        have p617_3 := h617c.2.2.2
                                        linarith only [hlam, p617_0]
                                      · have p617_0 := h617c.1
                                        have p617_1 := h617c.2.1
                                        have p617_2 := h617c.2.2.1
                                        have p617_3 := h617c.2.2.2
                                        linarith only [h0, hlam, p617_1]
                                      · have p617_0 := h617c.1
                                        have p617_1 := h617c.2.1
                                        have p617_2 := h617c.2.2.1
                                        have p617_3 := h617c.2.2.2
                                        linarith only [h0, h423, h606, h614, h616, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p617_1]
                                      · have p617_0 := h617c.1
                                        have p617_1 := h617c.2.1
                                        have p617_2 := h617c.2.2.1
                                        have p617_3 := h617c.2.2.2
                                        linarith only [h0, h423, h429, h606, h614, h616, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p617_1]
                                      · have p617_0 := h617c.1
                                        have p617_1 := h617c.2.1
                                        have p617_2 := h617c.2.2.1
                                        have p617_3 := h617c.2.2.2
                                        rcases p617_3 (m.d 0 1) (by simp) with h622 | h622
                                        · rcases p617_3 (m.d 0 2) (by simp) with h623 | h623
                                          · rcases p617_3 (m.d 0 3) (by simp) with h624 | h624
                                            · linarith only [h423, h624, hlam]
                                            · linarith only [h604, h624, hlam]
                                          · linarith only [h428, h623, hlam]
                                        · linarith only [h425, h622, hlam]
                                      · have p617_0 := h617c.1
                                        have p617_1 := h617c.2.1
                                        have p617_2 := h617c.2.2.1
                                        have p617_3 := h617c.2.2.2
                                        linarith only [h423, h606, h614, h616, hc45, hlam, hphi, ht0b, ht5b, p617_1, u0elo1]
                                      · have p617_0 := h617c.1
                                        have p617_1 := h617c.2.1
                                        have p617_2 := h617c.2.2.1
                                        have p617_3 := h617c.2.2.2
                                        linarith only [hlam, p617_0]
                                      · have p617_0 := h617c.1
                                        have p617_1 := h617c.2.1
                                        have p617_2 := h617c.2.2.1
                                        have p617_3 := h617c.2.2.2
                                        linarith only [h423, h606, h614, h616, hc45, hlam, hphi, ht0b, ht5b, p617_1, u0elo1]
                                      · have p617_0 := h617c.1
                                        have p617_1 := h617c.2.1
                                        have p617_2 := h617c.2.2.1
                                        have p617_3 := h617c.2.2.2
                                        linarith only [h423, h429, h606, h614, h616, hc45, hlam, hphi, ht0b, ht5b, p617_1, u0elo1]
                                      · have p617_0 := h617c.1
                                        have p617_1 := h617c.2.1
                                        have p617_2 := h617c.2.2.1
                                        have p617_3 := h617c.2.2.2
                                        rcases p617_3 (m.d 0 1) (by simp) with h633 | h633
                                        · linarith only [h0, h633, hlam]
                                        · linarith only [h425, h633, hlam]
                                      · have p617_0 := h617c.1
                                        have p617_1 := h617c.2.1
                                        have p617_2 := h617c.2.2.1
                                        have p617_3 := h617c.2.2.2
                                        linarith only [h423, hlam, p617_1]
                                      · have p617_0 := h617c.1
                                        have p617_1 := h617c.2.1
                                        have p617_2 := h617c.2.2.1
                                        have p617_3 := h617c.2.2.2
                                        linarith only [h426, hlam, p617_1]
                                      · have p617_0 := h617c.1
                                        have p617_1 := h617c.2.1
                                        have p617_2 := h617c.2.2.1
                                        have p617_3 := h617c.2.2.2
                                        linarith only [hlam, p617_0]
                                      · have p617_0 := h617c.1
                                        have p617_1 := h617c.2.1
                                        have p617_2 := h617c.2.2.1
                                        have p617_3 := h617c.2.2.2
                                        linarith only [h429, hlam, p617_1]
                                      · have p617_0 := h617c.1
                                        have p617_1 := h617c.2.1
                                        have p617_2 := h617c.2.2.1
                                        have p617_3 := h617c.2.2.2
                                        linarith only [h429, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p617_1, u3elo3]
                                      · have p617_0 := h617c.1
                                        have p617_1 := h617c.2.1
                                        have p617_2 := h617c.2.2.1
                                        have p617_3 := h617c.2.2.2
                                        linarith only [h424, hlam, p617_0]
                                      · have p617_0 := h617c.1
                                        have p617_1 := h617c.2.1
                                        have p617_2 := h617c.2.2.1
                                        have p617_3 := h617c.2.2.2
                                        linarith only [h427, hlam, p617_0]
                                      · have p617_0 := h617c.1
                                        have p617_1 := h617c.2.1
                                        have p617_2 := h617c.2.2.1
                                        have p617_3 := h617c.2.2.2
                                        linarith only [h423, h606, h614, hc35, hlam, hphi, ht0b, ht5b, p617_1, u0elo3]
                                      · have p617_0 := h617c.1
                                        have p617_1 := h617c.2.1
                                        have p617_2 := h617c.2.2.1
                                        have p617_3 := h617c.2.2.2
                                        linarith only [hlam, p617_0]
                                      · have p617_0 := h617c.1
                                        have p617_1 := h617c.2.1
                                        have p617_2 := h617c.2.2.1
                                        have p617_3 := h617c.2.2.2
                                        rcases p617_3 (m.d 0 1) (by simp) with h645 | h645
                                        · rcases p617_3 (m.d 0 2) (by simp) with h646 | h646
                                          · rcases p617_3 (m.d 0 3) (by simp) with h647 | h647
                                            · linarith only [h429, h647, hlam]
                                            · linarith only [h604, h647, hlam]
                                          · linarith only [h428, h646, hlam]
                                        · linarith only [h425, h645, hlam]
                                      · have p617_0 := h617c.1
                                        have p617_1 := h617c.2.1
                                        have p617_2 := h617c.2.2.1
                                        have p617_3 := h617c.2.2.2
                                        linarith only [h425, hlam, p617_0]
                                      · have p617_0 := h617c.1
                                        have p617_1 := h617c.2.1
                                        have p617_2 := h617c.2.2.1
                                        have p617_3 := h617c.2.2.2
                                        linarith only [h428, hlam, p617_1]
                                      · have p617_0 := h617c.1
                                        have p617_1 := h617c.2.1
                                        have p617_2 := h617c.2.2.1
                                        have p617_3 := h617c.2.2.2
                                        linarith only [h604, hlam, p617_0]
                                      · have p617_0 := h617c.1
                                        have p617_1 := h617c.2.1
                                        have p617_2 := h617c.2.2.1
                                        have p617_3 := h617c.2.2.2
                                        linarith only [h605, hlam, p617_1]
                                      · have p617_0 := h617c.1
                                        have p617_1 := h617c.2.1
                                        have p617_2 := h617c.2.2.1
                                        have p617_3 := h617c.2.2.2
                                        linarith only [hlam, p617_0]
                                    · linarith only [h423, h429, h606, h614, h616, hc35, hlam, hphi, u5elo4]
                                  · linarith only [h612, h614, h615, hc35, hlam, hphi, u5elo4]
                                · linarith only [h429, h604, h614, hc23, hlam, hphi, u3elo3]
                            · linarith only [h429, h605, h609, h611, hc13, hlam, hphi, u3elo3]
                        · linarith only [h0, h608, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h427, h607, hlam]
                    · linarith only [h0, h606, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h429, h604, h605, hc35, hlam, hphi, u5elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h665 | h665
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h666 | h666
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h667 | h667
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h668 | h668
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h669 | h669
                          · linarith only [h423, h604, h669, hc34, hlam, hphi, ht45, u5elo3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h671 | h671
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h672 | h672
                              · linarith only [h423, h429, h666, h672, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h674 | h674
                                · linarith only [h423, h604, h666, h674, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h676 | h676
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h677 | h677
                                    · rcases h0bigk with h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [hlam, p678_0]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [h0, hlam, p678_1]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        rcases p678_3 (m.d 0 1) (by simp) with h681 | h681
                                        · rcases p678_3 (m.d 0 2) (by simp) with h682 | h682
                                          · rcases p678_3 (m.d 0 3) (by simp) with h683 | h683
                                            · linarith only [h423, h683, hlam]
                                            · rcases p678_3 (m.d 0 4) (by simp) with h685 | h685
                                              · linarith only [h424, h685, hlam]
                                              · linarith only [h429, h685, hlam]
                                          · linarith only [h426, h682, hlam]
                                        · linarith only [h423, h681, hlam]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [h0, h424, h667, h676, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p678_1]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        rcases p678_3 (m.d 0 1) (by simp) with h691 | h691
                                        · rcases p678_3 (m.d 0 2) (by simp) with h692 | h692
                                          · rcases p678_3 (m.d 0 3) (by simp) with h693 | h693
                                            · linarith only [h423, h693, hlam]
                                            · rcases p678_3 (m.d 0 4) (by simp) with h695 | h695
                                              · linarith only [h424, h695, hlam]
                                              · linarith only [h665, h695, hlam]
                                          · linarith only [h428, h692, hlam]
                                        · linarith only [h425, h691, hlam]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [h423, h666, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p678_1, u0elo1]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [hlam, p678_0]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        rcases p678_3 (m.d 0 1) (by simp) with h702 | h702
                                        · linarith only [h0, h702, hlam]
                                        · linarith only [h423, h702, hlam]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [h424, h667, h676, hc45, hlam, hphi, ht0b, ht5b, p678_1, u0elo1]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        rcases p678_3 (m.d 0 1) (by simp) with h706 | h706
                                        · linarith only [h0, h706, hlam]
                                        · linarith only [h425, h706, hlam]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [h423, hlam, p678_1]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [h426, hlam, p678_1]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [hlam, p678_0]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [h429, hlam, p678_1]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [h604, hlam, p678_1]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [h424, hlam, p678_0]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [h427, hlam, p678_0]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [h423, h429, h666, hc23, hlam, hphi, p678_1, u3elo3]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [hlam, p678_0]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [h423, h429, h604, h666, hc23, hlam, hphi, p678_1, u3elo3]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [h425, hlam, p678_0]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [h428, hlam, p678_1]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [h423, h666, hc23, hlam, hphi, ht34, ht45, p678_1, u5elo0]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [h665, hlam, p678_1]
                                      · have p678_0 := h678c.1
                                        have p678_1 := h678c.2.1
                                        have p678_2 := h678c.2.2.1
                                        have p678_3 := h678c.2.2.2
                                        linarith only [hlam, p678_0]
                                    · linarith only [h427, h429, h676, h677, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                  · linarith only [h424, h671, h676, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h429, h665, h666, h669, h671, hc23, hlam, hphi, u3elo3]
                        · linarith only [h0, h668, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h427, h667, hlam]
                    · linarith only [h0, h666, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h730 | h730
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h731 | h731
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h732 | h732
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h733 | h733
                          · linarith only [h423, h429, h665, h733, hc34, hlam, hphi, ht45, u5elo4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h735 | h735
                            · linarith only [h424, h665, h735, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h737 | h737
                              · linarith only [h429, h737, hc03, hlam, hphi, u3elo2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h739 | h739
                                · linarith only [h423, h425, h429, h604, h665, h730, h732, h739, hc25, hlam, hphi, u5elo4]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h741 | h741
                                  · linarith only [h424, h665, h731, h741, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h743 | h743
                                    · linarith only [h429, h665, h743, hc03, hlam, hphi, u3elo3]
                                    · linarith only [h423, h429, h730, h743, hc23, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h0, h732, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h427, h731, hlam]
                    · linarith only [h0, h423, h730, hc13, hlam, hphi, u3elo2]
            · linarith only [h0, h423, h428, hc13, hlam, hphi, ht34, ht45, u5elo2]
          · linarith only [h0, h424, h427, hlam]
        · linarith only [h0, h423, h426, hc13, hlam, hphi, u3elo2]
      · linarith only [h423, h425, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h753 | h753
      · rcases m.htr 0 2 3 (by decide) (by decide) with h754 | h754
        · rcases m.htr 0 2 4 (by decide) (by decide) with h755 | h755
          · rcases m.htr 0 2 5 (by decide) (by decide) with h756 | h756
            · rcases m.htr 0 3 4 (by decide) (by decide) with h757 | h757
              · linarith only [h423, h424, h757, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h759 | h759
                · rcases m.htr 0 4 5 (by decide) (by decide) with h760 | h760
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h761 | h761
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h762 | h762
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h763 | h763
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h764 | h764
                          · linarith only [h423, h757, h764, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h423, h424, h764, hc13, hlam, hphi, u3elo3]
                        · linarith only [h423, h424, h761, h762, h763, hc23, hlam, hphi, ht34, ht45, u5elo2]
                      · linarith only [h0, h423, h755, h761, h762, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h761, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h423, h424, h760, hc13, hlam, hphi, ht34, ht45, u5elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h771 | h771
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h772 | h772
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h773 | h773
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h774 | h774
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h775 | h775
                          · linarith only [h423, h759, h775, hc34, hlam, hphi, ht45, u5elo3]
                          · linarith only [h423, h424, h775, hc13, hlam, hphi, u3elo3]
                        · linarith only [h423, h424, h772, h773, h774, hc23, hlam, hphi, ht34, ht45, u5elo2]
                      · linarith only [h0, h423, h755, h772, h773, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h0, h423, h772, hc13, hlam, hphi, u3elo2]
                  · linarith only [h423, h424, h771, hc13, hlam, hphi, ht34, ht45, u5elo4]
            · linarith only [h0, h423, h756, hc13, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h783 | h783
            · rcases m.htr 0 3 4 (by decide) (by decide) with h784 | h784
              · linarith only [h0, h423, h755, h784, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h786 | h786
                · rcases m.htr 0 4 5 (by decide) (by decide) with h787 | h787
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h788 | h788
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h789 | h789
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h790 | h790
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h791 | h791
                          · linarith only [h423, h784, h791, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h0, h423, h755, h788, h789, h791, hc23, hlam, hphi, u3elo3]
                        · linarith only [h0, h423, h755, h788, h789, h790, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h795 | h795
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h796 | h796
                          · linarith only [h0, h423, h755, h784, h789, h796, hc02, hc24, hlam, hphi]
                          · linarith only [h0, h423, h788, h789, h796, hc23, hlam, hphi, u3elo3]
                        · linarith only [h0, h423, h788, h795, hc23, hlam, hphi, ht34, ht45, u5elo2]
                    · linarith only [h0, h423, h788, hc13, hlam, hphi, u3elo2]
                  · linarith only [h0, h423, h755, h787, hc13, hlam, hphi, ht34, ht45, u5elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h802 | h802
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h803 | h803
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h804 | h804
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h805 | h805
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h806 | h806
                          · linarith only [h0, h423, h755, h804, h806, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h0, h423, h755, h803, h804, h806, hc23, hlam, hphi, u3elo3]
                        · linarith only [h0, h423, h755, h803, h804, h805, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h810 | h810
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h811 | h811
                          · linarith only [h0, h423, h755, h784, h804, h811, hc02, hc24, hlam, hphi]
                          · linarith only [h423, h424, h803, h811, hc23, hlam, hphi, u3elo3]
                        · linarith only [h0, h423, h803, h810, hc23, hlam, hphi, ht34, ht45, u5elo2]
                    · linarith only [h0, h423, h803, hc13, hlam, hphi, u3elo2]
                  · linarith only [h0, h423, h755, h802, hc13, hlam, hphi, ht34, ht45, u5elo4]
            · linarith only [h0, h423, h783, hc13, hlam, hphi, ht34, ht45, u5elo2]
        · linarith only [h0, h423, h754, hc13, hlam, hphi, u3elo2]
      · linarith only [h423, h753, hc13, hlam, hphi, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h820 | h820
    · rcases m.htr 0 1 5 (by decide) (by decide) with h821 | h821
      · rcases m.htr 0 2 3 (by decide) (by decide) with h822 | h822
        · rcases m.htr 0 2 4 (by decide) (by decide) with h823 | h823
          · rcases m.htr 0 2 5 (by decide) (by decide) with h824 | h824
            · rcases m.htr 0 3 4 (by decide) (by decide) with h825 | h825
              · rcases m.htr 0 3 5 (by decide) (by decide) with h826 | h826
                · rcases m.htr 0 4 5 (by decide) (by decide) with h827 | h827
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h828 | h828
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h829 | h829
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h830 | h830
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h831 | h831
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h832 | h832
                            · linarith only [h423, h820, h832, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                            · linarith only [h423, h820, h827, h829, h832, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                          · linarith only [h423, h831, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h423, h820, h828, h829, h830, hc24, hlam, hphi, ht45, u5elo2]
                      · linarith only [h0, h823, h829, hlam]
                    · linarith only [h0, h822, h828, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h839 | h839
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h840 | h840
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h841 | h841
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h842 | h842
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h843 | h843
                            · linarith only [h423, h820, h843, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h845 | h845
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h846 | h846
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h847 | h847
                                  · linarith only [h423, h821, h827, h840, h843, h847, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h849 | h849
                                    · linarith only [h820, h827, h840, h845, h849, hlam]
                                    · rcases h0bigk with h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [hlam, p851_0]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [h0, hlam, p851_1]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [h423, hlam, p851_0]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [h423, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p851_1, u3elo1]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [h423, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p851_1, u3elo1]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [h821, hc15, hlam, hphi, ht0b, ht5b, p851_1, u0elo1]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [hlam, p851_0]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [h423, h820, h840, h845, hc34, hlam, hphi, ht0b, ht45, ht5b, p851_1, u0elo1]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        rcases p851_3 (m.d 0 1) (by simp) with h860 | h860
                                        · linarith only [h0, h860, hlam]
                                        · linarith only [h820, h860, hlam]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        rcases p851_3 (m.d 0 1) (by simp) with h863 | h863
                                        · linarith only [h0, h863, hlam]
                                        · linarith only [h821, h863, hlam]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [h821, h841, h845, h847, hc34, hlam, hphi, ht0b, ht45, ht5b, p851_1, u0elo2]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [h822, hlam, p851_1]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [hlam, p851_0]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        rcases p851_3 (m.d 0 1) (by simp) with h869 | h869
                                        · linarith only [h423, h869, hlam]
                                        · linarith only [h820, h869, hlam]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        rcases p851_3 (m.d 0 1) (by simp) with h872 | h872
                                        · linarith only [h423, h872, hlam]
                                        · linarith only [h821, h872, hlam]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [h820, hlam, p851_0]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [h823, hlam, p851_0]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [h825, hlam, p851_0]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [hlam, p851_0]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [h827, hlam, p851_0]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [h821, hlam, p851_0]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [h824, hlam, p851_1]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [h826, hlam, p851_0]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [h820, h840, h845, hc34, hlam, hphi, ht45, p851_1, u5elo0]
                                      · have p851_0 := h851c.1
                                        have p851_1 := h851c.2.1
                                        have p851_2 := h851c.2.2.1
                                        have p851_3 := h851c.2.2.2
                                        linarith only [hlam, p851_0]
                                · linarith only [h423, h826, h846, hc23, hlam, hphi, u3elo1]
                              · linarith only [h423, h825, h845, hc23, hlam, hphi, u3elo1]
                          · linarith only [h423, h842, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h820, h840, h841, hc24, hlam, hphi, ht45, u5elo2]
                      · linarith only [h0, h823, h840, hlam]
                    · linarith only [h0, h839, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h423, h820, h826, hc14, hlam, hphi, ht45, u5elo3]
              · linarith only [h423, h820, h825, hlam]
            · linarith only [h823, h824, hc24, hlam, hphi, ht45, u5elo2]
          · linarith only [h423, h820, h822, h823, hc23, hlam, hphi, u3elo1]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h895 | h895
          · rcases m.htr 0 2 5 (by decide) (by decide) with h896 | h896
            · rcases m.htr 0 3 4 (by decide) (by decide) with h897 | h897
              · rcases m.htr 0 3 5 (by decide) (by decide) with h898 | h898
                · rcases m.htr 0 4 5 (by decide) (by decide) with h899 | h899
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h900 | h900
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h901 | h901
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h902 | h902
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h903 | h903
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h904 | h904
                            · linarith only [h0, h820, h822, h900, h904, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                            · linarith only [h0, h820, h822, h899, h900, h904, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                          · linarith only [h0, h822, h900, h903, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h820, h822, h900, h901, h902, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h820, h822, h900, h901, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h820, h900, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h911 | h911
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h912 | h912
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h913 | h913
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h914 | h914
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h915 | h915
                            · linarith only [h423, h820, h915, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h917 | h917
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h918 | h918
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h919 | h919
                                  · linarith only [h0, h821, h822, h899, h911, h912, h915, h919, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h921 | h921
                                    · linarith only [h820, h899, h912, h917, h921, hlam]
                                    · rcases h0bigk with h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c | h923c
                                      · have p923_0 := h923c.1
                                        have p923_1 := h923c.2.1
                                        have p923_2 := h923c.2.2.1
                                        have p923_3 := h923c.2.2.2
                                        linarith only [hlam, p923_0]
                                      · have p923_0 := h923c.1
                                        have p923_1 := h923c.2.1
                                        have p923_2 := h923c.2.2.1
                                        have p923_3 := h923c.2.2.2
                                        linarith only [h0, hlam, p923_1]
                                      · have p923_0 := h923c.1
                                        have p923_1 := h923c.2.1
                                        have p923_2 := h923c.2.2.1
                                        have p923_3 := h923c.2.2.2
                                        linarith only [h423, hlam, p923_0]
                                      · have p923_0 := h923c.1
                                        have p923_1 := h923c.2.1
                                        have p923_2 := h923c.2.2.1
                                        have p923_3 := h923c.2.2.2
                                        linarith only [h0, h822, h911, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p923_1, u3elo1]
                                      · have p923_0 := h923c.1
                                        have p923_1 := h923c.2.1
                                        have p923_2 := h923c.2.2.1
                                        have p923_3 := h923c.2.2.2
                                        linarith only [h0, h822, h911, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p923_1, u3elo1]
                                      · have p923_0 := h923c.1
                                        have p923_1 := h923c.2.1
                                        have p923_2 := h923c.2.2.1
                                        have p923_3 := h923c.2.2.2
                                        linarith only [h822, h911, hc01, hlam, hphi, ht12, ht23, p923_1, u3elo1]
                                      · have p923_0 := h923c.1
                                        have p923_1 := h923c.2.1
                                        have p923_2 := h923c.2.2.1
                                        have p923_3 := h923c.2.2.2
                                        linarith only [hlam, p923_0]
                                      · have p923_0 := h923c.1
                                        have p923_1 := h923c.2.1
                                        have p923_2 := h923c.2.2.1
                                        have p923_3 := h923c.2.2.2
                                        linarith only [h822, hlam, p923_0]
                                      · have p923_0 := h923c.1
                                        have p923_1 := h923c.2.1
                                        have p923_2 := h923c.2.2.1
                                        have p923_3 := h923c.2.2.2
                                        linarith only [h820, h822, h911, h912, h917, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p923_1, u3elo1]
                                      · have p923_0 := h923c.1
                                        have p923_1 := h923c.2.1
                                        have p923_2 := h923c.2.2.1
                                        have p923_3 := h923c.2.2.2
                                        linarith only [h821, h822, h911, h913, h918, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p923_1, u3elo1]
                                      · have p923_0 := h923c.1
                                        have p923_1 := h923c.2.1
                                        have p923_2 := h923c.2.2.1
                                        have p923_3 := h923c.2.2.2
                                        linarith only [h820, h912, h917, hc34, hlam, hphi, ht0b, ht45, ht5b, p923_1, u0elo2]
                                      · have p923_0 := h923c.1
                                        have p923_1 := h923c.2.1
                                        have p923_2 := h923c.2.2.1
                                        have p923_3 := h923c.2.2.2
                                        linarith only [h822, h911, hc02, hlam, hphi, ht23, p923_1, u3elo1]
                                      · have p923_0 := h923c.1
                                        have p923_1 := h923c.2.1
                                        have p923_2 := h923c.2.2.1
                                        have p923_3 := h923c.2.2.2
                                        linarith only [hlam, p923_0]
                                      · have p923_0 := h923c.1
                                        have p923_1 := h923c.2.1
                                        have p923_2 := h923c.2.2.1
                                        have p923_3 := h923c.2.2.2
                                        rcases p923_3 (m.d 0 1) (by simp) with h937 | h937
                                        · linarith only [h423, h937, hlam]
                                        · linarith only [h820, h937, hlam]
                                      · have p923_0 := h923c.1
                                        have p923_1 := h923c.2.1
                                        have p923_2 := h923c.2.2.1
                                        have p923_3 := h923c.2.2.2
                                        rcases p923_3 (m.d 0 1) (by simp) with h940 | h940
                                        · linarith only [h423, h940, hlam]
                                        · linarith only [h821, h940, hlam]
                                      · have p923_0 := h923c.1
                                        have p923_1 := h923c.2.1
                                        have p923_2 := h923c.2.2.1
                                        have p923_3 := h923c.2.2.2
                                        linarith only [h820, hlam, p923_0]
                                      · have p923_0 := h923c.1
                                        have p923_1 := h923c.2.1
                                        have p923_2 := h923c.2.2.1
                                        have p923_3 := h923c.2.2.2
                                        linarith only [h895, hlam, p923_0]
                                      · have p923_0 := h923c.1
                                        have p923_1 := h923c.2.1
                                        have p923_2 := h923c.2.2.1
                                        have p923_3 := h923c.2.2.2
                                        linarith only [h897, hlam, p923_0]
                                      · have p923_0 := h923c.1
                                        have p923_1 := h923c.2.1
                                        have p923_2 := h923c.2.2.1
                                        have p923_3 := h923c.2.2.2
                                        linarith only [hlam, p923_0]
                                      · have p923_0 := h923c.1
                                        have p923_1 := h923c.2.1
                                        have p923_2 := h923c.2.2.1
                                        have p923_3 := h923c.2.2.2
                                        linarith only [h899, hlam, p923_0]
                                      · have p923_0 := h923c.1
                                        have p923_1 := h923c.2.1
                                        have p923_2 := h923c.2.2.1
                                        have p923_3 := h923c.2.2.2
                                        linarith only [h821, hlam, p923_0]
                                      · have p923_0 := h923c.1
                                        have p923_1 := h923c.2.1
                                        have p923_2 := h923c.2.2.1
                                        have p923_3 := h923c.2.2.2
                                        linarith only [h896, hlam, p923_1]
                                      · have p923_0 := h923c.1
                                        have p923_1 := h923c.2.1
                                        have p923_2 := h923c.2.2.1
                                        have p923_3 := h923c.2.2.2
                                        linarith only [h898, hlam, p923_0]
                                      · have p923_0 := h923c.1
                                        have p923_1 := h923c.2.1
                                        have p923_2 := h923c.2.2.1
                                        have p923_3 := h923c.2.2.2
                                        linarith only [h820, h912, h917, hc34, hlam, hphi, ht45, p923_1, u5elo0]
                                      · have p923_0 := h923c.1
                                        have p923_1 := h923c.2.1
                                        have p923_2 := h923c.2.2.1
                                        have p923_3 := h923c.2.2.2
                                        linarith only [hlam, p923_0]
                                · linarith only [h423, h821, h822, h912, h915, h917, h918, hc34, hlam, hphi, ht45, u5elo3]
                              · linarith only [h0, h821, h822, h912, h915, h917, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                          · linarith only [h0, h821, h822, h897, h911, h914, hc15, hlam, hphi, ht0b, ht5b, u0elo3]
                        · linarith only [h0, h820, h822, h911, h912, h913, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h820, h822, h911, h912, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h820, h911, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · linarith only [h0, h820, h822, h898, hc14, hlam, hphi, ht45, u5elo3]
              · linarith only [h0, h820, h822, h897, hlam]
            · linarith only [h0, h820, h896, hc14, hlam, hphi, ht45, u5elo2]
          · linarith only [h0, h820, h895, hlam]
      · linarith only [h820, h821, hc14, hlam, hphi, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h964 | h964
      · rcases m.htr 0 2 3 (by decide) (by decide) with h965 | h965
        · rcases m.htr 0 2 4 (by decide) (by decide) with h966 | h966
          · rcases m.htr 0 2 5 (by decide) (by decide) with h967 | h967
            · rcases m.htr 0 3 4 (by decide) (by decide) with h968 | h968
              · rcases m.htr 0 3 5 (by decide) (by decide) with h969 | h969
                · rcases m.htr 0 4 5 (by decide) (by decide) with h970 | h970
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h971 | h971
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h972 | h972
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h973 | h973
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h974 | h974
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h975 | h975
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h976 | h976
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h977 | h977
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h978 | h978
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h979 | h979
                                    · linarith only [h965, h976, h979, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                    · linarith only [h423, h964, h975, h979, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                  · linarith only [h820, h964, h974, h975, h978, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                · linarith only [h969, h977, hc23, hlam, hphi, u3elo0]
                              · linarith only [h423, h968, h976, hc23, hlam, hphi, u3elo1]
                            · linarith only [h820, h975, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                          · linarith only [h423, h964, h973, h974, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                        · linarith only [h0, h964, h973, hc15, hlam, hphi, u5elo2]
                      · linarith only [h0, h966, h972, hlam]
                    · linarith only [h0, h964, h971, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                  · linarith only [h820, h964, h970, hc15, hlam, hphi, u5elo4]
                · linarith only [h820, h964, h968, h969, hc15, hlam, hphi, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h992 | h992
                · rcases m.htr 0 4 5 (by decide) (by decide) with h993 | h993
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h994 | h994
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h995 | h995
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h996 | h996
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h997 | h997
                          · linarith only [h423, h964, h968, h996, h997, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                          · linarith only [h423, h964, h996, h997, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                        · linarith only [h423, h964, h994, h996, hc15, hlam, hphi, u5elo2]
                      · linarith only [h423, h964, h966, h994, h995, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                    · linarith only [h0, h964, h994, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                  · linarith only [h423, h964, h968, h993, hc15, hlam, hphi, u5elo4]
                · linarith only [h423, h964, h992, hc15, hlam, hphi, u5elo3]
            · linarith only [h965, h967, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1006 | h1006
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1007 | h1007
              · linarith only [h1007, h965, h966, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1009 | h1009
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1010 | h1010
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1011 | h1011
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1012 | h1012
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1013 | h1013
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1014 | h1014
                          · linarith only [h1007, h1013, h1014, h423, h964, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                          · linarith only [h1013, h1014, h423, h964, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                        · linarith only [h1012, h1013, h965, h966, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1018 | h1018
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1019 | h1019
                          · linarith only [h1007, h1018, h1019, h423, h964, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                          · linarith only [h1018, h1019, h423, h964, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                        · linarith only [h0, h1018, h964, hc15, hlam, hphi, u5elo2]
                    · linarith only [h0, h1011, h964, h965, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                  · linarith only [h0, h1010, h964, h966, hc15, hlam, hphi, u5elo4]
                · linarith only [h1009, h423, h964, hc15, hlam, hphi, u5elo3]
            · linarith only [h1006, h965, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1027 | h1027
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1028 | h1028
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1029 | h1029
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1030 | h1030
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1031 | h1031
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1032 | h1032
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1033 | h1033
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1034 | h1034
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1035 | h1035
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1036 | h1036
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1037 | h1037
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1038 | h1038
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1039 | h1039
                                  · linarith only [h1027, h1032, h1039, h965, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                                  · linarith only [h1027, h1031, h1032, h1039, h965, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                · linarith only [h1027, h1038, h820, h965, hc01, hlam, hphi, ht12, ht23, u3elo4]
                              · linarith only [h1027, h1037, h820, h965, hc01, hlam, hphi, ht12, ht23, u3elo3]
                            · linarith only [h1034, h1036, h820, h964, hc25, hlam, hphi, u5elo4]
                          · linarith only [h1027, h1029, h1032, h1035, h965, hlam]
                        · linarith only [h1027, h1032, h1034, h820, h964, h965, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h1027, h1032, h1033, h965, hlam]
                    · linarith only [h0, h1032, h964, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                  · linarith only [h1031, h820, h964, hc15, hlam, hphi, u5elo4]
                · linarith only [h1030, h423, h964, hc15, hlam, hphi, u5elo3]
              · linarith only [h1027, h1029, h965, hlam]
            · linarith only [h1027, h1028, h820, h964, hc15, hlam, hphi, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1053 | h1053
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1054 | h1054
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1055 | h1055
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1056 | h1056
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1057 | h1057
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1058 | h1058
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1059 | h1059
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1060 | h1060
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1061 | h1061
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1062 | h1062
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1063 | h1063
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1064 | h1064
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1065 | h1065
                                    · rcases h0bigk with h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c
                                      · have p1066_0 := h1066c.1
                                        have p1066_1 := h1066c.2.1
                                        have p1066_2 := h1066c.2.2.1
                                        have p1066_3 := h1066c.2.2.2
                                        linarith only [hlam, p1066_0]
                                      · have p1066_0 := h1066c.1
                                        have p1066_1 := h1066c.2.1
                                        have p1066_2 := h1066c.2.2.1
                                        have p1066_3 := h1066c.2.2.2
                                        linarith only [h0, hlam, p1066_1]
                                      · have p1066_0 := h1066c.1
                                        have p1066_1 := h1066c.2.1
                                        have p1066_2 := h1066c.2.2.1
                                        have p1066_3 := h1066c.2.2.2
                                        linarith only [h423, hlam, p1066_0]
                                      · have p1066_0 := h1066c.1
                                        have p1066_1 := h1066c.2.1
                                        have p1066_2 := h1066c.2.2.1
                                        have p1066_3 := h1066c.2.2.2
                                        linarith only [h820, hlam, p1066_1]
                                      · have p1066_0 := h1066c.1
                                        have p1066_1 := h1066c.2.1
                                        have p1066_2 := h1066c.2.2.1
                                        have p1066_3 := h1066c.2.2.2
                                        linarith only [h423, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1066_1, u3elo1]
                                      · have p1066_0 := h1066c.1
                                        have p1066_1 := h1066c.2.1
                                        have p1066_2 := h1066c.2.2.1
                                        have p1066_3 := h1066c.2.2.2
                                        linarith only [h1027, h1058, hc01, hc14, hlam, hphi, p1066_1]
                                      · have p1066_0 := h1066c.1
                                        have p1066_1 := h1066c.2.1
                                        have p1066_2 := h1066c.2.2.1
                                        have p1066_3 := h1066c.2.2.2
                                        linarith only [hlam, p1066_0]
                                      · have p1066_0 := h1066c.1
                                        have p1066_1 := h1066c.2.1
                                        have p1066_2 := h1066c.2.2.1
                                        have p1066_3 := h1066c.2.2.2
                                        linarith only [h965, hlam, p1066_0]
                                      · have p1066_0 := h1066c.1
                                        have p1066_1 := h1066c.2.1
                                        have p1066_2 := h1066c.2.2.1
                                        have p1066_3 := h1066c.2.2.2
                                        linarith only [h1027, hlam, p1066_1]
                                      · have p1066_0 := h1066c.1
                                        have p1066_1 := h1066c.2.1
                                        have p1066_2 := h1066c.2.2.1
                                        have p1066_3 := h1066c.2.2.2
                                        linarith only [h1057, h1059, h1063, h1065, h964, h965, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1066_1, u3elo1]
                                      · have p1066_0 := h1066c.1
                                        have p1066_1 := h1066c.2.1
                                        have p1066_2 := h1066c.2.2.1
                                        have p1066_3 := h1066c.2.2.2
                                        linarith only [h1059, h1063, h1065, h964, hc45, hlam, hphi, ht0b, ht5b, p1066_1, u0elo2]
                                      · have p1066_0 := h1066c.1
                                        have p1066_1 := h1066c.2.1
                                        have p1066_2 := h1066c.2.2.1
                                        have p1066_3 := h1066c.2.2.2
                                        linarith only [h1057, h965, hc02, hlam, hphi, ht23, p1066_1, u3elo1]
                                      · have p1066_0 := h1066c.1
                                        have p1066_1 := h1066c.2.1
                                        have p1066_2 := h1066c.2.2.1
                                        have p1066_3 := h1066c.2.2.2
                                        linarith only [hlam, p1066_0]
                                      · have p1066_0 := h1066c.1
                                        have p1066_1 := h1066c.2.1
                                        have p1066_2 := h1066c.2.2.1
                                        have p1066_3 := h1066c.2.2.2
                                        linarith only [h1057, h1059, h1063, h1065, h820, h964, h965, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1066_1, u3elo1]
                                      · have p1066_0 := h1066c.1
                                        have p1066_1 := h1066c.2.1
                                        have p1066_2 := h1066c.2.2.1
                                        have p1066_3 := h1066c.2.2.2
                                        rcases p1066_3 (m.d 0 1) (by simp) with h1081 | h1081
                                        · linarith only [h1081, h423, hlam]
                                        · linarith only [h1081, h964, hlam]
                                      · have p1066_0 := h1066c.1
                                        have p1066_1 := h1066c.2.1
                                        have p1066_2 := h1066c.2.2.1
                                        have p1066_3 := h1066c.2.2.2
                                        linarith only [h1059, h1063, h1065, h964, hc45, hlam, hphi, ht0b, ht5b, p1066_1, u0elo3]
                                      · have p1066_0 := h1066c.1
                                        have p1066_1 := h1066c.2.1
                                        have p1066_2 := h1066c.2.2.1
                                        have p1066_3 := h1066c.2.2.2
                                        linarith only [h0, h1027, h1058, h1059, h1060, h1063, h1065, h964, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1066_1, u3elo1]
                                      · have p1066_0 := h1066c.1
                                        have p1066_1 := h1066c.2.1
                                        have p1066_2 := h1066c.2.2.1
                                        have p1066_3 := h1066c.2.2.2
                                        linarith only [h1054, hlam, p1066_0]
                                      · have p1066_0 := h1066c.1
                                        have p1066_1 := h1066c.2.1
                                        have p1066_2 := h1066c.2.2.1
                                        have p1066_3 := h1066c.2.2.2
                                        linarith only [hlam, p1066_0]
                                      · have p1066_0 := h1066c.1
                                        have p1066_1 := h1066c.2.1
                                        have p1066_2 := h1066c.2.2.1
                                        have p1066_3 := h1066c.2.2.2
                                        rcases p1066_3 (m.d 0 1) (by simp) with h1088 | h1088
                                        · linarith only [h1088, h820, hlam]
                                        · linarith only [h1088, h964, hlam]
                                      · have p1066_0 := h1066c.1
                                        have p1066_1 := h1066c.2.1
                                        have p1066_2 := h1066c.2.2.1
                                        have p1066_3 := h1066c.2.2.2
                                        linarith only [h964, hlam, p1066_0]
                                      · have p1066_0 := h1066c.1
                                        have p1066_1 := h1066c.2.1
                                        have p1066_2 := h1066c.2.2.1
                                        have p1066_3 := h1066c.2.2.2
                                        linarith only [h1053, hlam, p1066_1]
                                      · have p1066_0 := h1066c.1
                                        have p1066_1 := h1066c.2.1
                                        have p1066_2 := h1066c.2.2.1
                                        have p1066_3 := h1066c.2.2.2
                                        linarith only [h1055, hlam, p1066_0]
                                      · have p1066_0 := h1066c.1
                                        have p1066_1 := h1066c.2.1
                                        have p1066_2 := h1066c.2.2.1
                                        have p1066_3 := h1066c.2.2.2
                                        linarith only [h1056, hlam, p1066_1]
                                      · have p1066_0 := h1066c.1
                                        have p1066_1 := h1066c.2.1
                                        have p1066_2 := h1066c.2.2.1
                                        have p1066_3 := h1066c.2.2.2
                                        linarith only [hlam, p1066_0]
                                    · linarith only [h1061, h1065, h423, h964, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                  · linarith only [h0, h1027, h1061, h1064, h964, hlam]
                                · linarith only [h1061, h1063, h423, h964, h965, hc45, hlam, hphi, u5elo3]
                              · linarith only [h0, h1061, h1062, h964, h965, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                            · linarith only [h1059, h1061, h820, h964, hc25, hlam, hphi, u5elo4]
                          · linarith only [h1054, h1060, hc13, hlam, hphi, u3elo0]
                        · linarith only [h0, h1059, h964, hc15, hlam, hphi, u5elo2]
                      · linarith only [h0, h1057, h1058, h964, h965, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h0, h1057, h964, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                  · linarith only [h1056, h820, h964, hc15, hlam, hphi, u5elo4]
                · linarith only [h1054, h1055, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1107 | h1107
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1108 | h1108
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1109 | h1109
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1110 | h1110
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1111 | h1111
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1112 | h1112
                          · linarith only [h0, h1054, h1111, h1112, h964, h965, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                          · linarith only [h1111, h1112, h423, h964, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                        · linarith only [h0, h1109, h1111, h964, h965, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h1109, h1110, h964, h965, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h0, h1109, h964, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                  · linarith only [h0, h1054, h1108, h964, h965, hc15, hlam, hphi, u5elo4]
                · linarith only [h0, h1107, h964, h965, hc15, hlam, hphi, u5elo3]
            · linarith only [h0, h1053, h964, hc15, hlam, hphi, u5elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1121 | h1121
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1122 | h1122
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1123 | h1123
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1124 | h1124
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1125 | h1125
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1126 | h1126
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1127 | h1127
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1128 | h1128
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1129 | h1129
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1130 | h1130
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1131 | h1131
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1132 | h1132
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1133 | h1133
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1134 | h1134
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1135 | h1135
                                    · linarith only [h1121, h1132, h1135, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                    · linarith only [h1121, h1132, h1134, h1135, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1138 | h1138
                                    · linarith only [h1132, h1134, h1138, hlam]
                                    · rcases h0bigk with h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c
                                      · have p1140_0 := h1140c.1
                                        have p1140_1 := h1140c.2.1
                                        have p1140_2 := h1140c.2.2.1
                                        have p1140_3 := h1140c.2.2.2
                                        linarith only [hlam, p1140_0]
                                      · have p1140_0 := h1140c.1
                                        have p1140_1 := h1140c.2.1
                                        have p1140_2 := h1140c.2.2.1
                                        have p1140_3 := h1140c.2.2.2
                                        linarith only [h0, hlam, p1140_1]
                                      · have p1140_0 := h1140c.1
                                        have p1140_1 := h1140c.2.1
                                        have p1140_2 := h1140c.2.2.1
                                        have p1140_3 := h1140c.2.2.2
                                        linarith only [h423, hlam, p1140_0]
                                      · have p1140_0 := h1140c.1
                                        have p1140_1 := h1140c.2.1
                                        have p1140_2 := h1140c.2.2.1
                                        have p1140_3 := h1140c.2.2.2
                                        linarith only [h820, hlam, p1140_1]
                                      · have p1140_0 := h1140c.1
                                        have p1140_1 := h1140c.2.1
                                        have p1140_2 := h1140c.2.2.1
                                        have p1140_3 := h1140c.2.2.2
                                        linarith only [h964, hlam, p1140_1]
                                      · have p1140_0 := h1140c.1
                                        have p1140_1 := h1140c.2.1
                                        have p1140_2 := h1140c.2.2.1
                                        have p1140_3 := h1140c.2.2.2
                                        rcases p1140_3 (m.d 0 1) (by simp) with h1146 | h1146
                                        · linarith only [h0, h1146, hlam]
                                        · rcases p1140_3 (m.d 0 2) (by simp) with h1148 | h1148
                                          · rcases p1140_3 (m.d 0 3) (by simp) with h1149 | h1149
                                            · linarith only [h1121, h1149, hlam]
                                            · linarith only [h1149, h423, hlam]
                                          · linarith only [h0, h1148, hlam]
                                      · have p1140_0 := h1140c.1
                                        have p1140_1 := h1140c.2.1
                                        have p1140_2 := h1140c.2.2.1
                                        have p1140_3 := h1140c.2.2.2
                                        linarith only [hlam, p1140_0]
                                      · have p1140_0 := h1140c.1
                                        have p1140_1 := h1140c.2.1
                                        have p1140_2 := h1140c.2.2.1
                                        have p1140_3 := h1140c.2.2.2
                                        linarith only [h1124, h1126, h1132, h1134, hc34, hlam, hphi, ht0b, ht45, ht5b, p1140_1, u0elo1]
                                      · have p1140_0 := h1140c.1
                                        have p1140_1 := h1140c.2.1
                                        have p1140_2 := h1140c.2.2.1
                                        have p1140_3 := h1140c.2.2.2
                                        linarith only [h1126, h1132, h1134, hc34, hlam, hphi, ht0b, ht45, ht5b, p1140_1, u0elo1]
                                      · have p1140_0 := h1140c.1
                                        have p1140_1 := h1140c.2.1
                                        have p1140_2 := h1140c.2.2.1
                                        have p1140_3 := h1140c.2.2.2
                                        linarith only [h1126, h1132, h1134, hc34, hlam, hphi, ht0b, ht45, ht5b, p1140_1, u0elo1]
                                      · have p1140_0 := h1140c.1
                                        have p1140_1 := h1140c.2.1
                                        have p1140_2 := h1140c.2.2.1
                                        have p1140_3 := h1140c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht12, ht23, p1140_1, u3elo0]
                                      · have p1140_0 := h1140c.1
                                        have p1140_1 := h1140c.2.1
                                        have p1140_2 := h1140c.2.2.1
                                        have p1140_3 := h1140c.2.2.2
                                        linarith only [h1121, hlam, p1140_1]
                                      · have p1140_0 := h1140c.1
                                        have p1140_1 := h1140c.2.1
                                        have p1140_2 := h1140c.2.2.1
                                        have p1140_3 := h1140c.2.2.2
                                        linarith only [hlam, p1140_0]
                                      · have p1140_0 := h1140c.1
                                        have p1140_1 := h1140c.2.1
                                        have p1140_2 := h1140c.2.2.1
                                        have p1140_3 := h1140c.2.2.2
                                        linarith only [h1126, h1132, h1134, h423, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1140_1, u3elo1]
                                      · have p1140_0 := h1140c.1
                                        have p1140_1 := h1140c.2.1
                                        have p1140_2 := h1140c.2.2.1
                                        have p1140_3 := h1140c.2.2.2
                                        linarith only [h1126, h1132, h1134, h423, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1140_1, u3elo1]
                                      · have p1140_0 := h1140c.1
                                        have p1140_1 := h1140c.2.1
                                        have p1140_2 := h1140c.2.2.1
                                        have p1140_3 := h1140c.2.2.2
                                        linarith only [h1124, h423, hc01, hlam, hphi, ht12, ht23, p1140_1, u3elo1]
                                      · have p1140_0 := h1140c.1
                                        have p1140_1 := h1140c.2.1
                                        have p1140_2 := h1140c.2.2.1
                                        have p1140_3 := h1140c.2.2.2
                                        linarith only [h1122, hlam, p1140_0]
                                      · have p1140_0 := h1140c.1
                                        have p1140_1 := h1140c.2.1
                                        have p1140_2 := h1140c.2.2.1
                                        have p1140_3 := h1140c.2.2.2
                                        linarith only [h1124, hlam, p1140_0]
                                      · have p1140_0 := h1140c.1
                                        have p1140_1 := h1140c.2.1
                                        have p1140_2 := h1140c.2.2.1
                                        have p1140_3 := h1140c.2.2.2
                                        linarith only [hlam, p1140_0]
                                      · have p1140_0 := h1140c.1
                                        have p1140_1 := h1140c.2.1
                                        have p1140_2 := h1140c.2.2.1
                                        have p1140_3 := h1140c.2.2.2
                                        linarith only [h1124, h1126, h1132, h1134, h423, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1140_1, u3elo1]
                                      · have p1140_0 := h1140c.1
                                        have p1140_1 := h1140c.2.1
                                        have p1140_2 := h1140c.2.2.1
                                        have p1140_3 := h1140c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1140_1, u5elo0]
                                      · have p1140_0 := h1140c.1
                                        have p1140_1 := h1140c.2.1
                                        have p1140_2 := h1140c.2.2.1
                                        have p1140_3 := h1140c.2.2.2
                                        linarith only [h1123, hlam, p1140_1]
                                      · have p1140_0 := h1140c.1
                                        have p1140_1 := h1140c.2.1
                                        have p1140_2 := h1140c.2.2.1
                                        have p1140_3 := h1140c.2.2.2
                                        linarith only [h1125, hlam, p1140_0]
                                      · have p1140_0 := h1140c.1
                                        have p1140_1 := h1140c.2.1
                                        have p1140_2 := h1140c.2.2.1
                                        have p1140_3 := h1140c.2.2.2
                                        linarith only [h1126, hlam, p1140_1]
                                      · have p1140_0 := h1140c.1
                                        have p1140_1 := h1140c.2.1
                                        have p1140_2 := h1140c.2.2.1
                                        have p1140_3 := h1140c.2.2.2
                                        linarith only [hlam, p1140_0]
                                · linarith only [h1125, h1133, h423, hc23, hlam, hphi, u3elo1]
                              · linarith only [h1124, h1132, h423, hc23, hlam, hphi, u3elo1]
                            · linarith only [h1126, h1131, h820, hlam]
                          · linarith only [h1124, h1130, h423, hlam]
                        · linarith only [h0, h1129, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h1122, h1128, hlam]
                    · linarith only [h0, h1127, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1179 | h1179
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1180 | h1180
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1181 | h1181
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1182 | h1182
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1183 | h1183
                            · linarith only [h1126, h1182, h1183, h820, hc01, hlam, hphi, ht12, ht23, u3elo1]
                            · linarith only [h1183, h820, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                          · linarith only [h1124, h1182, hc13, hlam, hphi, u3elo0]
                        · linarith only [h0, h1123, h1181, hlam]
                      · linarith only [h0, h1122, h1180, hlam]
                    · linarith only [h0, h1179, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h1124, h1125, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1191 | h1191
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1192 | h1192
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1193 | h1193
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1194 | h1194
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1195 | h1195
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1196 | h1196
                          · linarith only [h1124, h1191, h1196, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                          · linarith only [h1196, h423, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h1123, h1193, h1195, h423, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h1122, h1194, hlam]
                    · linarith only [h0, h1193, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h1124, h1191, h1192, hc35, hlam, hphi, u5elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1203 | h1203
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1204 | h1204
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1205 | h1205
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1206 | h1206
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1207 | h1207
                          · linarith only [h1124, h1207, hc03, hlam, hphi, u3elo1]
                          · linarith only [h1207, h423, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h1123, h1204, h1206, h423, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h1122, h1205, hlam]
                    · linarith only [h0, h1204, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1213 | h1213
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1214 | h1214
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1215 | h1215
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1216 | h1216
                          · linarith only [h1124, h1216, h423, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h1216, h423, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h1123, h1213, h1215, h423, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h1122, h1214, hlam]
                    · linarith only [h0, h1213, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h1121, h1123, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1223 | h1223
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1224 | h1224
              · linarith only [h1121, h1122, h1224, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1226 | h1226
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1227 | h1227
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1228 | h1228
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1229 | h1229
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1230 | h1230
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1231 | h1231
                          · linarith only [h1224, h1231, hc03, hlam, hphi, u3elo1]
                          · linarith only [h1231, h423, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h1122, h1223, h1229, h1230, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1235 | h1235
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1236 | h1236
                          · linarith only [h1224, h1226, h1236, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                          · linarith only [h1236, h423, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h1223, h1235, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1228, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h1121, h1122, h1227, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1242 | h1242
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1243 | h1243
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1244 | h1244
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1245 | h1245
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1246 | h1246
                          · linarith only [h1224, h1246, hc03, hlam, hphi, u3elo1]
                          · linarith only [h1246, h423, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h1122, h1223, h1244, h1245, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1250 | h1250
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1251 | h1251
                          · linarith only [h1224, h1251, h423, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h1251, h423, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h1223, h1250, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1243, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h1121, h1122, h1242, hc23, hlam, hphi, ht34, ht45, u5elo4]
            · linarith only [h1121, h1223, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1258 | h1258
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1259 | h1259
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1260 | h1260
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1261 | h1261
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1262 | h1262
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1263 | h1263
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1264 | h1264
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1265 | h1265
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1266 | h1266
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1267 | h1267
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1268 | h1268
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1269 | h1269
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1270 | h1270
                                  · linarith only [h1121, h1258, h1263, h1270, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                                  · linarith only [h1121, h1258, h1262, h1263, h1268, h1270, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                · linarith only [h1121, h1269, hc02, hlam, hphi, ht23, u3elo4]
                              · linarith only [h1121, h1268, hc02, hlam, hphi, ht23, u3elo3]
                            · linarith only [h1121, h1258, h1262, h1267, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                          · linarith only [h1121, h1258, h1260, h1263, h1266, hlam]
                        · linarith only [h0, h1265, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h1121, h1258, h1263, h1264, hlam]
                    · linarith only [h0, h1263, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1280 | h1280
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1281 | h1281
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1282 | h1282
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1283 | h1283
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1284 | h1284
                            · linarith only [h1262, h1283, h1284, h820, hc01, hlam, hphi, ht12, ht23, u3elo1]
                            · linarith only [h1121, h1258, h1280, h1284, h820, hc01, hc24, hlam, hphi, ht12, ht23, ht45, u3elo1, u5elo4]
                          · linarith only [h1121, h1258, h1280, h1283, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h1121, h1259, h1280, h1282, hlam]
                      · linarith only [h1121, h1258, h1280, h1281, hlam]
                    · linarith only [h0, h1280, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h1121, h1258, h1261, hc24, hlam, hphi, ht45, u5elo3]
              · linarith only [h1121, h1258, h1260, hlam]
            · linarith only [h1258, h1259, hc24, hlam, hphi, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1294 | h1294
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1295 | h1295
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1296 | h1296
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1297 | h1297
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1298 | h1298
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1299 | h1299
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1300 | h1300
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1301 | h1301
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1302 | h1302
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1303 | h1303
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1304 | h1304
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1305 | h1305
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1306 | h1306
                                    · rcases h0bigk with h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c | h1307c
                                      · have p1307_0 := h1307c.1
                                        have p1307_1 := h1307c.2.1
                                        have p1307_2 := h1307c.2.2.1
                                        have p1307_3 := h1307c.2.2.2
                                        linarith only [hlam, p1307_0]
                                      · have p1307_0 := h1307c.1
                                        have p1307_1 := h1307c.2.1
                                        have p1307_2 := h1307c.2.2.1
                                        have p1307_3 := h1307c.2.2.2
                                        linarith only [h0, hlam, p1307_1]
                                      · have p1307_0 := h1307c.1
                                        have p1307_1 := h1307c.2.1
                                        have p1307_2 := h1307c.2.2.1
                                        have p1307_3 := h1307c.2.2.2
                                        linarith only [h423, hlam, p1307_0]
                                      · have p1307_0 := h1307c.1
                                        have p1307_1 := h1307c.2.1
                                        have p1307_2 := h1307c.2.2.1
                                        have p1307_3 := h1307c.2.2.2
                                        linarith only [h820, hlam, p1307_1]
                                      · have p1307_0 := h1307c.1
                                        have p1307_1 := h1307c.2.1
                                        have p1307_2 := h1307c.2.2.1
                                        have p1307_3 := h1307c.2.2.2
                                        linarith only [h964, hlam, p1307_1]
                                      · have p1307_0 := h1307c.1
                                        have p1307_1 := h1307c.2.1
                                        have p1307_2 := h1307c.2.2.1
                                        have p1307_3 := h1307c.2.2.2
                                        linarith only [h1258, h1299, hc01, hc14, hlam, hphi, p1307_1]
                                      · have p1307_0 := h1307c.1
                                        have p1307_1 := h1307c.2.1
                                        have p1307_2 := h1307c.2.2.1
                                        have p1307_3 := h1307c.2.2.2
                                        linarith only [hlam, p1307_0]
                                      · have p1307_0 := h1307c.1
                                        have p1307_1 := h1307c.2.1
                                        have p1307_2 := h1307c.2.2.1
                                        have p1307_3 := h1307c.2.2.2
                                        linarith only [h1121, hlam, p1307_0]
                                      · have p1307_0 := h1307c.1
                                        have p1307_1 := h1307c.2.1
                                        have p1307_2 := h1307c.2.2.1
                                        have p1307_3 := h1307c.2.2.2
                                        linarith only [h1258, hlam, p1307_1]
                                      · have p1307_0 := h1307c.1
                                        have p1307_1 := h1307c.2.1
                                        have p1307_2 := h1307c.2.2.1
                                        have p1307_3 := h1307c.2.2.2
                                        linarith only [h1258, h1299, h964, hc01, hc14, hlam, hphi, p1307_1]
                                      · have p1307_0 := h1307c.1
                                        have p1307_1 := h1307c.2.1
                                        have p1307_2 := h1307c.2.2.1
                                        have p1307_3 := h1307c.2.2.2
                                        linarith only [h423, hc01, hlam, hphi, ht12, ht23, p1307_1, u3elo1]
                                      · have p1307_0 := h1307c.1
                                        have p1307_1 := h1307c.2.1
                                        have p1307_2 := h1307c.2.2.1
                                        have p1307_3 := h1307c.2.2.2
                                        linarith only [h1121, h1294, h1298, h1304, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1307_1, u3elo1]
                                      · have p1307_0 := h1307c.1
                                        have p1307_1 := h1307c.2.1
                                        have p1307_2 := h1307c.2.2.1
                                        have p1307_3 := h1307c.2.2.2
                                        linarith only [hlam, p1307_0]
                                      · have p1307_0 := h1307c.1
                                        have p1307_1 := h1307c.2.1
                                        have p1307_2 := h1307c.2.2.1
                                        have p1307_3 := h1307c.2.2.2
                                        linarith only [h1121, h1258, h1294, h1298, h1304, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1307_1, u3elo1]
                                      · have p1307_0 := h1307c.1
                                        have p1307_1 := h1307c.2.1
                                        have p1307_2 := h1307c.2.2.1
                                        have p1307_3 := h1307c.2.2.2
                                        linarith only [h1121, h1298, h964, hc01, hlam, hphi, ht12, ht23, p1307_1, u3elo1]
                                      · have p1307_0 := h1307c.1
                                        have p1307_1 := h1307c.2.1
                                        have p1307_2 := h1307c.2.2.1
                                        have p1307_3 := h1307c.2.2.2
                                        linarith only [h1121, h1295, h1298, hc01, hlam, hphi, ht12, ht23, p1307_1, u3elo1]
                                      · have p1307_0 := h1307c.1
                                        have p1307_1 := h1307c.2.1
                                        have p1307_2 := h1307c.2.2.1
                                        have p1307_3 := h1307c.2.2.2
                                        linarith only [h1294, h1304, hc35, hlam, hphi, ht0b, ht5b, p1307_1, u0elo3]
                                      · have p1307_0 := h1307c.1
                                        have p1307_1 := h1307c.2.1
                                        have p1307_2 := h1307c.2.2.1
                                        have p1307_3 := h1307c.2.2.2
                                        linarith only [h1295, hlam, p1307_0]
                                      · have p1307_0 := h1307c.1
                                        have p1307_1 := h1307c.2.1
                                        have p1307_2 := h1307c.2.2.1
                                        have p1307_3 := h1307c.2.2.2
                                        linarith only [hlam, p1307_0]
                                      · have p1307_0 := h1307c.1
                                        have p1307_1 := h1307c.2.1
                                        have p1307_2 := h1307c.2.2.1
                                        have p1307_3 := h1307c.2.2.2
                                        linarith only [h1121, h1295, h1298, h964, hc01, hlam, hphi, ht12, ht23, p1307_1, u3elo1]
                                      · have p1307_0 := h1307c.1
                                        have p1307_1 := h1307c.2.1
                                        have p1307_2 := h1307c.2.2.1
                                        have p1307_3 := h1307c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1307_1, u5elo0]
                                      · have p1307_0 := h1307c.1
                                        have p1307_1 := h1307c.2.1
                                        have p1307_2 := h1307c.2.2.1
                                        have p1307_3 := h1307c.2.2.2
                                        linarith only [h1294, hlam, p1307_1]
                                      · have p1307_0 := h1307c.1
                                        have p1307_1 := h1307c.2.1
                                        have p1307_2 := h1307c.2.2.1
                                        have p1307_3 := h1307c.2.2.2
                                        linarith only [h1296, hlam, p1307_0]
                                      · have p1307_0 := h1307c.1
                                        have p1307_1 := h1307c.2.1
                                        have p1307_2 := h1307c.2.2.1
                                        have p1307_3 := h1307c.2.2.2
                                        linarith only [h1297, hlam, p1307_1]
                                      · have p1307_0 := h1307c.1
                                        have p1307_1 := h1307c.2.1
                                        have p1307_2 := h1307c.2.2.1
                                        have p1307_3 := h1307c.2.2.2
                                        linarith only [hlam, p1307_0]
                                    · linarith only [h1258, h1294, h1299, h1301, h1305, h1306, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                  · linarith only [h1258, h1305, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                                · linarith only [h1121, h1304, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                              · linarith only [h1121, h1303, hc02, hlam, hphi, ht23, u3elo3]
                            · linarith only [h1121, h1294, h1297, h1302, h820, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h1121, h1295, h1298, h1301, hlam]
                        · linarith only [h0, h1300, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h1121, h1298, h1299, hc02, hc24, hlam, hphi]
                    · linarith only [h0, h1298, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h1258, h1294, h1297, hc25, hlam, hphi, u5elo4]
                · linarith only [h1121, h1294, h1296, hc25, hlam, hphi, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1344 | h1344
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1345 | h1345
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1346 | h1346
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1347 | h1347
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1348 | h1348
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1349 | h1349
                          · linarith only [h1121, h1294, h1295, h1349, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                          · linarith only [h1349, h423, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h1121, h1294, h1346, h1348, hlam]
                      · linarith only [h1121, h1294, h1346, h1347, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h0, h1346, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h1121, h1294, h1295, h1345, hc25, hlam, hphi, u5elo4]
                · linarith only [h1121, h1294, h1344, hc25, hlam, hphi, u5elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1357 | h1357
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1358 | h1358
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1359 | h1359
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1360 | h1360
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1361 | h1361
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1362 | h1362
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1363 | h1363
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1364 | h1364
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1365 | h1365
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1366 | h1366
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1367 | h1367
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1368 | h1368
                                    · rcases h0bigk with h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c | h1369c
                                      · have p1369_0 := h1369c.1
                                        have p1369_1 := h1369c.2.1
                                        have p1369_2 := h1369c.2.2.1
                                        have p1369_3 := h1369c.2.2.2
                                        linarith only [hlam, p1369_0]
                                      · have p1369_0 := h1369c.1
                                        have p1369_1 := h1369c.2.1
                                        have p1369_2 := h1369c.2.2.1
                                        have p1369_3 := h1369c.2.2.2
                                        linarith only [h0, hlam, p1369_1]
                                      · have p1369_0 := h1369c.1
                                        have p1369_1 := h1369c.2.1
                                        have p1369_2 := h1369c.2.2.1
                                        have p1369_3 := h1369c.2.2.2
                                        linarith only [h423, hlam, p1369_0]
                                      · have p1369_0 := h1369c.1
                                        have p1369_1 := h1369c.2.1
                                        have p1369_2 := h1369c.2.2.1
                                        have p1369_3 := h1369c.2.2.2
                                        linarith only [h820, hlam, p1369_1]
                                      · have p1369_0 := h1369c.1
                                        have p1369_1 := h1369c.2.1
                                        have p1369_2 := h1369c.2.2.1
                                        have p1369_3 := h1369c.2.2.2
                                        linarith only [h964, hlam, p1369_1]
                                      · have p1369_0 := h1369c.1
                                        have p1369_1 := h1369c.2.1
                                        have p1369_2 := h1369c.2.2.1
                                        have p1369_3 := h1369c.2.2.2
                                        linarith only [h1121, h1294, h1357, h1360, h1362, h1368, hc01, hc45, hlam, hphi, ht12, ht23, p1369_1, u3elo1, u5elo1]
                                      · have p1369_0 := h1369c.1
                                        have p1369_1 := h1369c.2.1
                                        have p1369_2 := h1369c.2.2.1
                                        have p1369_3 := h1369c.2.2.2
                                        linarith only [hlam, p1369_0]
                                      · have p1369_0 := h1369c.1
                                        have p1369_1 := h1369c.2.1
                                        have p1369_2 := h1369c.2.2.1
                                        have p1369_3 := h1369c.2.2.2
                                        linarith only [h1121, hlam, p1369_0]
                                      · have p1369_0 := h1369c.1
                                        have p1369_1 := h1369c.2.1
                                        have p1369_2 := h1369c.2.2.1
                                        have p1369_3 := h1369c.2.2.2
                                        linarith only [h1258, hlam, p1369_1]
                                      · have p1369_0 := h1369c.1
                                        have p1369_1 := h1369c.2.1
                                        have p1369_2 := h1369c.2.2.1
                                        have p1369_3 := h1369c.2.2.2
                                        linarith only [h1294, hlam, p1369_0]
                                      · have p1369_0 := h1369c.1
                                        have p1369_1 := h1369c.2.1
                                        have p1369_2 := h1369c.2.2.1
                                        have p1369_3 := h1369c.2.2.2
                                        linarith only [h1121, h1360, hc01, hlam, hphi, ht12, ht23, p1369_1, u3elo1]
                                      · have p1369_0 := h1369c.1
                                        have p1369_1 := h1369c.2.1
                                        have p1369_2 := h1369c.2.2.1
                                        have p1369_3 := h1369c.2.2.2
                                        linarith only [h1121, h1360, hc02, hlam, hphi, ht23, p1369_1, u3elo1]
                                      · have p1369_0 := h1369c.1
                                        have p1369_1 := h1369c.2.1
                                        have p1369_2 := h1369c.2.2.1
                                        have p1369_3 := h1369c.2.2.2
                                        linarith only [hlam, p1369_0]
                                      · have p1369_0 := h1369c.1
                                        have p1369_1 := h1369c.2.1
                                        have p1369_2 := h1369c.2.2.1
                                        have p1369_3 := h1369c.2.2.2
                                        linarith only [h1121, h1357, h1360, h1368, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1369_1, u3elo1]
                                      · have p1369_0 := h1369c.1
                                        have p1369_1 := h1369c.2.1
                                        have p1369_2 := h1369c.2.2.1
                                        have p1369_3 := h1369c.2.2.2
                                        linarith only [h0, h1121, h1294, h1360, hc01, hlam, hphi, ht12, ht23, p1369_1, u3elo1]
                                      · have p1369_0 := h1369c.1
                                        have p1369_1 := h1369c.2.1
                                        have p1369_2 := h1369c.2.2.1
                                        have p1369_3 := h1369c.2.2.2
                                        linarith only [h1363, h820, hc01, hlam, hphi, ht12, ht23, p1369_1, u3elo1]
                                      · have p1369_0 := h1369c.1
                                        have p1369_1 := h1369c.2.1
                                        have p1369_2 := h1369c.2.2.1
                                        have p1369_3 := h1369c.2.2.2
                                        linarith only [h0, h1258, h1361, h1363, hc01, hlam, hphi, ht12, ht23, p1369_1, u3elo1]
                                      · have p1369_0 := h1369c.1
                                        have p1369_1 := h1369c.2.1
                                        have p1369_2 := h1369c.2.2.1
                                        have p1369_3 := h1369c.2.2.2
                                        linarith only [h1357, hlam, p1369_0]
                                      · have p1369_0 := h1369c.1
                                        have p1369_1 := h1369c.2.1
                                        have p1369_2 := h1369c.2.2.1
                                        have p1369_3 := h1369c.2.2.2
                                        linarith only [hlam, p1369_0]
                                      · have p1369_0 := h1369c.1
                                        have p1369_1 := h1369c.2.1
                                        have p1369_2 := h1369c.2.2.1
                                        have p1369_3 := h1369c.2.2.2
                                        linarith only [h0, h1258, h1294, h1361, h1363, hc01, hlam, hphi, ht12, ht23, p1369_1, u3elo1]
                                      · have p1369_0 := h1369c.1
                                        have p1369_1 := h1369c.2.1
                                        have p1369_2 := h1369c.2.2.1
                                        have p1369_3 := h1369c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1369_1, u5elo0]
                                      · have p1369_0 := h1369c.1
                                        have p1369_1 := h1369c.2.1
                                        have p1369_2 := h1369c.2.2.1
                                        have p1369_3 := h1369c.2.2.2
                                        linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1369_1, u5elo0]
                                      · have p1369_0 := h1369c.1
                                        have p1369_1 := h1369c.2.1
                                        have p1369_2 := h1369c.2.2.1
                                        have p1369_3 := h1369c.2.2.2
                                        linarith only [h1358, hlam, p1369_0]
                                      · have p1369_0 := h1369c.1
                                        have p1369_1 := h1369c.2.1
                                        have p1369_2 := h1369c.2.2.1
                                        have p1369_3 := h1369c.2.2.2
                                        linarith only [h1359, hlam, p1369_1]
                                      · have p1369_0 := h1369c.1
                                        have p1369_1 := h1369c.2.1
                                        have p1369_2 := h1369c.2.2.1
                                        have p1369_3 := h1369c.2.2.2
                                        linarith only [hlam, p1369_0]
                                    · rcases h0bigk with h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c
                                      · have p1395_0 := h1395c.1
                                        have p1395_1 := h1395c.2.1
                                        have p1395_2 := h1395c.2.2.1
                                        have p1395_3 := h1395c.2.2.2
                                        linarith only [hlam, p1395_0]
                                      · have p1395_0 := h1395c.1
                                        have p1395_1 := h1395c.2.1
                                        have p1395_2 := h1395c.2.2.1
                                        have p1395_3 := h1395c.2.2.2
                                        linarith only [h0, hlam, p1395_1]
                                      · have p1395_0 := h1395c.1
                                        have p1395_1 := h1395c.2.1
                                        have p1395_2 := h1395c.2.2.1
                                        have p1395_3 := h1395c.2.2.2
                                        linarith only [h423, hlam, p1395_0]
                                      · have p1395_0 := h1395c.1
                                        have p1395_1 := h1395c.2.1
                                        have p1395_2 := h1395c.2.2.1
                                        have p1395_3 := h1395c.2.2.2
                                        linarith only [h820, hlam, p1395_1]
                                      · have p1395_0 := h1395c.1
                                        have p1395_1 := h1395c.2.1
                                        have p1395_2 := h1395c.2.2.1
                                        have p1395_3 := h1395c.2.2.2
                                        linarith only [h964, hlam, p1395_1]
                                      · have p1395_0 := h1395c.1
                                        have p1395_1 := h1395c.2.1
                                        have p1395_2 := h1395c.2.2.1
                                        have p1395_3 := h1395c.2.2.2
                                        linarith only [h1121, h1360, hc01, hlam, hphi, ht12, ht23, p1395_1, u3elo1]
                                      · have p1395_0 := h1395c.1
                                        have p1395_1 := h1395c.2.1
                                        have p1395_2 := h1395c.2.2.1
                                        have p1395_3 := h1395c.2.2.2
                                        linarith only [hlam, p1395_0]
                                      · have p1395_0 := h1395c.1
                                        have p1395_1 := h1395c.2.1
                                        have p1395_2 := h1395c.2.2.1
                                        have p1395_3 := h1395c.2.2.2
                                        linarith only [h1121, hlam, p1395_0]
                                      · have p1395_0 := h1395c.1
                                        have p1395_1 := h1395c.2.1
                                        have p1395_2 := h1395c.2.2.1
                                        have p1395_3 := h1395c.2.2.2
                                        linarith only [h1258, hlam, p1395_1]
                                      · have p1395_0 := h1395c.1
                                        have p1395_1 := h1395c.2.1
                                        have p1395_2 := h1395c.2.2.1
                                        have p1395_3 := h1395c.2.2.2
                                        linarith only [h1294, hlam, p1395_0]
                                      · have p1395_0 := h1395c.1
                                        have p1395_1 := h1395c.2.1
                                        have p1395_2 := h1395c.2.2.1
                                        have p1395_3 := h1395c.2.2.2
                                        linarith only [h1121, h1360, hc01, hlam, hphi, ht12, ht23, p1395_1, u3elo1]
                                      · have p1395_0 := h1395c.1
                                        have p1395_1 := h1395c.2.1
                                        have p1395_2 := h1395c.2.2.1
                                        have p1395_3 := h1395c.2.2.2
                                        linarith only [h1121, h1360, hc02, hlam, hphi, ht23, p1395_1, u3elo1]
                                      · have p1395_0 := h1395c.1
                                        have p1395_1 := h1395c.2.1
                                        have p1395_2 := h1395c.2.2.1
                                        have p1395_3 := h1395c.2.2.2
                                        linarith only [hlam, p1395_0]
                                      · have p1395_0 := h1395c.1
                                        have p1395_1 := h1395c.2.1
                                        have p1395_2 := h1395c.2.2.1
                                        have p1395_3 := h1395c.2.2.2
                                        linarith only [h1121, h1359, h1360, h1368, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1395_1, u3elo1]
                                      · have p1395_0 := h1395c.1
                                        have p1395_1 := h1395c.2.1
                                        have p1395_2 := h1395c.2.2.1
                                        have p1395_3 := h1395c.2.2.2
                                        linarith only [h1121, h1360, h964, hc01, hlam, hphi, ht12, ht23, p1395_1, u3elo1]
                                      · have p1395_0 := h1395c.1
                                        have p1395_1 := h1395c.2.1
                                        have p1395_2 := h1395c.2.2.1
                                        have p1395_3 := h1395c.2.2.2
                                        linarith only [h1121, h1357, h1360, hc01, hlam, hphi, ht12, ht23, p1395_1, u3elo1]
                                      · have p1395_0 := h1395c.1
                                        have p1395_1 := h1395c.2.1
                                        have p1395_2 := h1395c.2.2.1
                                        have p1395_3 := h1395c.2.2.2
                                        linarith only [h0, h1121, h1357, h1360, hc01, hlam, hphi, ht12, ht23, p1395_1, u3elo1]
                                      · have p1395_0 := h1395c.1
                                        have p1395_1 := h1395c.2.1
                                        have p1395_2 := h1395c.2.2.1
                                        have p1395_3 := h1395c.2.2.2
                                        linarith only [h1357, hlam, p1395_0]
                                      · have p1395_0 := h1395c.1
                                        have p1395_1 := h1395c.2.1
                                        have p1395_2 := h1395c.2.2.1
                                        have p1395_3 := h1395c.2.2.2
                                        linarith only [hlam, p1395_0]
                                      · have p1395_0 := h1395c.1
                                        have p1395_1 := h1395c.2.1
                                        have p1395_2 := h1395c.2.2.1
                                        have p1395_3 := h1395c.2.2.2
                                        linarith only [h0, h1121, h1294, h1357, h1360, hc01, hlam, hphi, ht12, ht23, p1395_1, u3elo1]
                                      · have p1395_0 := h1395c.1
                                        have p1395_1 := h1395c.2.1
                                        have p1395_2 := h1395c.2.2.1
                                        have p1395_3 := h1395c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1395_1, u5elo0]
                                      · have p1395_0 := h1395c.1
                                        have p1395_1 := h1395c.2.1
                                        have p1395_2 := h1395c.2.2.1
                                        have p1395_3 := h1395c.2.2.2
                                        linarith only [h0, h964, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1395_1, u5elo1]
                                      · have p1395_0 := h1395c.1
                                        have p1395_1 := h1395c.2.1
                                        have p1395_2 := h1395c.2.2.1
                                        have p1395_3 := h1395c.2.2.2
                                        linarith only [h1358, hlam, p1395_0]
                                      · have p1395_0 := h1395c.1
                                        have p1395_1 := h1395c.2.1
                                        have p1395_2 := h1395c.2.2.1
                                        have p1395_3 := h1395c.2.2.2
                                        linarith only [h1359, hlam, p1395_1]
                                      · have p1395_0 := h1395c.1
                                        have p1395_1 := h1395c.2.1
                                        have p1395_2 := h1395c.2.2.1
                                        have p1395_3 := h1395c.2.2.2
                                        linarith only [hlam, p1395_0]
                                  · linarith only [h1258, h1359, h1367, hlam]
                                · linarith only [h1121, h1357, h1359, h1366, hc45, hlam, hphi, u5elo3]
                              · linarith only [h0, h1121, h1365, hc01, hlam, hphi, ht12, ht23, u3elo3]
                            · linarith only [h1357, h1359, h1364, h423, h820, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h1121, h1357, h1360, h1363, hlam]
                        · linarith only [h0, h1362, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h1121, h1360, h1361, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h1360, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1429 | h1429
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1430 | h1430
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1431 | h1431
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1432 | h1432
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1433 | h1433
                            · linarith only [h1359, h1432, h1433, h820, hc01, hlam, hphi, ht12, ht23, u3elo1]
                            · linarith only [h1433, h820, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                          · linarith only [h1357, h1429, h1432, hc23, hlam, hphi, u3elo0]
                        · linarith only [h1121, h1429, h1431, hc03, hlam, hphi, ht34, ht45, u5elo2]
                      · linarith only [h0, h1121, h1429, h1430, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h1429, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h1357, h1358, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1441 | h1441
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1442 | h1442
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1443 | h1443
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1444 | h1444
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1445 | h1445
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1446 | h1446
                          · linarith only [h1357, h1441, h1446, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                          · linarith only [h1446, h423, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h1444, h1445, hc24, hlam, hphi, ht45, u5elo2]
                      · linarith only [h0, h1121, h1443, h1444, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h1443, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h1357, h1441, h1442, hc35, hlam, hphi, u5elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1453 | h1453
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1454 | h1454
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1455 | h1455
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1456 | h1456
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1457 | h1457
                          · linarith only [h1357, h1457, hc03, hlam, hphi, u3elo1]
                          · linarith only [h1457, h423, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h1121, h1454, h1456, hc01, hc25, hlam, hphi, ht12]
                      · linarith only [h0, h1121, h1454, h1455, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h1454, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1463 | h1463
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1464 | h1464
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1465 | h1465
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1466 | h1466
                          · linarith only [h0, h1121, h1357, h1466, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h1466, h423, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h1121, h1463, h1465, hc01, hc25, hlam, hphi, ht12]
                      · linarith only [h0, h1121, h1463, h1464, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h1463, hc01, hlam, hphi, ht12, ht23, u3elo2]

theorem r1l7_20_12_13_15_M_LI_L_I_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h3elo := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_13_15_M_LI_L_I_L_0_L_0_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_20_12_13_15_M_LI_L_I_L_0_L_0_x1 m hb0 hb2 hb3 hb5 h0

end R2N4
