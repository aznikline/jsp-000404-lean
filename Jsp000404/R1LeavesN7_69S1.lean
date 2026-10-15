import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_69S0

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_0_L_I_L_I_H_L_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0elo := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h419 | h419
  · rcases m.htr 0 2 3 (by decide) (by decide) with h420 | h420
    · rcases m.htr 0 2 4 (by decide) (by decide) with h421 | h421
      · rcases m.htr 0 2 5 (by decide) (by decide) with h422 | h422
        · rcases m.htr 0 3 4 (by decide) (by decide) with h423 | h423
          · rcases m.htr 0 3 5 (by decide) (by decide) with h424 | h424
            · rcases m.htr 1 2 3 (by decide) (by decide) with h425 | h425
              · rcases m.htr 1 2 4 (by decide) (by decide) with h426 | h426
                · rcases m.htr 1 2 5 (by decide) (by decide) with h427 | h427
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h428 | h428
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h429 | h429
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h430 | h430
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h431 | h431
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h432 | h432
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h433 | h433
                              · linarith only [h419, h425, h430, h433, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                              · linarith only [h433, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h432, hc24, hlam, hphi, ht45, u5elo4]
                          · linarith only [h431, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h0, h419, h428, h430, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h429, hc13, hlam, hphi, ht34, ht45, u5elo3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h440 | h440
                      · linarith only [h0, h419, h423, h428, h440, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                      · linarith only [h440, hc13, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h0, h422, h427, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
                · linarith only [h0, h421, h426, hlam]
              · linarith only [h0, h420, h425, hlam]
            · linarith only [h423, h424, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h447 | h447
            · rcases m.htr 1 2 3 (by decide) (by decide) with h448 | h448
              · rcases m.htr 1 2 4 (by decide) (by decide) with h449 | h449
                · rcases m.htr 1 2 5 (by decide) (by decide) with h450 | h450
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h451 | h451
                    · linarith only [h419, h423, h447, h451, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h453 | h453
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h454 | h454
                        · linarith only [h419, h423, h448, h454, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h456 | h456
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h457 | h457
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h458 | h458
                              · rcases h2bigk with h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [hlam, p459_0]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [h0, hlam, p459_1]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [h456, h458, hc45, hlam, hphi, ht0b, ht5b, p459_1, u0elo1]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [h454, h456, h458, hc45, hlam, hphi, ht0b, ht5b, p459_1, u0elo1]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  rcases p459_3 (m.d 0 2) (by simp) with h464 | h464
                                  · rcases p459_3 (m.d 1 2) (by simp) with h465 | h465
                                    · rcases p459_3 (m.d 2 3) (by simp) with h466 | h466
                                      · linarith only [h420, h466, hlam]
                                      · linarith only [h456, h466, hlam]
                                    · linarith only [h450, h465, hlam]
                                  · linarith only [h464, hlam, p459_0]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [h0, h419, h448, h456, h458, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p459_1]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [hlam, p459_0]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  rcases p459_3 (m.d 0 2) (by simp) with h473 | h473
                                  · linarith only [h0, h473, hlam]
                                  · linarith only [h420, h473, hlam]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  rcases p459_3 (m.d 0 2) (by simp) with h476 | h476
                                  · linarith only [h0, h476, hlam]
                                  · linarith only [h421, h476, hlam]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  rcases p459_3 (m.d 0 2) (by simp) with h479 | h479
                                  · linarith only [h0, h479, hlam]
                                  · linarith only [h422, h479, hlam]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [h420, hlam, p459_0]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [h448, hlam, p459_0]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [hlam, p459_0]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [h454, hlam, p459_0]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [h419, h448, hc25, hlam, hphi, ht0b, ht5b, p459_1, u0elo0]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [h421, hlam, p459_0]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [h449, hlam, p459_0]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [h421, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p459_1, u0elo1]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [hlam, p459_0]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [h421, h456, h458, hc45, hlam, hphi, ht0b, ht5b, p459_1, u0elo1]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [h422, hlam, p459_0]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [h450, hlam, p459_0]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [h456, hlam, p459_1]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [h457, hlam, p459_0]
                                · have p459_0 := h459c.1
                                  have p459_1 := h459c.2.1
                                  have p459_2 := h459c.2.2.1
                                  have p459_3 := h459c.2.2.2
                                  linarith only [hlam, p459_0]
                              · linarith only [h423, h458, hc03, hlam, hphi, ht34, ht45, u5elo4]
                            · linarith only [h457, hc24, hlam, hphi, ht45, u5elo4]
                          · linarith only [h456, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h447, h453, hc13, hlam, hphi, ht34, ht45, u5elo0]
                  · linarith only [h450, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                · linarith only [h0, h421, h449, hlam]
              · linarith only [h0, h420, h448, hlam]
            · linarith only [h447, hc03, hlam, hphi, ht34, ht45, u5elo3]
        · linarith only [h422, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h506 | h506
        · rcases m.htr 0 3 4 (by decide) (by decide) with h507 | h507
          · linarith only [h0, h419, h421, h507, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h509 | h509
            · rcases m.htr 1 2 3 (by decide) (by decide) with h510 | h510
              · rcases m.htr 1 2 4 (by decide) (by decide) with h511 | h511
                · rcases m.htr 1 2 5 (by decide) (by decide) with h512 | h512
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h513 | h513
                    · linarith only [h0, h419, h421, h507, h511, h513, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h515 | h515
                      · linarith only [h0, h419, h421, h511, h515, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h510, h515, hc23, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h421, h506, h511, h512, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h519 | h519
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h520 | h520
                    · linarith only [h0, h419, h507, h520, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h522 | h522
                      · linarith only [h0, h419, h511, h522, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h522, hc13, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h0, h506, h519, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
              · linarith only [h0, h419, h420, h510, hlam]
            · linarith only [h509, hc03, hlam, hphi, ht34, ht45, u5elo3]
        · linarith only [h506, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
    · linarith only [h0, h419, h420, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h530 | h530
    · rcases m.htr 0 2 4 (by decide) (by decide) with h531 | h531
      · rcases m.htr 0 2 5 (by decide) (by decide) with h532 | h532
        · rcases m.htr 0 3 4 (by decide) (by decide) with h533 | h533
          · rcases m.htr 0 3 5 (by decide) (by decide) with h534 | h534
            · rcases m.htr 1 2 3 (by decide) (by decide) with h535 | h535
              · rcases m.htr 1 2 4 (by decide) (by decide) with h536 | h536
                · rcases m.htr 1 2 5 (by decide) (by decide) with h537 | h537
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h538 | h538
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h539 | h539
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h540 | h540
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h541 | h541
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h542 | h542
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h543 | h543
                              · linarith only [h530, h540, h543, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                              · linarith only [h543, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h542, hc24, hlam, hphi, ht45, u5elo4]
                          · linarith only [h541, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h548 | h548
                          · linarith only [h533, h540, h548, hc35, hlam, hphi, ht0b, ht5b, u0elo2]
                          · linarith only [h548, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h419, h534, h539, hc03, hlam, hphi, ht34, ht45, u5elo0]
                    · linarith only [h419, h533, h538, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h0, h532, h537, hc02, hlam, hphi, ht23, ht34, ht45, u5elo0]
                · linarith only [h419, h531, h535, h536, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h530, h535, hlam]
            · linarith only [h533, h534, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h557 | h557
            · rcases m.htr 1 2 3 (by decide) (by decide) with h558 | h558
              · rcases m.htr 1 2 4 (by decide) (by decide) with h559 | h559
                · rcases m.htr 1 2 5 (by decide) (by decide) with h560 | h560
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h561 | h561
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h562 | h562
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h563 | h563
                        · linarith only [h530, h533, h563, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h565 | h565
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h566 | h566
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h567 | h567
                              · rcases h2bigk with h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h0, hlam, p568_1]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h565, h567, hc45, hlam, hphi, ht0b, ht5b, p568_1, u0elo1]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h563, h565, h567, hc45, hlam, hphi, ht0b, ht5b, p568_1, u0elo1]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  rcases p568_3 (m.d 0 2) (by simp) with h573 | h573
                                  · rcases p568_3 (m.d 1 2) (by simp) with h574 | h574
                                    · rcases p568_3 (m.d 2 3) (by simp) with h575 | h575
                                      · linarith only [h530, h575, hlam]
                                      · linarith only [h565, h575, hlam]
                                    · linarith only [h560, h574, hlam]
                                  · linarith only [h573, hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h530, h565, h567, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p568_1]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  rcases p568_3 (m.d 0 2) (by simp) with h582 | h582
                                  · linarith only [h0, h582, hlam]
                                  · linarith only [h530, h582, hlam]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  rcases p568_3 (m.d 0 2) (by simp) with h585 | h585
                                  · linarith only [h0, h585, hlam]
                                  · linarith only [h531, h585, hlam]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  rcases p568_3 (m.d 0 2) (by simp) with h588 | h588
                                  · linarith only [h0, h588, hlam]
                                  · linarith only [h532, h588, hlam]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h530, hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h558, hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h563, hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h531, h563, hc25, hlam, hphi, ht0b, ht5b, p568_1, u0elo1]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h531, hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h559, hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h531, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p568_1, u0elo1]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h531, h565, h567, hc45, hlam, hphi, ht0b, ht5b, p568_1, u0elo1]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h532, hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h560, hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h565, hlam, p568_1]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h566, hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [hlam, p568_0]
                              · linarith only [h533, h567, hc03, hlam, hphi, ht34, ht45, u5elo4]
                            · linarith only [h566, hc24, hlam, hphi, ht45, u5elo4]
                          · linarith only [h565, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h533, h557, h561, h562, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h610 | h610
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h611 | h611
                        · linarith only [h419, h561, h611, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h613 | h613
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h614 | h614
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h615 | h615
                              · rcases h2bigk with h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c
                                · have p616_0 := h616c.1
                                  have p616_1 := h616c.2.1
                                  have p616_2 := h616c.2.2.1
                                  have p616_3 := h616c.2.2.2
                                  linarith only [hlam, p616_0]
                                · have p616_0 := h616c.1
                                  have p616_1 := h616c.2.1
                                  have p616_2 := h616c.2.2.1
                                  have p616_3 := h616c.2.2.2
                                  linarith only [h0, hlam, p616_1]
                                · have p616_0 := h616c.1
                                  have p616_1 := h616c.2.1
                                  have p616_2 := h616c.2.2.1
                                  have p616_3 := h616c.2.2.2
                                  linarith only [h613, h615, hc45, hlam, hphi, ht0b, ht5b, p616_1, u0elo1]
                                · have p616_0 := h616c.1
                                  have p616_1 := h616c.2.1
                                  have p616_2 := h616c.2.2.1
                                  have p616_3 := h616c.2.2.2
                                  linarith only [h611, h613, h615, hc45, hlam, hphi, ht0b, ht5b, p616_1, u0elo1]
                                · have p616_0 := h616c.1
                                  have p616_1 := h616c.2.1
                                  have p616_2 := h616c.2.2.1
                                  have p616_3 := h616c.2.2.2
                                  rcases p616_3 (m.d 0 2) (by simp) with h621 | h621
                                  · rcases p616_3 (m.d 1 2) (by simp) with h622 | h622
                                    · rcases p616_3 (m.d 2 3) (by simp) with h623 | h623
                                      · linarith only [h530, h623, hlam]
                                      · linarith only [h613, h623, hlam]
                                    · linarith only [h560, h622, hlam]
                                  · linarith only [h621, hlam, p616_0]
                                · have p616_0 := h616c.1
                                  have p616_1 := h616c.2.1
                                  have p616_2 := h616c.2.2.1
                                  have p616_3 := h616c.2.2.2
                                  linarith only [h530, h613, h615, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p616_1]
                                · have p616_0 := h616c.1
                                  have p616_1 := h616c.2.1
                                  have p616_2 := h616c.2.2.1
                                  have p616_3 := h616c.2.2.2
                                  linarith only [hlam, p616_0]
                                · have p616_0 := h616c.1
                                  have p616_1 := h616c.2.1
                                  have p616_2 := h616c.2.2.1
                                  have p616_3 := h616c.2.2.2
                                  rcases p616_3 (m.d 0 2) (by simp) with h630 | h630
                                  · linarith only [h0, h630, hlam]
                                  · linarith only [h530, h630, hlam]
                                · have p616_0 := h616c.1
                                  have p616_1 := h616c.2.1
                                  have p616_2 := h616c.2.2.1
                                  have p616_3 := h616c.2.2.2
                                  rcases p616_3 (m.d 0 2) (by simp) with h633 | h633
                                  · linarith only [h0, h633, hlam]
                                  · linarith only [h531, h633, hlam]
                                · have p616_0 := h616c.1
                                  have p616_1 := h616c.2.1
                                  have p616_2 := h616c.2.2.1
                                  have p616_3 := h616c.2.2.2
                                  rcases p616_3 (m.d 0 2) (by simp) with h636 | h636
                                  · linarith only [h0, h636, hlam]
                                  · linarith only [h532, h636, hlam]
                                · have p616_0 := h616c.1
                                  have p616_1 := h616c.2.1
                                  have p616_2 := h616c.2.2.1
                                  have p616_3 := h616c.2.2.2
                                  linarith only [h530, hlam, p616_0]
                                · have p616_0 := h616c.1
                                  have p616_1 := h616c.2.1
                                  have p616_2 := h616c.2.2.1
                                  have p616_3 := h616c.2.2.2
                                  linarith only [h558, hlam, p616_0]
                                · have p616_0 := h616c.1
                                  have p616_1 := h616c.2.1
                                  have p616_2 := h616c.2.2.1
                                  have p616_3 := h616c.2.2.2
                                  linarith only [hlam, p616_0]
                                · have p616_0 := h616c.1
                                  have p616_1 := h616c.2.1
                                  have p616_2 := h616c.2.2.1
                                  have p616_3 := h616c.2.2.2
                                  linarith only [h611, hlam, p616_0]
                                · have p616_0 := h616c.1
                                  have p616_1 := h616c.2.1
                                  have p616_2 := h616c.2.2.1
                                  have p616_3 := h616c.2.2.2
                                  linarith only [h531, h611, h613, h615, hc45, hlam, hphi, ht0b, ht5b, p616_1, u0elo1]
                                · have p616_0 := h616c.1
                                  have p616_1 := h616c.2.1
                                  have p616_2 := h616c.2.2.1
                                  have p616_3 := h616c.2.2.2
                                  linarith only [h531, hlam, p616_0]
                                · have p616_0 := h616c.1
                                  have p616_1 := h616c.2.1
                                  have p616_2 := h616c.2.2.1
                                  have p616_3 := h616c.2.2.2
                                  linarith only [h559, hlam, p616_0]
                                · have p616_0 := h616c.1
                                  have p616_1 := h616c.2.1
                                  have p616_2 := h616c.2.2.1
                                  have p616_3 := h616c.2.2.2
                                  linarith only [h531, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p616_1, u0elo1]
                                · have p616_0 := h616c.1
                                  have p616_1 := h616c.2.1
                                  have p616_2 := h616c.2.2.1
                                  have p616_3 := h616c.2.2.2
                                  linarith only [hlam, p616_0]
                                · have p616_0 := h616c.1
                                  have p616_1 := h616c.2.1
                                  have p616_2 := h616c.2.2.1
                                  have p616_3 := h616c.2.2.2
                                  linarith only [h531, h613, h615, hc45, hlam, hphi, ht0b, ht5b, p616_1, u0elo1]
                                · have p616_0 := h616c.1
                                  have p616_1 := h616c.2.1
                                  have p616_2 := h616c.2.2.1
                                  have p616_3 := h616c.2.2.2
                                  linarith only [h532, hlam, p616_0]
                                · have p616_0 := h616c.1
                                  have p616_1 := h616c.2.1
                                  have p616_2 := h616c.2.2.1
                                  have p616_3 := h616c.2.2.2
                                  linarith only [h560, hlam, p616_0]
                                · have p616_0 := h616c.1
                                  have p616_1 := h616c.2.1
                                  have p616_2 := h616c.2.2.1
                                  have p616_3 := h616c.2.2.2
                                  linarith only [h613, hlam, p616_1]
                                · have p616_0 := h616c.1
                                  have p616_1 := h616c.2.1
                                  have p616_2 := h616c.2.2.1
                                  have p616_3 := h616c.2.2.2
                                  linarith only [h614, hlam, p616_0]
                                · have p616_0 := h616c.1
                                  have p616_1 := h616c.2.1
                                  have p616_2 := h616c.2.2.1
                                  have p616_3 := h616c.2.2.2
                                  linarith only [hlam, p616_0]
                              · linarith only [h419, h561, h615, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                            · linarith only [h614, hc24, hlam, hphi, ht45, u5elo4]
                          · linarith only [h613, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h419, h557, h610, hlam]
                  · linarith only [h532, h560, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
                · linarith only [h0, h531, h559, hlam]
              · linarith only [h0, h530, h558, hlam]
            · linarith only [h557, hc03, hlam, hphi, ht34, ht45, u5elo3]
        · linarith only [h532, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h663 | h663
        · rcases m.htr 0 3 4 (by decide) (by decide) with h664 | h664
          · linarith only [h530, h531, h664, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h666 | h666
            · rcases m.htr 1 2 3 (by decide) (by decide) with h667 | h667
              · rcases m.htr 1 2 4 (by decide) (by decide) with h668 | h668
                · rcases m.htr 1 2 5 (by decide) (by decide) with h669 | h669
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h670 | h670
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h671 | h671
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h672 | h672
                        · linarith only [h530, h664, h672, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h674 | h674
                          · linarith only [h530, h531, h667, h670, h672, h674, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h674, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h530, h531, h666, h670, h671, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h678 | h678
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h679 | h679
                        · linarith only [h530, h531, h668, h670, h679, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h681 | h681
                          · linarith only [h530, h531, h668, h681, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h681, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h419, h530, h531, h666, h668, h678, hc01, hc12, hlam, hphi]
                  · linarith only [h531, h663, h668, h669, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h686 | h686
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h687 | h687
                    · linarith only [h664, h666, h667, h668, h687, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h689 | h689
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h690 | h690
                        · linarith only [h530, h664, h690, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h692 | h692
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h693 | h693
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h694 | h694
                              · rcases h2bigk with h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c
                                · have p695_0 := h695c.1
                                  have p695_1 := h695c.2.1
                                  have p695_2 := h695c.2.2.1
                                  have p695_3 := h695c.2.2.2
                                  linarith only [hlam, p695_0]
                                · have p695_0 := h695c.1
                                  have p695_1 := h695c.2.1
                                  have p695_2 := h695c.2.2.1
                                  have p695_3 := h695c.2.2.2
                                  linarith only [h0, hlam, p695_1]
                                · have p695_0 := h695c.1
                                  have p695_1 := h695c.2.1
                                  have p695_2 := h695c.2.2.1
                                  have p695_3 := h695c.2.2.2
                                  linarith only [h0, h668, h690, hc23, hc34, hlam, hphi, p695_1]
                                · have p695_0 := h695c.1
                                  have p695_1 := h695c.2.1
                                  have p695_2 := h695c.2.2.1
                                  have p695_3 := h695c.2.2.2
                                  linarith only [h531, hlam, p695_0]
                                · have p695_0 := h695c.1
                                  have p695_1 := h695c.2.1
                                  have p695_2 := h695c.2.2.1
                                  have p695_3 := h695c.2.2.2
                                  rcases p695_3 (m.d 0 2) (by simp) with h700 | h700
                                  · rcases p695_3 (m.d 1 2) (by simp) with h701 | h701
                                    · rcases p695_3 (m.d 2 3) (by simp) with h702 | h702
                                      · linarith only [h530, h702, hlam]
                                      · linarith only [h692, h702, hlam]
                                    · linarith only [h686, h701, hlam]
                                  · linarith only [h700, hlam, p695_0]
                                · have p695_0 := h695c.1
                                  have p695_1 := h695c.2.1
                                  have p695_2 := h695c.2.2.1
                                  have p695_3 := h695c.2.2.2
                                  linarith only [h668, h690, hc02, hc34, hlam, hphi, ht23, p695_1]
                                · have p695_0 := h695c.1
                                  have p695_1 := h695c.2.1
                                  have p695_2 := h695c.2.2.1
                                  have p695_3 := h695c.2.2.2
                                  linarith only [hlam, p695_0]
                                · have p695_0 := h695c.1
                                  have p695_1 := h695c.2.1
                                  have p695_2 := h695c.2.2.1
                                  have p695_3 := h695c.2.2.2
                                  linarith only [h668, h690, h692, h694, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p695_1]
                                · have p695_0 := h695c.1
                                  have p695_1 := h695c.2.1
                                  have p695_2 := h695c.2.2.1
                                  have p695_3 := h695c.2.2.2
                                  linarith only [h668, hlam, p695_0]
                                · have p695_0 := h695c.1
                                  have p695_1 := h695c.2.1
                                  have p695_2 := h695c.2.2.1
                                  have p695_3 := h695c.2.2.2
                                  rcases p695_3 (m.d 0 2) (by simp) with h711 | h711
                                  · linarith only [h0, h711, hlam]
                                  · linarith only [h663, h711, hlam]
                                · have p695_0 := h695c.1
                                  have p695_1 := h695c.2.1
                                  have p695_2 := h695c.2.2.1
                                  have p695_3 := h695c.2.2.2
                                  linarith only [h530, hlam, p695_0]
                                · have p695_0 := h695c.1
                                  have p695_1 := h695c.2.1
                                  have p695_2 := h695c.2.2.1
                                  have p695_3 := h695c.2.2.2
                                  linarith only [h667, hlam, p695_0]
                                · have p695_0 := h695c.1
                                  have p695_1 := h695c.2.1
                                  have p695_2 := h695c.2.2.1
                                  have p695_3 := h695c.2.2.2
                                  linarith only [hlam, p695_0]
                                · have p695_0 := h695c.1
                                  have p695_1 := h695c.2.1
                                  have p695_2 := h695c.2.2.1
                                  have p695_3 := h695c.2.2.2
                                  linarith only [h690, hlam, p695_0]
                                · have p695_0 := h695c.1
                                  have p695_1 := h695c.2.1
                                  have p695_2 := h695c.2.2.1
                                  have p695_3 := h695c.2.2.2
                                  linarith only [h530, h692, h694, hc45, hlam, hphi, ht0b, ht5b, p695_1, u0elo1]
                                · have p695_0 := h695c.1
                                  have p695_1 := h695c.2.1
                                  have p695_2 := h695c.2.2.1
                                  have p695_3 := h695c.2.2.2
                                  linarith only [h530, h690, hc23, hc34, hlam, hphi, p695_1]
                                · have p695_0 := h695c.1
                                  have p695_1 := h695c.2.1
                                  have p695_2 := h695c.2.2.1
                                  have p695_3 := h695c.2.2.2
                                  linarith only [h0, h690, hc01, hc34, hlam, hphi, ht12, ht23, p695_1]
                                · have p695_0 := h695c.1
                                  have p695_1 := h695c.2.1
                                  have p695_2 := h695c.2.2.1
                                  have p695_3 := h695c.2.2.2
                                  rcases p695_3 (m.d 0 2) (by simp) with h721 | h721
                                  · linarith only [h531, h721, hlam]
                                  · linarith only [h530, h721, hlam]
                                · have p695_0 := h695c.1
                                  have p695_1 := h695c.2.1
                                  have p695_2 := h695c.2.2.1
                                  have p695_3 := h695c.2.2.2
                                  linarith only [hlam, p695_0]
                                · have p695_0 := h695c.1
                                  have p695_1 := h695c.2.1
                                  have p695_2 := h695c.2.2.1
                                  have p695_3 := h695c.2.2.2
                                  rcases p695_3 (m.d 0 2) (by simp) with h725 | h725
                                  · linarith only [h531, h725, hlam]
                                  · linarith only [h663, h725, hlam]
                                · have p695_0 := h695c.1
                                  have p695_1 := h695c.2.1
                                  have p695_2 := h695c.2.2.1
                                  have p695_3 := h695c.2.2.2
                                  linarith only [h663, hlam, p695_0]
                                · have p695_0 := h695c.1
                                  have p695_1 := h695c.2.1
                                  have p695_2 := h695c.2.2.1
                                  have p695_3 := h695c.2.2.2
                                  linarith only [h686, hlam, p695_0]
                                · have p695_0 := h695c.1
                                  have p695_1 := h695c.2.1
                                  have p695_2 := h695c.2.2.1
                                  have p695_3 := h695c.2.2.2
                                  linarith only [h692, hlam, p695_1]
                                · have p695_0 := h695c.1
                                  have p695_1 := h695c.2.1
                                  have p695_2 := h695c.2.2.1
                                  have p695_3 := h695c.2.2.2
                                  linarith only [h693, hlam, p695_0]
                                · have p695_0 := h695c.1
                                  have p695_1 := h695c.2.1
                                  have p695_2 := h695c.2.2.1
                                  have p695_3 := h695c.2.2.2
                                  linarith only [hlam, p695_0]
                              · linarith only [h694, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h0, h668, h693, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                          · linarith only [h692, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h419, h530, h666, h689, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h663, h686, hc02, hlam, hphi, ht23, ht34, ht45, u5elo0]
              · linarith only [h0, h530, h667, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h666, hc03, hlam, hphi, ht34, ht45, u5elo3]
        · linarith only [h663, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h741 | h741
      · rcases m.htr 0 2 5 (by decide) (by decide) with h742 | h742
        · rcases m.htr 0 3 4 (by decide) (by decide) with h743 | h743
          · rcases m.htr 0 3 5 (by decide) (by decide) with h744 | h744
            · rcases m.htr 1 2 3 (by decide) (by decide) with h745 | h745
              · rcases m.htr 1 2 4 (by decide) (by decide) with h746 | h746
                · rcases m.htr 1 2 5 (by decide) (by decide) with h747 | h747
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h748 | h748
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h749 | h749
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h750 | h750
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h751 | h751
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h752 | h752
                            · linarith only [h530, h741, h745, h752, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h752, hc24, hlam, hphi, ht45, u5elo4]
                          · linarith only [h530, h741, h750, h751, hc34, hlam, hphi, ht45, u5elo3]
                        · linarith only [h530, h741, h743, h750, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h530, h744, h745, h749, hc03, hlam, hphi, ht34, ht45, u5elo0]
                    · linarith only [h530, h741, h743, h745, h748, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · linarith only [h530, h742, h745, h747, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h530, h745, h746, hc02, hc24, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h761 | h761
                · rcases m.htr 1 2 5 (by decide) (by decide) with h762 | h762
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h763 | h763
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h764 | h764
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h765 | h765
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h766 | h766
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h767 | h767
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h768 | h768
                              · rcases h2bigk with h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c
                                · have p769_0 := h769c.1
                                  have p769_1 := h769c.2.1
                                  have p769_2 := h769c.2.2.1
                                  have p769_3 := h769c.2.2.2
                                  linarith only [hlam, p769_0]
                                · have p769_0 := h769c.1
                                  have p769_1 := h769c.2.1
                                  have p769_2 := h769c.2.2.1
                                  have p769_3 := h769c.2.2.2
                                  linarith only [h0, hlam, p769_1]
                                · have p769_0 := h769c.1
                                  have p769_1 := h769c.2.1
                                  have p769_2 := h769c.2.2.1
                                  have p769_3 := h769c.2.2.2
                                  linarith only [h530, hlam, p769_0]
                                · have p769_0 := h769c.1
                                  have p769_1 := h769c.2.1
                                  have p769_2 := h769c.2.2.1
                                  have p769_3 := h769c.2.2.2
                                  linarith only [h765, h768, hc45, hlam, hphi, ht0b, ht5b, p769_1, u0elo1]
                                · have p769_0 := h769c.1
                                  have p769_1 := h769c.2.1
                                  have p769_2 := h769c.2.2.1
                                  have p769_3 := h769c.2.2.2
                                  rcases p769_3 (m.d 0 2) (by simp) with h774 | h774
                                  · rcases p769_3 (m.d 1 2) (by simp) with h775 | h775
                                    · rcases p769_3 (m.d 2 3) (by simp) with h776 | h776
                                      · rcases p769_3 (m.d 2 4) (by simp) with h777 | h777
                                        · linarith only [h741, h777, hlam]
                                        · linarith only [h767, h777, hlam]
                                      · linarith only [h766, h776, hlam]
                                    · linarith only [h762, h775, hlam]
                                  · linarith only [h774, hlam, p769_0]
                                · have p769_0 := h769c.1
                                  have p769_1 := h769c.2.1
                                  have p769_2 := h769c.2.2.1
                                  have p769_3 := h769c.2.2.2
                                  linarith only [h745, hc02, hc23, hlam, hphi, p769_1]
                                · have p769_0 := h769c.1
                                  have p769_1 := h769c.2.1
                                  have p769_2 := h769c.2.2.1
                                  have p769_3 := h769c.2.2.2
                                  linarith only [hlam, p769_0]
                                · have p769_0 := h769c.1
                                  have p769_1 := h769c.2.1
                                  have p769_2 := h769c.2.2.1
                                  have p769_3 := h769c.2.2.2
                                  linarith only [h745, hlam, p769_0]
                                · have p769_0 := h769c.1
                                  have p769_1 := h769c.2.1
                                  have p769_2 := h769c.2.2.1
                                  have p769_3 := h769c.2.2.2
                                  linarith only [h745, h765, h768, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p769_1]
                                · have p769_0 := h769c.1
                                  have p769_1 := h769c.2.1
                                  have p769_2 := h769c.2.2.1
                                  have p769_3 := h769c.2.2.2
                                  rcases p769_3 (m.d 0 2) (by simp) with h787 | h787
                                  · linarith only [h0, h787, hlam]
                                  · linarith only [h742, h787, hlam]
                                · have p769_0 := h769c.1
                                  have p769_1 := h769c.2.1
                                  have p769_2 := h769c.2.2.1
                                  have p769_3 := h769c.2.2.2
                                  linarith only [h741, h765, h768, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p769_1]
                                · have p769_0 := h769c.1
                                  have p769_1 := h769c.2.1
                                  have p769_2 := h769c.2.2.1
                                  have p769_3 := h769c.2.2.2
                                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p769_1]
                                · have p769_0 := h769c.1
                                  have p769_1 := h769c.2.1
                                  have p769_2 := h769c.2.2.1
                                  have p769_3 := h769c.2.2.2
                                  linarith only [hlam, p769_0]
                                · have p769_0 := h769c.1
                                  have p769_1 := h769c.2.1
                                  have p769_2 := h769c.2.2.1
                                  have p769_3 := h769c.2.2.2
                                  rcases p769_3 (m.d 0 2) (by simp) with h793 | h793
                                  · linarith only [h530, h793, hlam]
                                  · linarith only [h741, h793, hlam]
                                · have p769_0 := h769c.1
                                  have p769_1 := h769c.2.1
                                  have p769_2 := h769c.2.2.1
                                  have p769_3 := h769c.2.2.2
                                  rcases p769_3 (m.d 0 2) (by simp) with h796 | h796
                                  · linarith only [h530, h796, hlam]
                                  · linarith only [h742, h796, hlam]
                                · have p769_0 := h769c.1
                                  have p769_1 := h769c.2.1
                                  have p769_2 := h769c.2.2.1
                                  have p769_3 := h769c.2.2.2
                                  linarith only [h741, hlam, p769_0]
                                · have p769_0 := h769c.1
                                  have p769_1 := h769c.2.1
                                  have p769_2 := h769c.2.2.1
                                  have p769_3 := h769c.2.2.2
                                  linarith only [h761, hlam, p769_0]
                                · have p769_0 := h769c.1
                                  have p769_1 := h769c.2.1
                                  have p769_2 := h769c.2.2.1
                                  have p769_3 := h769c.2.2.2
                                  linarith only [h765, hlam, p769_1]
                                · have p769_0 := h769c.1
                                  have p769_1 := h769c.2.1
                                  have p769_2 := h769c.2.2.1
                                  have p769_3 := h769c.2.2.2
                                  linarith only [hlam, p769_0]
                                · have p769_0 := h769c.1
                                  have p769_1 := h769c.2.1
                                  have p769_2 := h769c.2.2.1
                                  have p769_3 := h769c.2.2.2
                                  linarith only [h741, hc25, hlam, hphi, ht0b, ht5b, p769_1, u0elo1]
                                · have p769_0 := h769c.1
                                  have p769_1 := h769c.2.1
                                  have p769_2 := h769c.2.2.1
                                  have p769_3 := h769c.2.2.2
                                  linarith only [h742, hlam, p769_0]
                                · have p769_0 := h769c.1
                                  have p769_1 := h769c.2.1
                                  have p769_2 := h769c.2.2.1
                                  have p769_3 := h769c.2.2.2
                                  linarith only [h762, hlam, p769_0]
                                · have p769_0 := h769c.1
                                  have p769_1 := h769c.2.1
                                  have p769_2 := h769c.2.2.1
                                  have p769_3 := h769c.2.2.2
                                  linarith only [h766, hlam, p769_1]
                                · have p769_0 := h769c.1
                                  have p769_1 := h769c.2.1
                                  have p769_2 := h769c.2.2.1
                                  have p769_3 := h769c.2.2.2
                                  linarith only [h767, hlam, p769_0]
                                · have p769_0 := h769c.1
                                  have p769_1 := h769c.2.1
                                  have p769_2 := h769c.2.2.1
                                  have p769_3 := h769c.2.2.2
                                  linarith only [hlam, p769_0]
                              · linarith only [h768, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h767, hc24, hlam, hphi, ht45, u5elo4]
                          · linarith only [h0, h745, h766, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                        · linarith only [h419, h743, h745, h765, hlam]
                      · linarith only [h419, h744, h764, hc03, hlam, hphi, ht34, ht45, u5elo0]
                    · linarith only [h0, h743, h745, h763, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h0, h762, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                · linarith only [h0, h741, h761, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h744, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · linarith only [h530, h741, h743, hlam]
        · linarith only [h742, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h820 | h820
        · rcases m.htr 0 3 4 (by decide) (by decide) with h821 | h821
          · rcases m.htr 0 3 5 (by decide) (by decide) with h822 | h822
            · rcases m.htr 1 2 3 (by decide) (by decide) with h823 | h823
              · rcases m.htr 1 2 4 (by decide) (by decide) with h824 | h824
                · rcases m.htr 1 2 5 (by decide) (by decide) with h825 | h825
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h826 | h826
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h827 | h827
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h828 | h828
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h829 | h829
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h830 | h830
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h831 | h831
                              · rcases h2bigk with h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c
                                · have p832_0 := h832c.1
                                  have p832_1 := h832c.2.1
                                  have p832_2 := h832c.2.2.1
                                  have p832_3 := h832c.2.2.2
                                  linarith only [hlam, p832_0]
                                · have p832_0 := h832c.1
                                  have p832_1 := h832c.2.1
                                  have p832_2 := h832c.2.2.1
                                  have p832_3 := h832c.2.2.2
                                  linarith only [h0, hlam, p832_1]
                                · have p832_0 := h832c.1
                                  have p832_1 := h832c.2.1
                                  have p832_2 := h832c.2.2.1
                                  have p832_3 := h832c.2.2.2
                                  linarith only [h530, hlam, p832_0]
                                · have p832_0 := h832c.1
                                  have p832_1 := h832c.2.1
                                  have p832_2 := h832c.2.2.1
                                  have p832_3 := h832c.2.2.2
                                  linarith only [h741, hlam, p832_0]
                                · have p832_0 := h832c.1
                                  have p832_1 := h832c.2.1
                                  have p832_2 := h832c.2.2.1
                                  have p832_3 := h832c.2.2.2
                                  linarith only [h530, h823, h829, h831, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p832_1]
                                · have p832_0 := h832c.1
                                  have p832_1 := h832c.2.1
                                  have p832_2 := h832c.2.2.1
                                  have p832_3 := h832c.2.2.2
                                  rcases p832_3 (m.d 0 2) (by simp) with h838 | h838
                                  · linarith only [h0, h838, hlam]
                                  · rcases p832_3 (m.d 1 2) (by simp) with h840 | h840
                                    · rcases p832_3 (m.d 2 3) (by simp) with h841 | h841
                                      · linarith only [h823, h841, hlam]
                                      · linarith only [h530, h841, hlam]
                                    · linarith only [h0, h840, hlam]
                                · have p832_0 := h832c.1
                                  have p832_1 := h832c.2.1
                                  have p832_2 := h832c.2.2.1
                                  have p832_3 := h832c.2.2.2
                                  linarith only [hlam, p832_0]
                                · have p832_0 := h832c.1
                                  have p832_1 := h832c.2.1
                                  have p832_2 := h832c.2.2.1
                                  have p832_3 := h832c.2.2.2
                                  linarith only [h0, h741, h828, hc01, hc12, hlam, hphi, p832_1]
                                · have p832_0 := h832c.1
                                  have p832_1 := h832c.2.1
                                  have p832_2 := h832c.2.2.1
                                  have p832_3 := h832c.2.2.2
                                  linarith only [h741, h820, h829, h831, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p832_1]
                                · have p832_0 := h832c.1
                                  have p832_1 := h832c.2.1
                                  have p832_2 := h832c.2.2.1
                                  have p832_3 := h832c.2.2.2
                                  linarith only [h530, h820, h823, hlam, p832_2]
                                · have p832_0 := h832c.1
                                  have p832_1 := h832c.2.1
                                  have p832_2 := h832c.2.2.1
                                  have p832_3 := h832c.2.2.2
                                  linarith only [h820, h823, h829, h831, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p832_1]
                                · have p832_0 := h832c.1
                                  have p832_1 := h832c.2.1
                                  have p832_2 := h832c.2.2.1
                                  have p832_3 := h832c.2.2.2
                                  linarith only [h823, hlam, p832_0]
                                · have p832_0 := h832c.1
                                  have p832_1 := h832c.2.1
                                  have p832_2 := h832c.2.2.1
                                  have p832_3 := h832c.2.2.2
                                  linarith only [hlam, p832_0]
                                · have p832_0 := h832c.1
                                  have p832_1 := h832c.2.1
                                  have p832_2 := h832c.2.2.1
                                  have p832_3 := h832c.2.2.2
                                  linarith only [h741, h820, h823, h829, h831, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p832_1]
                                · have p832_0 := h832c.1
                                  have p832_1 := h832c.2.1
                                  have p832_2 := h832c.2.2.1
                                  have p832_3 := h832c.2.2.2
                                  rcases p832_3 (m.d 0 2) (by simp) with h853 | h853
                                  · linarith only [h530, h853, hlam]
                                  · linarith only [h820, h853, hlam]
                                · have p832_0 := h832c.1
                                  have p832_1 := h832c.2.1
                                  have p832_2 := h832c.2.2.1
                                  have p832_3 := h832c.2.2.2
                                  linarith only [h820, h824, h829, h831, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p832_1]
                                · have p832_0 := h832c.1
                                  have p832_1 := h832c.2.1
                                  have p832_2 := h832c.2.2.1
                                  have p832_3 := h832c.2.2.2
                                  linarith only [h824, hlam, p832_0]
                                · have p832_0 := h832c.1
                                  have p832_1 := h832c.2.1
                                  have p832_2 := h832c.2.2.1
                                  have p832_3 := h832c.2.2.2
                                  linarith only [h828, hlam, p832_1]
                                · have p832_0 := h832c.1
                                  have p832_1 := h832c.2.1
                                  have p832_2 := h832c.2.2.1
                                  have p832_3 := h832c.2.2.2
                                  linarith only [hlam, p832_0]
                                · have p832_0 := h832c.1
                                  have p832_1 := h832c.2.1
                                  have p832_2 := h832c.2.2.1
                                  have p832_3 := h832c.2.2.2
                                  rcases p832_3 (m.d 0 2) (by simp) with h860 | h860
                                  · linarith only [h741, h860, hlam]
                                  · linarith only [h820, h860, hlam]
                                · have p832_0 := h832c.1
                                  have p832_1 := h832c.2.1
                                  have p832_2 := h832c.2.2.1
                                  have p832_3 := h832c.2.2.2
                                  linarith only [h820, hlam, p832_0]
                                · have p832_0 := h832c.1
                                  have p832_1 := h832c.2.1
                                  have p832_2 := h832c.2.2.1
                                  have p832_3 := h832c.2.2.2
                                  linarith only [h825, hlam, p832_0]
                                · have p832_0 := h832c.1
                                  have p832_1 := h832c.2.1
                                  have p832_2 := h832c.2.2.1
                                  have p832_3 := h832c.2.2.2
                                  linarith only [h829, hlam, p832_1]
                                · have p832_0 := h832c.1
                                  have p832_1 := h832c.2.1
                                  have p832_2 := h832c.2.2.1
                                  have p832_3 := h832c.2.2.2
                                  linarith only [h830, hlam, p832_0]
                                · have p832_0 := h832c.1
                                  have p832_1 := h832c.2.1
                                  have p832_2 := h832c.2.2.1
                                  have p832_3 := h832c.2.2.2
                                  linarith only [hlam, p832_0]
                              · linarith only [h831, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h741, h830, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                          · linarith only [h741, h820, h828, h829, hc25, hlam, hphi, u5elo3]
                        · linarith only [h530, h821, h828, hlam]
                      · linarith only [h741, h820, h822, h824, h826, h827, hc25, hlam, hphi, u5elo0]
                    · linarith only [h419, h821, h826, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h530, h820, h823, h825, hlam]
                · linarith only [h530, h823, h824, hc02, hc24, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h876 | h876
                · linarith only [h741, h820, h823, h876, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h878 | h878
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h879 | h879
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h880 | h880
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h881 | h881
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h882 | h882
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h883 | h883
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h884 | h884
                              · rcases h2bigk with h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c
                                · have p885_0 := h885c.1
                                  have p885_1 := h885c.2.1
                                  have p885_2 := h885c.2.2.1
                                  have p885_3 := h885c.2.2.2
                                  linarith only [hlam, p885_0]
                                · have p885_0 := h885c.1
                                  have p885_1 := h885c.2.1
                                  have p885_2 := h885c.2.2.1
                                  have p885_3 := h885c.2.2.2
                                  linarith only [h0, hlam, p885_1]
                                · have p885_0 := h885c.1
                                  have p885_1 := h885c.2.1
                                  have p885_2 := h885c.2.2.1
                                  have p885_3 := h885c.2.2.2
                                  linarith only [h530, hlam, p885_0]
                                · have p885_0 := h885c.1
                                  have p885_1 := h885c.2.1
                                  have p885_2 := h885c.2.2.1
                                  have p885_3 := h885c.2.2.2
                                  linarith only [h741, hlam, p885_0]
                                · have p885_0 := h885c.1
                                  have p885_1 := h885c.2.1
                                  have p885_2 := h885c.2.2.1
                                  have p885_3 := h885c.2.2.2
                                  rcases p885_3 (m.d 0 2) (by simp) with h890 | h890
                                  · rcases p885_3 (m.d 1 2) (by simp) with h891 | h891
                                    · rcases p885_3 (m.d 2 3) (by simp) with h892 | h892
                                      · rcases p885_3 (m.d 2 4) (by simp) with h893 | h893
                                        · rcases p885_3 (m.d 2 5) (by simp) with h894 | h894
                                          · linarith only [h894, hlam, p885_0]
                                          · rcases h3bigk with h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c
                                            · have p896_0 := h896c.1
                                              have p896_1 := h896c.2.1
                                              have p896_2 := h896c.2.2.1
                                              have p896_3 := h896c.2.2.2
                                              linarith only [hlam, p896_0]
                                            · have p896_0 := h896c.1
                                              have p896_1 := h896c.2.1
                                              have p896_2 := h896c.2.2.1
                                              have p896_3 := h896c.2.2.2
                                              linarith only [h419, hlam, p896_1]
                                            · have p896_0 := h896c.1
                                              have p896_1 := h896c.2.1
                                              have p896_2 := h896c.2.2.1
                                              have p896_3 := h896c.2.2.2
                                              linarith only [h530, hlam, p896_1]
                                            · have p896_0 := h896c.1
                                              have p896_1 := h896c.2.1
                                              have p896_2 := h896c.2.2.1
                                              have p896_3 := h896c.2.2.2
                                              linarith only [h884, hc45, hlam, hphi, ht0b, ht5b, p896_1, u0elo2]
                                            · have p896_0 := h896c.1
                                              have p896_1 := h896c.2.1
                                              have p896_2 := h896c.2.2.1
                                              have p896_3 := h896c.2.2.2
                                              rcases p896_3 (m.d 0 3) (by simp) with h901 | h901
                                              · rcases p896_3 (m.d 1 3) (by simp) with h902 | h902
                                                · rcases p896_3 (m.d 2 3) (by simp) with h903 | h903
                                                  · rcases p896_3 (m.d 3 4) (by simp) with h904 | h904
                                                    · linarith only [h821, h904, hlam]
                                                    · linarith only [h884, h904, hlam]
                                                  · linarith only [h882, h903, hlam]
                                                · linarith only [h880, h902, hlam]
                                              · linarith only [h901, hlam, p896_0]
                                            · have p896_0 := h896c.1
                                              have p896_1 := h896c.2.1
                                              have p896_2 := h896c.2.2.1
                                              have p896_3 := h896c.2.2.2
                                              linarith only [h530, h882, h884, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p885_1, p896_1]
                                            · have p896_0 := h896c.1
                                              have p896_1 := h896c.2.1
                                              have p896_2 := h896c.2.2.1
                                              have p896_3 := h896c.2.2.2
                                              linarith only [hlam, p896_0]
                                            · have p896_0 := h896c.1
                                              have p896_1 := h896c.2.1
                                              have p896_2 := h896c.2.2.1
                                              have p896_3 := h896c.2.2.2
                                              linarith only [h823, hlam, p896_1]
                                            · have p896_0 := h896c.1
                                              have p896_1 := h896c.2.1
                                              have p896_2 := h896c.2.2.1
                                              have p896_3 := h896c.2.2.2
                                              rcases p896_3 (m.d 0 3) (by simp) with h913 | h913
                                              · linarith only [h419, h913, hlam]
                                              · linarith only [h821, h913, hlam]
                                            · have p896_0 := h896c.1
                                              have p896_1 := h896c.2.1
                                              have p896_2 := h896c.2.2.1
                                              have p896_3 := h896c.2.2.2
                                              rcases p896_3 (m.d 0 3) (by simp) with h916 | h916
                                              · linarith only [h419, h916, hlam]
                                              · linarith only [h822, h916, hlam]
                                            · have p896_0 := h896c.1
                                              have p896_1 := h896c.2.1
                                              have p896_2 := h896c.2.2.1
                                              have p896_3 := h896c.2.2.2
                                              linarith only [h741, h821, h882, h884, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p885_1, p896_1]
                                            · have p896_0 := h896c.1
                                              have p896_1 := h896c.2.1
                                              have p896_2 := h896c.2.2.1
                                              have p896_3 := h896c.2.2.2
                                              linarith only [h419, hc01, hc23, hlam, hphi, ht12, p896_1]
                                            · have p896_0 := h896c.1
                                              have p896_1 := h896c.2.1
                                              have p896_2 := h896c.2.2.1
                                              have p896_3 := h896c.2.2.2
                                              linarith only [hlam, p896_0]
                                            · have p896_0 := h896c.1
                                              have p896_1 := h896c.2.1
                                              have p896_2 := h896c.2.2.1
                                              have p896_3 := h896c.2.2.2
                                              rcases p896_3 (m.d 0 3) (by simp) with h922 | h922
                                              · linarith only [h530, h922, hlam]
                                              · linarith only [h821, h922, hlam]
                                            · have p896_0 := h896c.1
                                              have p896_1 := h896c.2.1
                                              have p896_2 := h896c.2.2.1
                                              have p896_3 := h896c.2.2.2
                                              linarith only [h0, h876, h881, h882, hlam, p885_1, p896_2]
                                            · have p896_0 := h896c.1
                                              have p896_1 := h896c.2.1
                                              have p896_2 := h896c.2.2.1
                                              have p896_3 := h896c.2.2.2
                                              linarith only [h821, hlam, p896_0]
                                            · have p896_0 := h896c.1
                                              have p896_1 := h896c.2.1
                                              have p896_2 := h896c.2.2.1
                                              have p896_3 := h896c.2.2.2
                                              linarith only [h879, hlam, p896_0]
                                            · have p896_0 := h896c.1
                                              have p896_1 := h896c.2.1
                                              have p896_2 := h896c.2.2.1
                                              have p896_3 := h896c.2.2.2
                                              linarith only [h881, hlam, p896_0]
                                            · have p896_0 := h896c.1
                                              have p896_1 := h896c.2.1
                                              have p896_2 := h896c.2.2.1
                                              have p896_3 := h896c.2.2.2
                                              linarith only [hlam, p896_0]
                                            · have p896_0 := h896c.1
                                              have p896_1 := h896c.2.1
                                              have p896_2 := h896c.2.2.1
                                              have p896_3 := h896c.2.2.2
                                              linarith only [h821, h884, hc45, hlam, hphi, ht0b, ht5b, p896_1, u0elo2]
                                            · have p896_0 := h896c.1
                                              have p896_1 := h896c.2.1
                                              have p896_2 := h896c.2.2.1
                                              have p896_3 := h896c.2.2.2
                                              linarith only [h822, hlam, p896_0]
                                            · have p896_0 := h896c.1
                                              have p896_1 := h896c.2.1
                                              have p896_2 := h896c.2.2.1
                                              have p896_3 := h896c.2.2.2
                                              linarith only [h880, hlam, p896_0]
                                            · have p896_0 := h896c.1
                                              have p896_1 := h896c.2.1
                                              have p896_2 := h896c.2.2.1
                                              have p896_3 := h896c.2.2.2
                                              linarith only [h882, hlam, p896_0]
                                            · have p896_0 := h896c.1
                                              have p896_1 := h896c.2.1
                                              have p896_2 := h896c.2.2.1
                                              have p896_3 := h896c.2.2.2
                                              linarith only [h884, hlam, p896_0]
                                            · have p896_0 := h896c.1
                                              have p896_1 := h896c.2.1
                                              have p896_2 := h896c.2.2.1
                                              have p896_3 := h896c.2.2.2
                                              linarith only [hlam, p896_0]
                                        · linarith only [h883, h893, hlam]
                                      · linarith only [h882, h892, hlam]
                                    · linarith only [h878, h891, hlam]
                                  · linarith only [h890, hlam, p885_0]
                                · have p885_0 := h885c.1
                                  have p885_1 := h885c.2.1
                                  have p885_2 := h885c.2.2.1
                                  have p885_3 := h885c.2.2.2
                                  linarith only [h876, h881, hc02, hc23, hlam, hphi, p885_1]
                                · have p885_0 := h885c.1
                                  have p885_1 := h885c.2.1
                                  have p885_2 := h885c.2.2.1
                                  have p885_3 := h885c.2.2.2
                                  linarith only [hlam, p885_0]
                                · have p885_0 := h885c.1
                                  have p885_1 := h885c.2.1
                                  have p885_2 := h885c.2.2.1
                                  have p885_3 := h885c.2.2.2
                                  linarith only [h823, hlam, p885_0]
                                · have p885_0 := h885c.1
                                  have p885_1 := h885c.2.1
                                  have p885_2 := h885c.2.2.1
                                  have p885_3 := h885c.2.2.2
                                  linarith only [h876, hlam, p885_0]
                                · have p885_0 := h885c.1
                                  have p885_1 := h885c.2.1
                                  have p885_2 := h885c.2.2.1
                                  have p885_3 := h885c.2.2.2
                                  rcases p885_3 (m.d 0 2) (by simp) with h944 | h944
                                  · linarith only [h0, h944, hlam]
                                  · linarith only [h820, h944, hlam]
                                · have p885_0 := h885c.1
                                  have p885_1 := h885c.2.1
                                  have p885_2 := h885c.2.2.1
                                  have p885_3 := h885c.2.2.2
                                  rcases p885_3 (m.d 0 2) (by simp) with h947 | h947
                                  · linarith only [h947, hlam, p885_0]
                                  · rcases p885_3 (m.d 1 2) (by simp) with h949 | h949
                                    · linarith only [h823, h949, hlam]
                                    · linarith only [h0, h949, hlam]
                                · have p885_0 := h885c.1
                                  have p885_1 := h885c.2.1
                                  have p885_2 := h885c.2.2.1
                                  have p885_3 := h885c.2.2.2
                                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p885_1]
                                · have p885_0 := h885c.1
                                  have p885_1 := h885c.2.1
                                  have p885_2 := h885c.2.2.1
                                  have p885_3 := h885c.2.2.2
                                  linarith only [hlam, p885_0]
                                · have p885_0 := h885c.1
                                  have p885_1 := h885c.2.1
                                  have p885_2 := h885c.2.2.1
                                  have p885_3 := h885c.2.2.2
                                  linarith only [h741, h820, h882, h884, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p885_1]
                                · have p885_0 := h885c.1
                                  have p885_1 := h885c.2.1
                                  have p885_2 := h885c.2.2.1
                                  have p885_3 := h885c.2.2.2
                                  rcases p885_3 (m.d 0 2) (by simp) with h955 | h955
                                  · linarith only [h530, h955, hlam]
                                  · linarith only [h820, h955, hlam]
                                · have p885_0 := h885c.1
                                  have p885_1 := h885c.2.1
                                  have p885_2 := h885c.2.2.1
                                  have p885_3 := h885c.2.2.2
                                  rcases p885_3 (m.d 0 2) (by simp) with h958 | h958
                                  · linarith only [h958, hlam, p885_0]
                                  · rcases p885_3 (m.d 1 2) (by simp) with h960 | h960
                                    · linarith only [h876, h960, hlam]
                                    · linarith only [h0, h960, hlam]
                                · have p885_0 := h885c.1
                                  have p885_1 := h885c.2.1
                                  have p885_2 := h885c.2.2.1
                                  have p885_3 := h885c.2.2.2
                                  linarith only [h0, h881, hc01, hc23, hlam, hphi, ht12, p885_1]
                                · have p885_0 := h885c.1
                                  have p885_1 := h885c.2.1
                                  have p885_2 := h885c.2.2.1
                                  have p885_3 := h885c.2.2.2
                                  linarith only [h881, hlam, p885_1]
                                · have p885_0 := h885c.1
                                  have p885_1 := h885c.2.1
                                  have p885_2 := h885c.2.2.1
                                  have p885_3 := h885c.2.2.2
                                  linarith only [hlam, p885_0]
                                · have p885_0 := h885c.1
                                  have p885_1 := h885c.2.1
                                  have p885_2 := h885c.2.2.1
                                  have p885_3 := h885c.2.2.2
                                  rcases p885_3 (m.d 0 2) (by simp) with h966 | h966
                                  · linarith only [h741, h966, hlam]
                                  · linarith only [h820, h966, hlam]
                                · have p885_0 := h885c.1
                                  have p885_1 := h885c.2.1
                                  have p885_2 := h885c.2.2.1
                                  have p885_3 := h885c.2.2.2
                                  linarith only [h820, hlam, p885_0]
                                · have p885_0 := h885c.1
                                  have p885_1 := h885c.2.1
                                  have p885_2 := h885c.2.2.1
                                  have p885_3 := h885c.2.2.2
                                  linarith only [h878, hlam, p885_0]
                                · have p885_0 := h885c.1
                                  have p885_1 := h885c.2.1
                                  have p885_2 := h885c.2.2.1
                                  have p885_3 := h885c.2.2.2
                                  linarith only [h882, hlam, p885_1]
                                · have p885_0 := h885c.1
                                  have p885_1 := h885c.2.1
                                  have p885_2 := h885c.2.2.1
                                  have p885_3 := h885c.2.2.2
                                  linarith only [h883, hlam, p885_0]
                                · have p885_0 := h885c.1
                                  have p885_1 := h885c.2.1
                                  have p885_2 := h885c.2.2.1
                                  have p885_3 := h885c.2.2.2
                                  linarith only [hlam, p885_0]
                              · linarith only [h884, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h883, hc24, hlam, hphi, ht45, u5elo4]
                          · linarith only [h823, h882, hc13, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h0, h823, h881, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h822, h876, h879, h880, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h419, h821, h879, hlam]
                  · linarith only [h0, h820, h878, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h822, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h982 | h982
            · rcases m.htr 1 2 3 (by decide) (by decide) with h983 | h983
              · rcases m.htr 1 2 4 (by decide) (by decide) with h984 | h984
                · rcases m.htr 1 2 5 (by decide) (by decide) with h985 | h985
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h986 | h986
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h987 | h987
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h988 | h988
                        · linarith only [h530, h820, h821, h983, h988, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h530, h820, h983, h986, h988, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h982, h986, h987, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h992 | h992
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h993 | h993
                        · linarith only [h983, h986, h993, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h995 | h995
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h996 | h996
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h997 | h997
                              · rcases h2bigk with h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c
                                · have p998_0 := h998c.1
                                  have p998_1 := h998c.2.1
                                  have p998_2 := h998c.2.2.1
                                  have p998_3 := h998c.2.2.2
                                  linarith only [hlam, p998_0]
                                · have p998_0 := h998c.1
                                  have p998_1 := h998c.2.1
                                  have p998_2 := h998c.2.2.1
                                  have p998_3 := h998c.2.2.2
                                  linarith only [h0, hlam, p998_1]
                                · have p998_0 := h998c.1
                                  have p998_1 := h998c.2.1
                                  have p998_2 := h998c.2.2.1
                                  have p998_3 := h998c.2.2.2
                                  linarith only [h530, hlam, p998_0]
                                · have p998_0 := h998c.1
                                  have p998_1 := h998c.2.1
                                  have p998_2 := h998c.2.2.1
                                  have p998_3 := h998c.2.2.2
                                  linarith only [h741, hlam, p998_0]
                                · have p998_0 := h998c.1
                                  have p998_1 := h998c.2.1
                                  have p998_2 := h998c.2.2.1
                                  have p998_3 := h998c.2.2.2
                                  linarith only [h530, h983, h986, h995, h997, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p998_1]
                                · have p998_0 := h998c.1
                                  have p998_1 := h998c.2.1
                                  have p998_2 := h998c.2.2.1
                                  have p998_3 := h998c.2.2.2
                                  rcases p998_3 (m.d 0 2) (by simp) with h1004 | h1004
                                  · linarith only [h0, h1004, hlam]
                                  · rcases p998_3 (m.d 1 2) (by simp) with h1006 | h1006
                                    · rcases p998_3 (m.d 2 3) (by simp) with h1007 | h1007
                                      · linarith only [h1007, h983, hlam]
                                      · linarith only [h1007, h530, hlam]
                                    · linarith only [h0, h1006, hlam]
                                · have p998_0 := h998c.1
                                  have p998_1 := h998c.2.1
                                  have p998_2 := h998c.2.2.1
                                  have p998_3 := h998c.2.2.2
                                  linarith only [hlam, p998_0]
                                · have p998_0 := h998c.1
                                  have p998_1 := h998c.2.1
                                  have p998_2 := h998c.2.2.1
                                  have p998_3 := h998c.2.2.2
                                  linarith only [h0, h530, hc01, hc12, hlam, hphi, p998_1]
                                · have p998_0 := h998c.1
                                  have p998_1 := h998c.2.1
                                  have p998_2 := h998c.2.2.1
                                  have p998_3 := h998c.2.2.2
                                  linarith only [h0, h741, hc01, hc12, hlam, hphi, p998_1]
                                · have p998_0 := h998c.1
                                  have p998_1 := h998c.2.1
                                  have p998_2 := h998c.2.2.1
                                  have p998_3 := h998c.2.2.2
                                  linarith only [h530, h820, h983, hlam, p998_2]
                                · have p998_0 := h998c.1
                                  have p998_1 := h998c.2.1
                                  have p998_2 := h998c.2.2.1
                                  have p998_3 := h998c.2.2.2
                                  linarith only [h820, h983, h995, h997, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p998_1]
                                · have p998_0 := h998c.1
                                  have p998_1 := h998c.2.1
                                  have p998_2 := h998c.2.2.1
                                  have p998_3 := h998c.2.2.2
                                  linarith only [h983, hlam, p998_0]
                                · have p998_0 := h998c.1
                                  have p998_1 := h998c.2.1
                                  have p998_2 := h998c.2.2.1
                                  have p998_3 := h998c.2.2.2
                                  linarith only [hlam, p998_0]
                                · have p998_0 := h998c.1
                                  have p998_1 := h998c.2.1
                                  have p998_2 := h998c.2.2.1
                                  have p998_3 := h998c.2.2.2
                                  linarith only [h993, hlam, p998_0]
                                · have p998_0 := h998c.1
                                  have p998_1 := h998c.2.1
                                  have p998_2 := h998c.2.2.1
                                  have p998_3 := h998c.2.2.2
                                  rcases p998_3 (m.d 0 2) (by simp) with h1019 | h1019
                                  · linarith only [h1019, h530, hlam]
                                  · linarith only [h1019, h820, hlam]
                                · have p998_0 := h998c.1
                                  have p998_1 := h998c.2.1
                                  have p998_2 := h998c.2.2.1
                                  have p998_3 := h998c.2.2.2
                                  linarith only [h820, h984, h995, h997, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p998_1]
                                · have p998_0 := h998c.1
                                  have p998_1 := h998c.2.1
                                  have p998_2 := h998c.2.2.1
                                  have p998_3 := h998c.2.2.2
                                  linarith only [h984, hlam, p998_0]
                                · have p998_0 := h998c.1
                                  have p998_1 := h998c.2.1
                                  have p998_2 := h998c.2.2.1
                                  have p998_3 := h998c.2.2.2
                                  linarith only [h530, h820, h984, h995, h997, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p998_1]
                                · have p998_0 := h998c.1
                                  have p998_1 := h998c.2.1
                                  have p998_2 := h998c.2.2.1
                                  have p998_3 := h998c.2.2.2
                                  linarith only [hlam, p998_0]
                                · have p998_0 := h998c.1
                                  have p998_1 := h998c.2.1
                                  have p998_2 := h998c.2.2.1
                                  have p998_3 := h998c.2.2.2
                                  rcases p998_3 (m.d 0 2) (by simp) with h1026 | h1026
                                  · linarith only [h1026, h741, hlam]
                                  · linarith only [h1026, h820, hlam]
                                · have p998_0 := h998c.1
                                  have p998_1 := h998c.2.1
                                  have p998_2 := h998c.2.2.1
                                  have p998_3 := h998c.2.2.2
                                  linarith only [h820, hlam, p998_0]
                                · have p998_0 := h998c.1
                                  have p998_1 := h998c.2.1
                                  have p998_2 := h998c.2.2.1
                                  have p998_3 := h998c.2.2.2
                                  linarith only [h985, hlam, p998_0]
                                · have p998_0 := h998c.1
                                  have p998_1 := h998c.2.1
                                  have p998_2 := h998c.2.2.1
                                  have p998_3 := h998c.2.2.2
                                  linarith only [h995, hlam, p998_1]
                                · have p998_0 := h998c.1
                                  have p998_1 := h998c.2.1
                                  have p998_2 := h998c.2.2.1
                                  have p998_3 := h998c.2.2.2
                                  linarith only [h996, hlam, p998_0]
                                · have p998_0 := h998c.1
                                  have p998_1 := h998c.2.1
                                  have p998_2 := h998c.2.2.1
                                  have p998_3 := h998c.2.2.2
                                  linarith only [hlam, p998_0]
                              · linarith only [h986, h997, hc13, hlam, hphi, ht34, ht45, u5elo4]
                            · linarith only [h741, h996, hc04, hlam, hphi, ht45, u5elo4]
                          · linarith only [h530, h995, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h530, h820, h982, h983, h992, hc25, hlam, hphi, u5elo0]
                  · linarith only [h530, h820, h985, hc12, hc23, hlam, hphi]
                · linarith only [h530, h983, h984, hc02, hc24, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1040 | h1040
                · linarith only [h1040, h741, h820, h983, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1042 | h1042
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1043 | h1043
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1044 | h1044
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1045 | h1045
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1046 | h1046
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1047 | h1047
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1048 | h1048
                              · rcases h2bigk with h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c
                                · have p1049_0 := h1049c.1
                                  have p1049_1 := h1049c.2.1
                                  have p1049_2 := h1049c.2.2.1
                                  have p1049_3 := h1049c.2.2.2
                                  linarith only [hlam, p1049_0]
                                · have p1049_0 := h1049c.1
                                  have p1049_1 := h1049c.2.1
                                  have p1049_2 := h1049c.2.2.1
                                  have p1049_3 := h1049c.2.2.2
                                  linarith only [h0, hlam, p1049_1]
                                · have p1049_0 := h1049c.1
                                  have p1049_1 := h1049c.2.1
                                  have p1049_2 := h1049c.2.2.1
                                  have p1049_3 := h1049c.2.2.2
                                  linarith only [h530, hlam, p1049_0]
                                · have p1049_0 := h1049c.1
                                  have p1049_1 := h1049c.2.1
                                  have p1049_2 := h1049c.2.2.1
                                  have p1049_3 := h1049c.2.2.2
                                  linarith only [h741, hlam, p1049_0]
                                · have p1049_0 := h1049c.1
                                  have p1049_1 := h1049c.2.1
                                  have p1049_2 := h1049c.2.2.1
                                  have p1049_3 := h1049c.2.2.2
                                  linarith only [h1043, h1046, h1048, h530, h821, h983, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1049_1]
                                · have p1049_0 := h1049c.1
                                  have p1049_1 := h1049c.2.1
                                  have p1049_2 := h1049c.2.2.1
                                  have p1049_3 := h1049c.2.2.2
                                  linarith only [h1040, h1045, hc02, hc23, hlam, hphi, p1049_1]
                                · have p1049_0 := h1049c.1
                                  have p1049_1 := h1049c.2.1
                                  have p1049_2 := h1049c.2.2.1
                                  have p1049_3 := h1049c.2.2.2
                                  linarith only [hlam, p1049_0]
                                · have p1049_0 := h1049c.1
                                  have p1049_1 := h1049c.2.1
                                  have p1049_2 := h1049c.2.2.1
                                  have p1049_3 := h1049c.2.2.2
                                  linarith only [h983, hlam, p1049_0]
                                · have p1049_0 := h1049c.1
                                  have p1049_1 := h1049c.2.1
                                  have p1049_2 := h1049c.2.2.1
                                  have p1049_3 := h1049c.2.2.2
                                  linarith only [h1040, hlam, p1049_0]
                                · have p1049_0 := h1049c.1
                                  have p1049_1 := h1049c.2.1
                                  have p1049_2 := h1049c.2.2.1
                                  have p1049_3 := h1049c.2.2.2
                                  rcases p1049_3 (m.d 0 2) (by simp) with h1059 | h1059
                                  · linarith only [h0, h1059, hlam]
                                  · linarith only [h1059, h820, hlam]
                                · have p1049_0 := h1049c.1
                                  have p1049_1 := h1049c.2.1
                                  have p1049_2 := h1049c.2.2.1
                                  have p1049_3 := h1049c.2.2.2
                                  rcases p1049_3 (m.d 0 2) (by simp) with h1062 | h1062
                                  · linarith only [h1062, hlam, p1049_0]
                                  · rcases p1049_3 (m.d 1 2) (by simp) with h1064 | h1064
                                    · linarith only [h1064, h983, hlam]
                                    · linarith only [h0, h1064, hlam]
                                · have p1049_0 := h1049c.1
                                  have p1049_1 := h1049c.2.1
                                  have p1049_2 := h1049c.2.2.1
                                  have p1049_3 := h1049c.2.2.2
                                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p1049_1]
                                · have p1049_0 := h1049c.1
                                  have p1049_1 := h1049c.2.1
                                  have p1049_2 := h1049c.2.2.1
                                  have p1049_3 := h1049c.2.2.2
                                  linarith only [hlam, p1049_0]
                                · have p1049_0 := h1049c.1
                                  have p1049_1 := h1049c.2.1
                                  have p1049_2 := h1049c.2.2.1
                                  have p1049_3 := h1049c.2.2.2
                                  linarith only [h1046, h1048, h741, h820, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1049_1]
                                · have p1049_0 := h1049c.1
                                  have p1049_1 := h1049c.2.1
                                  have p1049_2 := h1049c.2.2.1
                                  have p1049_3 := h1049c.2.2.2
                                  linarith only [h1043, h530, h820, h821, h983, hlam, p1049_2]
                                · have p1049_0 := h1049c.1
                                  have p1049_1 := h1049c.2.1
                                  have p1049_2 := h1049c.2.2.1
                                  have p1049_3 := h1049c.2.2.2
                                  rcases p1049_3 (m.d 0 2) (by simp) with h1071 | h1071
                                  · linarith only [h1071, hlam, p1049_0]
                                  · rcases p1049_3 (m.d 1 2) (by simp) with h1073 | h1073
                                    · linarith only [h1040, h1073, hlam]
                                    · linarith only [h0, h1073, hlam]
                                · have p1049_0 := h1049c.1
                                  have p1049_1 := h1049c.2.1
                                  have p1049_2 := h1049c.2.2.1
                                  have p1049_3 := h1049c.2.2.2
                                  linarith only [h0, hc01, hc24, hlam, hphi, ht12, p1049_1]
                                · have p1049_0 := h1049c.1
                                  have p1049_1 := h1049c.2.1
                                  have p1049_2 := h1049c.2.2.1
                                  have p1049_3 := h1049c.2.2.2
                                  linarith only [h1045, hlam, p1049_1]
                                · have p1049_0 := h1049c.1
                                  have p1049_1 := h1049c.2.1
                                  have p1049_2 := h1049c.2.2.1
                                  have p1049_3 := h1049c.2.2.2
                                  linarith only [hlam, p1049_0]
                                · have p1049_0 := h1049c.1
                                  have p1049_1 := h1049c.2.1
                                  have p1049_2 := h1049c.2.2.1
                                  have p1049_3 := h1049c.2.2.2
                                  rcases p1049_3 (m.d 0 2) (by simp) with h1079 | h1079
                                  · linarith only [h1079, h741, hlam]
                                  · linarith only [h1079, h820, hlam]
                                · have p1049_0 := h1049c.1
                                  have p1049_1 := h1049c.2.1
                                  have p1049_2 := h1049c.2.2.1
                                  have p1049_3 := h1049c.2.2.2
                                  linarith only [h820, hlam, p1049_0]
                                · have p1049_0 := h1049c.1
                                  have p1049_1 := h1049c.2.1
                                  have p1049_2 := h1049c.2.2.1
                                  have p1049_3 := h1049c.2.2.2
                                  linarith only [h1042, hlam, p1049_0]
                                · have p1049_0 := h1049c.1
                                  have p1049_1 := h1049c.2.1
                                  have p1049_2 := h1049c.2.2.1
                                  have p1049_3 := h1049c.2.2.2
                                  linarith only [h1046, hlam, p1049_1]
                                · have p1049_0 := h1049c.1
                                  have p1049_1 := h1049c.2.1
                                  have p1049_2 := h1049c.2.2.1
                                  have p1049_3 := h1049c.2.2.2
                                  linarith only [h1047, hlam, p1049_0]
                                · have p1049_0 := h1049c.1
                                  have p1049_1 := h1049c.2.1
                                  have p1049_2 := h1049c.2.2.1
                                  have p1049_3 := h1049c.2.2.2
                                  linarith only [hlam, p1049_0]
                              · linarith only [h1048, h530, h821, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                            · linarith only [h1040, h1047, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h1043, h1046, h530, h820, h821, h983, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h1043, h1045, h983, hlam]
                      · linarith only [h1043, h1044, h821, h982, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1092 | h1092
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1093 | h1093
                        · linarith only [h1043, h1093, h419, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h1093, h983, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h1092, h982, h983, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h0, h1042, h820, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h530, h982, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
        · linarith only [h0, h820, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]

theorem r1l7_10_12_13_25_L_0_L_I_L_I_H_L (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0elo := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_13_25_L_0_L_I_L_I_H_L_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_10_12_13_25_L_0_L_I_L_I_H_L_x1 m hb0 hb2 hb3 hb5 h0

end R2N4
