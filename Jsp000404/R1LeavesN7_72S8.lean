import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_72S7

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_13_15_H_I_L_0_L_0_L_0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h468 | h468
  · rcases m.htr 0 1 4 (by decide) (by decide) with h469 | h469
    · rcases m.htr 0 2 3 (by decide) (by decide) with h470 | h470
      · rcases m.htr 0 2 4 (by decide) (by decide) with h471 | h471
        · rcases m.htr 0 3 4 (by decide) (by decide) with h472 | h472
          · rcases m.htr 0 3 5 (by decide) (by decide) with h473 | h473
            · rcases m.htr 0 4 5 (by decide) (by decide) with h474 | h474
              · rcases m.htr 1 2 3 (by decide) (by decide) with h475 | h475
                · rcases m.htr 1 2 4 (by decide) (by decide) with h476 | h476
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h477 | h477
                    · linarith only [h0, h468, h475, h477, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h472, h477, hc23, hlam, hphi, u3elo0]
                  · linarith only [h0, h476, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h475, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h482 | h482
                · rcases m.htr 1 2 4 (by decide) (by decide) with h483 | h483
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h484 | h484
                    · linarith only [h0, h468, h482, h484, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h472, h484, hc23, hlam, hphi, u3elo0]
                  · linarith only [h0, h483, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h468, h482, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
            · linarith only [h472, h473, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h490 | h490
            · rcases m.htr 0 4 5 (by decide) (by decide) with h491 | h491
              · rcases m.htr 1 2 3 (by decide) (by decide) with h492 | h492
                · rcases m.htr 1 2 4 (by decide) (by decide) with h493 | h493
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h494 | h494
                    · linarith only [h468, h472, h490, h492, h494, hc01, hc35, hlam, hphi, ht0b, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h496 | h496
                      · linarith only [h0, h469, h493, h494, h496, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · linarith only [h472, h490, h496, hc23, hlam, hphi, u3elo3]
                  · linarith only [h0, h493, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h492, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h472, h490, h491, hc35, hlam, hphi, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h502 | h502
              · rcases m.htr 1 2 3 (by decide) (by decide) with h503 | h503
                · rcases m.htr 1 2 4 (by decide) (by decide) with h504 | h504
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h505 | h505
                    · linarith only [h0, h468, h503, h505, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h507 | h507
                      · linarith only [h0, h469, h490, h504, h505, h507, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h509 | h509
                        · rcases h0bigk with h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [hlam, p510_0]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [h0, hlam, p510_1]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [h0, h468, h503, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p510_1, u2elo1]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p510_1, u2elo1]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [h0, h468, h490, h503, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p510_1, u2elo1]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [hc01, hlam, hphi, ht12, p510_1, u2elo0]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [hlam, p510_0]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [h0, h468, h503, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p510_1, u2elo1]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [h0, h502, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p510_1, u2elo1]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [h0, h468, h490, h503, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p510_1, u2elo1]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [h468, hlam, p510_1]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [h470, hlam, p510_1]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [hlam, p510_0]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [h472, hlam, p510_1]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [h490, hlam, p510_1]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [h469, hlam, p510_0]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [h471, hlam, p510_0]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [h0, h468, h469, h503, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p510_1, u2elo1]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [hlam, p510_0]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [h0, h468, h469, h490, h503, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p510_1, u2elo1]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p510_1, u5elo0]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [h0, h469, h502, hlam, p510_1]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [h0, h468, h469, h502, h503, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p510_1, u2elo1]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [h502, hlam, p510_1]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [hlam, p510_0]
                        · linarith only [h468, h472, h503, h509, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h0, h504, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h503, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h539 | h539
                · rcases m.htr 1 2 4 (by decide) (by decide) with h540 | h540
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h541 | h541
                    · linarith only [h0, h468, h472, h539, h541, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h543 | h543
                      · linarith only [h0, h468, h539, h543, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h545 | h545
                        · linarith only [h472, h502, h545, hc03, hlam, hphi, u3elo3]
                        · linarith only [h468, h472, h539, h545, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h0, h469, h471, h540, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h539, hc01, hlam, hphi, ht12, u2elo2]
        · linarith only [h0, h469, h471, hlam]
      · linarith only [h0, h468, h470, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h552 | h552
      · rcases m.htr 0 2 4 (by decide) (by decide) with h553 | h553
        · rcases m.htr 0 3 4 (by decide) (by decide) with h554 | h554
          · linarith only [h468, h469, h554, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h556 | h556
            · rcases m.htr 0 4 5 (by decide) (by decide) with h557 | h557
              · rcases m.htr 1 2 3 (by decide) (by decide) with h558 | h558
                · rcases m.htr 1 2 4 (by decide) (by decide) with h559 | h559
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h560 | h560
                    · linarith only [h468, h469, h554, h558, h560, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h562 | h562
                      · linarith only [h468, h469, h558, h559, h562, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · linarith only [h556, h562, hc23, hlam, hphi, u3elo0]
                  · linarith only [h0, h553, h559, hlam]
                · linarith only [h0, h468, h558, hc13, hlam, hphi, u3elo2]
              · linarith only [h468, h469, h557, hc13, hlam, hphi, ht34, ht45, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h568 | h568
              · rcases m.htr 1 2 3 (by decide) (by decide) with h569 | h569
                · rcases m.htr 1 2 4 (by decide) (by decide) with h570 | h570
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h571 | h571
                    · linarith only [h468, h469, h569, h570, h571, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h573 | h573
                      · linarith only [h468, h469, h556, h569, h570, h573, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h575 | h575
                        · rcases h0bigk with h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c
                          · have p576_0 := h576c.1
                            have p576_1 := h576c.2.1
                            have p576_2 := h576c.2.2.1
                            have p576_3 := h576c.2.2.2
                            linarith only [hlam, p576_0]
                          · have p576_0 := h576c.1
                            have p576_1 := h576c.2.1
                            have p576_2 := h576c.2.2.1
                            have p576_3 := h576c.2.2.2
                            linarith only [h0, hlam, p576_1]
                          · have p576_0 := h576c.1
                            have p576_1 := h576c.2.1
                            have p576_2 := h576c.2.2.1
                            have p576_3 := h576c.2.2.2
                            linarith only [h468, h469, h569, h570, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p576_1, u2elo1]
                          · have p576_0 := h576c.1
                            have p576_1 := h576c.2.1
                            have p576_2 := h576c.2.2.1
                            have p576_3 := h576c.2.2.2
                            linarith only [h469, hlam, p576_1]
                          · have p576_0 := h576c.1
                            have p576_1 := h576c.2.1
                            have p576_2 := h576c.2.2.1
                            have p576_3 := h576c.2.2.2
                            linarith only [h468, h469, h556, h569, h570, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p576_1, u2elo1]
                          · have p576_0 := h576c.1
                            have p576_1 := h576c.2.1
                            have p576_2 := h576c.2.2.1
                            have p576_3 := h576c.2.2.2
                            linarith only [h0, hc01, hlam, hphi, ht12, p576_1, u2elo1]
                          · have p576_0 := h576c.1
                            have p576_1 := h576c.2.1
                            have p576_2 := h576c.2.2.1
                            have p576_3 := h576c.2.2.2
                            linarith only [hlam, p576_0]
                          · have p576_0 := h576c.1
                            have p576_1 := h576c.2.1
                            have p576_2 := h576c.2.2.1
                            have p576_3 := h576c.2.2.2
                            linarith only [h0, h468, h569, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p576_1, u2elo1]
                          · have p576_0 := h576c.1
                            have p576_1 := h576c.2.1
                            have p576_2 := h576c.2.2.1
                            have p576_3 := h576c.2.2.2
                            linarith only [h0, h468, h469, h569, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p576_1, u2elo1]
                          · have p576_0 := h576c.1
                            have p576_1 := h576c.2.1
                            have p576_2 := h576c.2.2.1
                            have p576_3 := h576c.2.2.2
                            linarith only [h0, h468, h556, h569, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p576_1, u2elo1]
                          · have p576_0 := h576c.1
                            have p576_1 := h576c.2.1
                            have p576_2 := h576c.2.2.1
                            have p576_3 := h576c.2.2.2
                            linarith only [h468, hlam, p576_1]
                          · have p576_0 := h576c.1
                            have p576_1 := h576c.2.1
                            have p576_2 := h576c.2.2.1
                            have p576_3 := h576c.2.2.2
                            linarith only [h552, hlam, p576_1]
                          · have p576_0 := h576c.1
                            have p576_1 := h576c.2.1
                            have p576_2 := h576c.2.2.1
                            have p576_3 := h576c.2.2.2
                            linarith only [hlam, p576_0]
                          · have p576_0 := h576c.1
                            have p576_1 := h576c.2.1
                            have p576_2 := h576c.2.2.1
                            have p576_3 := h576c.2.2.2
                            linarith only [h554, hlam, p576_1]
                          · have p576_0 := h576c.1
                            have p576_1 := h576c.2.1
                            have p576_2 := h576c.2.2.1
                            have p576_3 := h576c.2.2.2
                            linarith only [h556, hlam, p576_1]
                          · have p576_0 := h576c.1
                            have p576_1 := h576c.2.1
                            have p576_2 := h576c.2.2.1
                            have p576_3 := h576c.2.2.2
                            linarith only [h468, h569, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p576_1]
                          · have p576_0 := h576c.1
                            have p576_1 := h576c.2.1
                            have p576_2 := h576c.2.2.1
                            have p576_3 := h576c.2.2.2
                            linarith only [h553, hlam, p576_0]
                          · have p576_0 := h576c.1
                            have p576_1 := h576c.2.1
                            have p576_2 := h576c.2.2.1
                            have p576_3 := h576c.2.2.2
                            linarith only [h468, h554, h569, hc23, hlam, hphi, p576_1, u3elo3]
                          · have p576_0 := h576c.1
                            have p576_1 := h576c.2.1
                            have p576_2 := h576c.2.2.1
                            have p576_3 := h576c.2.2.2
                            linarith only [hlam, p576_0]
                          · have p576_0 := h576c.1
                            have p576_1 := h576c.2.1
                            have p576_2 := h576c.2.2.1
                            have p576_3 := h576c.2.2.2
                            linarith only [h468, h554, h556, h569, hc23, hlam, hphi, p576_1, u3elo3]
                          · have p576_0 := h576c.1
                            have p576_1 := h576c.2.1
                            have p576_2 := h576c.2.2.1
                            have p576_3 := h576c.2.2.2
                            linarith only [h468, h569, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p576_1]
                          · have p576_0 := h576c.1
                            have p576_1 := h576c.2.1
                            have p576_2 := h576c.2.2.1
                            have p576_3 := h576c.2.2.2
                            linarith only [h553, hc05, hc24, hlam, hphi, ht0b, ht45, ht5b, p576_1]
                          · have p576_0 := h576c.1
                            have p576_1 := h576c.2.1
                            have p576_2 := h576c.2.2.1
                            have p576_3 := h576c.2.2.2
                            linarith only [h468, h556, h569, hc23, hlam, hphi, ht34, ht45, p576_1, u5elo3]
                          · have p576_0 := h576c.1
                            have p576_1 := h576c.2.1
                            have p576_2 := h576c.2.2.1
                            have p576_3 := h576c.2.2.2
                            linarith only [h568, hlam, p576_1]
                          · have p576_0 := h576c.1
                            have p576_1 := h576c.2.1
                            have p576_2 := h576c.2.2.1
                            have p576_3 := h576c.2.2.2
                            linarith only [hlam, p576_0]
                        · linarith only [h554, h568, h575, hlam]
                  · linarith only [h0, h468, h569, h570, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h0, h468, h569, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
              · linarith only [h468, h469, h568, hc13, hlam, hphi, ht34, ht45, u5elo4]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h606 | h606
          · linarith only [h0, h468, h553, h606, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h608 | h608
            · rcases m.htr 0 4 5 (by decide) (by decide) with h609 | h609
              · rcases m.htr 1 2 3 (by decide) (by decide) with h610 | h610
                · rcases m.htr 1 2 4 (by decide) (by decide) with h611 | h611
                  · linarith only [h0, h468, h553, h610, h611, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h0, h468, h610, h611, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h0, h468, h610, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
              · linarith only [h468, h469, h609, hc13, hlam, hphi, ht34, ht45, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h616 | h616
              · rcases m.htr 1 2 3 (by decide) (by decide) with h617 | h617
                · rcases m.htr 1 2 4 (by decide) (by decide) with h618 | h618
                  · linarith only [h553, h618, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h468, h617, h618, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h0, h468, h617, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
              · linarith only [h468, h469, h616, hc13, hlam, hphi, ht34, ht45, u5elo4]
      · linarith only [h0, h468, h552, hc13, hlam, hphi, u3elo2]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h624 | h624
    · rcases m.htr 0 2 3 (by decide) (by decide) with h625 | h625
      · rcases m.htr 0 2 4 (by decide) (by decide) with h626 | h626
        · rcases m.htr 0 3 4 (by decide) (by decide) with h627 | h627
          · rcases m.htr 0 3 5 (by decide) (by decide) with h628 | h628
            · rcases m.htr 0 4 5 (by decide) (by decide) with h629 | h629
              · rcases m.htr 1 2 3 (by decide) (by decide) with h630 | h630
                · rcases m.htr 1 2 4 (by decide) (by decide) with h631 | h631
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h632 | h632
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h633 | h633
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h634 | h634
                        · linarith only [h468, h624, h631, h632, h634, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                        · linarith only [h468, h624, h629, h634, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                      · linarith only [h632, h633, hc34, hlam, hphi, ht45, u5elo3]
                    · linarith only [h627, h632, hc23, hlam, hphi, u3elo0]
                  · linarith only [h468, h624, h626, h631, hc12, hlam, hphi, ht23, u3elo1]
                · linarith only [h0, h630, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h641 | h641
                · rcases m.htr 1 2 4 (by decide) (by decide) with h642 | h642
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h643 | h643
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h644 | h644
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h645 | h645
                        · linarith only [h468, h624, h629, h641, h642, h643, h645, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases h0bigk with h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [hlam, p647_0]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h0, hlam, p647_1]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h468, hlam, p647_0]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h468, h641, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p647_1, u2elo1]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h468, h641, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p647_1, u2elo1]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h0, hc01, hlam, hphi, ht12, p647_1, u2elo1]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [hlam, p647_0]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p647_1, u2elo1]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h0, h624, h642, h643, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p647_1, u2elo1]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p647_1, u2elo1]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h624, h642, h643, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p647_1]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h625, hlam, p647_1]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [hlam, p647_0]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h468, h624, h642, h643, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p647_1, u3elo1]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h468, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p647_1, u3elo1]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h624, hlam, p647_0]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h626, hlam, p647_0]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h627, hlam, p647_0]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [hlam, p647_0]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h629, hlam, p647_0]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h624, h642, h643, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p647_1]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h629, hc02, hlam, hphi, ht23, ht34, ht45, p647_1, u5elo4]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h628, hlam, p647_0]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h624, h629, h642, h643, hc34, hlam, hphi, ht45, p647_1, u5elo4]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [hlam, p647_0]
                      · linarith only [h643, h644, hc34, hlam, hphi, ht45, u5elo3]
                    · linarith only [h468, h627, h643, hc23, hlam, hphi, u3elo1]
                  · linarith only [h0, h624, h642, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                · linarith only [h0, h624, h641, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · linarith only [h627, h628, hc34, hlam, hphi, ht45, u5elo3]
          · linarith only [h468, h624, h627, hlam]
        · linarith only [h468, h624, h625, h626, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h680 | h680
        · rcases m.htr 0 3 4 (by decide) (by decide) with h681 | h681
          · rcases m.htr 0 3 5 (by decide) (by decide) with h682 | h682
            · rcases m.htr 0 4 5 (by decide) (by decide) with h683 | h683
              · rcases m.htr 1 2 3 (by decide) (by decide) with h684 | h684
                · linarith only [h625, h684, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h624, h684, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h687 | h687
                · linarith only [h0, h624, h625, h687, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · linarith only [h0, h624, h687, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · linarith only [h0, h624, h625, h682, hc14, hlam, hphi, ht45, u5elo3]
          · linarith only [h0, h624, h625, h681, hlam]
        · linarith only [h0, h624, h680, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h693 | h693
      · rcases m.htr 0 2 4 (by decide) (by decide) with h694 | h694
        · rcases m.htr 0 3 4 (by decide) (by decide) with h695 | h695
          · rcases m.htr 0 3 5 (by decide) (by decide) with h696 | h696
            · rcases m.htr 0 4 5 (by decide) (by decide) with h697 | h697
              · rcases m.htr 1 2 3 (by decide) (by decide) with h698 | h698
                · rcases m.htr 1 2 4 (by decide) (by decide) with h699 | h699
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h700 | h700
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h701 | h701
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h702 | h702
                        · linarith only [h0, h693, h700, h702, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · rcases h0bigk with h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c
                          · have p704_0 := h704c.1
                            have p704_1 := h704c.2.1
                            have p704_2 := h704c.2.2.1
                            have p704_3 := h704c.2.2.2
                            linarith only [hlam, p704_0]
                          · have p704_0 := h704c.1
                            have p704_1 := h704c.2.1
                            have p704_2 := h704c.2.2.1
                            have p704_3 := h704c.2.2.2
                            linarith only [h0, hlam, p704_1]
                          · have p704_0 := h704c.1
                            have p704_1 := h704c.2.1
                            have p704_2 := h704c.2.2.1
                            have p704_3 := h704c.2.2.2
                            linarith only [h468, hlam, p704_0]
                          · have p704_0 := h704c.1
                            have p704_1 := h704c.2.1
                            have p704_2 := h704c.2.2.1
                            have p704_3 := h704c.2.2.2
                            linarith only [h624, hlam, p704_1]
                          · have p704_0 := h704c.1
                            have p704_1 := h704c.2.1
                            have p704_2 := h704c.2.2.1
                            have p704_3 := h704c.2.2.2
                            linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p704_1, u2elo1]
                          · have p704_0 := h704c.1
                            have p704_1 := h704c.2.1
                            have p704_2 := h704c.2.2.1
                            have p704_3 := h704c.2.2.2
                            linarith only [h0, hc01, hlam, hphi, ht12, p704_1, u2elo1]
                          · have p704_0 := h704c.1
                            have p704_1 := h704c.2.1
                            have p704_2 := h704c.2.2.1
                            have p704_3 := h704c.2.2.2
                            linarith only [hlam, p704_0]
                          · have p704_0 := h704c.1
                            have p704_1 := h704c.2.1
                            have p704_2 := h704c.2.2.1
                            have p704_3 := h704c.2.2.2
                            linarith only [h0, h695, h697, h702, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p704_1, u2elo1]
                          · have p704_0 := h704c.1
                            have p704_1 := h704c.2.1
                            have p704_2 := h704c.2.2.1
                            have p704_3 := h704c.2.2.2
                            linarith only [h0, h697, h702, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p704_1, u2elo1]
                          · have p704_0 := h704c.1
                            have p704_1 := h704c.2.1
                            have p704_2 := h704c.2.2.1
                            have p704_3 := h704c.2.2.2
                            linarith only [h0, h697, h702, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p704_1, u2elo1]
                          · have p704_0 := h704c.1
                            have p704_1 := h704c.2.1
                            have p704_2 := h704c.2.2.1
                            have p704_3 := h704c.2.2.2
                            linarith only [h468, hc01, hlam, hphi, ht12, ht23, p704_1, u3elo1]
                          · have p704_0 := h704c.1
                            have p704_1 := h704c.2.1
                            have p704_2 := h704c.2.2.1
                            have p704_3 := h704c.2.2.2
                            linarith only [h693, hlam, p704_1]
                          · have p704_0 := h704c.1
                            have p704_1 := h704c.2.1
                            have p704_2 := h704c.2.2.1
                            have p704_3 := h704c.2.2.2
                            linarith only [hlam, p704_0]
                          · have p704_0 := h704c.1
                            have p704_1 := h704c.2.1
                            have p704_2 := h704c.2.2.1
                            have p704_3 := h704c.2.2.2
                            linarith only [h468, h697, h702, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p704_1, u3elo1]
                          · have p704_0 := h704c.1
                            have p704_1 := h704c.2.1
                            have p704_2 := h704c.2.2.1
                            have p704_3 := h704c.2.2.2
                            linarith only [h468, h697, h702, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p704_1, u3elo1]
                          · have p704_0 := h704c.1
                            have p704_1 := h704c.2.1
                            have p704_2 := h704c.2.2.1
                            have p704_3 := h704c.2.2.2
                            linarith only [h624, hc01, hc14, hlam, hphi, p704_1]
                          · have p704_0 := h704c.1
                            have p704_1 := h704c.2.1
                            have p704_2 := h704c.2.2.1
                            have p704_3 := h704c.2.2.2
                            linarith only [h694, hlam, p704_0]
                          · have p704_0 := h704c.1
                            have p704_1 := h704c.2.1
                            have p704_2 := h704c.2.2.1
                            have p704_3 := h704c.2.2.2
                            linarith only [h695, hlam, p704_0]
                          · have p704_0 := h704c.1
                            have p704_1 := h704c.2.1
                            have p704_2 := h704c.2.2.1
                            have p704_3 := h704c.2.2.2
                            linarith only [hlam, p704_0]
                          · have p704_0 := h704c.1
                            have p704_1 := h704c.2.1
                            have p704_2 := h704c.2.2.1
                            have p704_3 := h704c.2.2.2
                            linarith only [h468, h695, h697, h702, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p704_1, u3elo1]
                          · have p704_0 := h704c.1
                            have p704_1 := h704c.2.1
                            have p704_2 := h704c.2.2.1
                            have p704_3 := h704c.2.2.2
                            linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p704_1, u5elo0]
                          · have p704_0 := h704c.1
                            have p704_1 := h704c.2.1
                            have p704_2 := h704c.2.2.1
                            have p704_3 := h704c.2.2.2
                            linarith only [h468, h695, h697, h702, hc02, hc34, hlam, hphi, ht23, ht45, p704_1, u3elo1, u5elo0]
                          · have p704_0 := h704c.1
                            have p704_1 := h704c.2.1
                            have p704_2 := h704c.2.2.1
                            have p704_3 := h704c.2.2.2
                            linarith only [h696, hlam, p704_0]
                          · have p704_0 := h704c.1
                            have p704_1 := h704c.2.1
                            have p704_2 := h704c.2.2.1
                            have p704_3 := h704c.2.2.2
                            linarith only [h697, hlam, p704_1]
                          · have p704_0 := h704c.1
                            have p704_1 := h704c.2.1
                            have p704_2 := h704c.2.2.1
                            have p704_3 := h704c.2.2.2
                            linarith only [hlam, p704_0]
                      · linarith only [h700, h701, hc34, hlam, hphi, ht45, u5elo3]
                    · linarith only [h468, h695, h700, hc23, hlam, hphi, u3elo1]
                  · linarith only [h0, h699, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h698, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h734 | h734
                · rcases m.htr 1 2 4 (by decide) (by decide) with h735 | h735
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h736 | h736
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h737 | h737
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h738 | h738
                        · linarith only [h693, h697, h736, h738, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h0bigk with h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c
                          · have p740_0 := h740c.1
                            have p740_1 := h740c.2.1
                            have p740_2 := h740c.2.2.1
                            have p740_3 := h740c.2.2.2
                            linarith only [hlam, p740_0]
                          · have p740_0 := h740c.1
                            have p740_1 := h740c.2.1
                            have p740_2 := h740c.2.2.1
                            have p740_3 := h740c.2.2.2
                            linarith only [h0, hlam, p740_1]
                          · have p740_0 := h740c.1
                            have p740_1 := h740c.2.1
                            have p740_2 := h740c.2.2.1
                            have p740_3 := h740c.2.2.2
                            linarith only [h468, hlam, p740_0]
                          · have p740_0 := h740c.1
                            have p740_1 := h740c.2.1
                            have p740_2 := h740c.2.2.1
                            have p740_3 := h740c.2.2.2
                            linarith only [h624, hlam, p740_1]
                          · have p740_0 := h740c.1
                            have p740_1 := h740c.2.1
                            have p740_2 := h740c.2.2.1
                            have p740_3 := h740c.2.2.2
                            linarith only [h468, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p740_1]
                          · have p740_0 := h740c.1
                            have p740_1 := h740c.2.1
                            have p740_2 := h740c.2.2.1
                            have p740_3 := h740c.2.2.2
                            linarith only [h0, hc01, hlam, hphi, ht12, p740_1, u2elo1]
                          · have p740_0 := h740c.1
                            have p740_1 := h740c.2.1
                            have p740_2 := h740c.2.2.1
                            have p740_3 := h740c.2.2.2
                            linarith only [hlam, p740_0]
                          · have p740_0 := h740c.1
                            have p740_1 := h740c.2.1
                            have p740_2 := h740c.2.2.1
                            have p740_3 := h740c.2.2.2
                            linarith only [h0, h693, h737, h738, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p740_1, u2elo1]
                          · have p740_0 := h740c.1
                            have p740_1 := h740c.2.1
                            have p740_2 := h740c.2.2.1
                            have p740_3 := h740c.2.2.2
                            linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p740_1, u2elo1]
                          · have p740_0 := h740c.1
                            have p740_1 := h740c.2.1
                            have p740_2 := h740c.2.2.1
                            have p740_3 := h740c.2.2.2
                            linarith only [h0, h624, h697, hc01, hlam, hphi, ht12, p740_1, u2elo1]
                          · have p740_0 := h740c.1
                            have p740_1 := h740c.2.1
                            have p740_2 := h740c.2.2.1
                            have p740_3 := h740c.2.2.2
                            linarith only [hc01, hlam, hphi, ht12, ht23, p740_1, u3elo0]
                          · have p740_0 := h740c.1
                            have p740_1 := h740c.2.1
                            have p740_2 := h740c.2.2.1
                            have p740_3 := h740c.2.2.2
                            linarith only [h693, hlam, p740_1]
                          · have p740_0 := h740c.1
                            have p740_1 := h740c.2.1
                            have p740_2 := h740c.2.2.1
                            have p740_3 := h740c.2.2.2
                            linarith only [hlam, p740_0]
                          · have p740_0 := h740c.1
                            have p740_1 := h740c.2.1
                            have p740_2 := h740c.2.2.1
                            have p740_3 := h740c.2.2.2
                            linarith only [h468, h624, hc01, hlam, hphi, ht12, ht23, p740_1, u3elo1]
                          · have p740_0 := h740c.1
                            have p740_1 := h740c.2.1
                            have p740_2 := h740c.2.2.1
                            have p740_3 := h740c.2.2.2
                            linarith only [h468, h624, h697, hc01, hlam, hphi, ht12, ht23, p740_1, u3elo1]
                          · have p740_0 := h740c.1
                            have p740_1 := h740c.2.1
                            have p740_2 := h740c.2.2.1
                            have p740_3 := h740c.2.2.2
                            linarith only [h697, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p740_1, u5elo0]
                          · have p740_0 := h740c.1
                            have p740_1 := h740c.2.1
                            have p740_2 := h740c.2.2.1
                            have p740_3 := h740c.2.2.2
                            linarith only [h694, hlam, p740_0]
                          · have p740_0 := h740c.1
                            have p740_1 := h740c.2.1
                            have p740_2 := h740c.2.2.1
                            have p740_3 := h740c.2.2.2
                            linarith only [h695, hlam, p740_0]
                          · have p740_0 := h740c.1
                            have p740_1 := h740c.2.1
                            have p740_2 := h740c.2.2.1
                            have p740_3 := h740c.2.2.2
                            linarith only [hlam, p740_0]
                          · have p740_0 := h740c.1
                            have p740_1 := h740c.2.1
                            have p740_2 := h740c.2.2.1
                            have p740_3 := h740c.2.2.2
                            linarith only [h697, hlam, p740_0]
                          · have p740_0 := h740c.1
                            have p740_1 := h740c.2.1
                            have p740_2 := h740c.2.2.1
                            have p740_3 := h740c.2.2.2
                            linarith only [h0, h693, h697, h737, h738, hc01, hc34, hlam, hphi, ht12, ht45, p740_1, u2elo1, u5elo4]
                          · have p740_0 := h740c.1
                            have p740_1 := h740c.2.1
                            have p740_2 := h740c.2.2.1
                            have p740_3 := h740c.2.2.2
                            linarith only [h693, h697, h737, h738, hc34, hlam, hphi, ht45, p740_1, u5elo4]
                          · have p740_0 := h740c.1
                            have p740_1 := h740c.2.1
                            have p740_2 := h740c.2.2.1
                            have p740_3 := h740c.2.2.2
                            linarith only [h696, hlam, p740_0]
                          · have p740_0 := h740c.1
                            have p740_1 := h740c.2.1
                            have p740_2 := h740c.2.2.1
                            have p740_3 := h740c.2.2.2
                            linarith only [h697, hc04, hlam, hphi, ht45, p740_1, u5elo4]
                          · have p740_0 := h740c.1
                            have p740_1 := h740c.2.1
                            have p740_2 := h740c.2.2.1
                            have p740_3 := h740c.2.2.2
                            linarith only [hlam, p740_0]
                      · linarith only [h468, h696, h737, hc23, hlam, hphi, u3elo1]
                    · linarith only [h468, h695, h736, hc23, hlam, hphi, u3elo1]
                  · linarith only [h0, h735, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h734, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h695, h696, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h771 | h771
            · rcases m.htr 0 4 5 (by decide) (by decide) with h772 | h772
              · rcases m.htr 1 2 3 (by decide) (by decide) with h773 | h773
                · rcases m.htr 1 2 4 (by decide) (by decide) with h774 | h774
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h775 | h775
                    · linarith only [h695, h771, h775, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h777 | h777
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h778 | h778
                        · rcases h0bigk with h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c
                          · have p779_0 := h779c.1
                            have p779_1 := h779c.2.1
                            have p779_2 := h779c.2.2.1
                            have p779_3 := h779c.2.2.2
                            linarith only [hlam, p779_0]
                          · have p779_0 := h779c.1
                            have p779_1 := h779c.2.1
                            have p779_2 := h779c.2.2.1
                            have p779_3 := h779c.2.2.2
                            linarith only [h0, hlam, p779_1]
                          · have p779_0 := h779c.1
                            have p779_1 := h779c.2.1
                            have p779_2 := h779c.2.2.1
                            have p779_3 := h779c.2.2.2
                            linarith only [h468, hlam, p779_0]
                          · have p779_0 := h779c.1
                            have p779_1 := h779c.2.1
                            have p779_2 := h779c.2.2.1
                            have p779_3 := h779c.2.2.2
                            linarith only [h624, hlam, p779_1]
                          · have p779_0 := h779c.1
                            have p779_1 := h779c.2.1
                            have p779_2 := h779c.2.2.1
                            have p779_3 := h779c.2.2.2
                            linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p779_1, u2elo1]
                          · have p779_0 := h779c.1
                            have p779_1 := h779c.2.1
                            have p779_2 := h779c.2.2.1
                            have p779_3 := h779c.2.2.2
                            linarith only [h0, hc01, hlam, hphi, ht12, p779_1, u2elo1]
                          · have p779_0 := h779c.1
                            have p779_1 := h779c.2.1
                            have p779_2 := h779c.2.2.1
                            have p779_3 := h779c.2.2.2
                            linarith only [hlam, p779_0]
                          · have p779_0 := h779c.1
                            have p779_1 := h779c.2.1
                            have p779_2 := h779c.2.2.1
                            have p779_3 := h779c.2.2.2
                            linarith only [h0, h693, h777, h778, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p779_1, u2elo1]
                          · have p779_0 := h779c.1
                            have p779_1 := h779c.2.1
                            have p779_2 := h779c.2.2.1
                            have p779_3 := h779c.2.2.2
                            linarith only [h0, h693, h695, h777, h778, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p779_1, u2elo1]
                          · have p779_0 := h779c.1
                            have p779_1 := h779c.2.1
                            have p779_2 := h779c.2.2.1
                            have p779_3 := h779c.2.2.2
                            linarith only [h0, h771, h778, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p779_1, u2elo1]
                          · have p779_0 := h779c.1
                            have p779_1 := h779c.2.1
                            have p779_2 := h779c.2.2.1
                            have p779_3 := h779c.2.2.2
                            linarith only [h695, hc01, hlam, hphi, ht12, ht23, p779_1, u3elo3]
                          · have p779_0 := h779c.1
                            have p779_1 := h779c.2.1
                            have p779_2 := h779c.2.2.1
                            have p779_3 := h779c.2.2.2
                            linarith only [h693, hlam, p779_1]
                          · have p779_0 := h779c.1
                            have p779_1 := h779c.2.1
                            have p779_2 := h779c.2.2.1
                            have p779_3 := h779c.2.2.2
                            linarith only [hlam, p779_0]
                          · have p779_0 := h779c.1
                            have p779_1 := h779c.2.1
                            have p779_2 := h779c.2.2.1
                            have p779_3 := h779c.2.2.2
                            linarith only [h695, hlam, p779_1]
                          · have p779_0 := h779c.1
                            have p779_1 := h779c.2.1
                            have p779_2 := h779c.2.2.1
                            have p779_3 := h779c.2.2.2
                            linarith only [h695, h771, h778, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p779_1, u3elo3]
                          · have p779_0 := h779c.1
                            have p779_1 := h779c.2.1
                            have p779_2 := h779c.2.2.1
                            have p779_3 := h779c.2.2.2
                            linarith only [h624, hc01, hc14, hlam, hphi, p779_1]
                          · have p779_0 := h779c.1
                            have p779_1 := h779c.2.1
                            have p779_2 := h779c.2.2.1
                            have p779_3 := h779c.2.2.2
                            linarith only [h694, hlam, p779_0]
                          · have p779_0 := h779c.1
                            have p779_1 := h779c.2.1
                            have p779_2 := h779c.2.2.1
                            have p779_3 := h779c.2.2.2
                            linarith only [h0, h694, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p779_1, u2elo1]
                          · have p779_0 := h779c.1
                            have p779_1 := h779c.2.1
                            have p779_2 := h779c.2.2.1
                            have p779_3 := h779c.2.2.2
                            linarith only [hlam, p779_0]
                          · have p779_0 := h779c.1
                            have p779_1 := h779c.2.1
                            have p779_2 := h779c.2.2.1
                            have p779_3 := h779c.2.2.2
                            linarith only [h695, h771, h778, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p779_1, u3elo3]
                          · have p779_0 := h779c.1
                            have p779_1 := h779c.2.1
                            have p779_2 := h779c.2.2.1
                            have p779_3 := h779c.2.2.2
                            linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p779_1, u5elo0]
                          · have p779_0 := h779c.1
                            have p779_1 := h779c.2.1
                            have p779_2 := h779c.2.2.1
                            have p779_3 := h779c.2.2.2
                            linarith only [h694, h695, h771, h775, h777, h778, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p779_1, u3elo3]
                          · have p779_0 := h779c.1
                            have p779_1 := h779c.2.1
                            have p779_2 := h779c.2.2.1
                            have p779_3 := h779c.2.2.2
                            linarith only [h771, hlam, p779_0]
                          · have p779_0 := h779c.1
                            have p779_1 := h779c.2.1
                            have p779_2 := h779c.2.2.1
                            have p779_3 := h779c.2.2.2
                            linarith only [h772, hlam, p779_1]
                          · have p779_0 := h779c.1
                            have p779_1 := h779c.2.1
                            have p779_2 := h779c.2.2.1
                            have p779_3 := h779c.2.2.2
                            linarith only [hlam, p779_0]
                        · linarith only [h695, h778, hc03, hlam, hphi, ht34, ht45, u5elo4]
                      · linarith only [h695, h771, h777, hc23, hlam, hphi, u3elo3]
                  · linarith only [h694, h774, hc12, hlam, hphi, u2elo0]
                · linarith only [h0, h773, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · linarith only [h695, h771, h772, hc35, hlam, hphi, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h810 | h810
              · rcases m.htr 1 2 3 (by decide) (by decide) with h811 | h811
                · rcases m.htr 1 2 4 (by decide) (by decide) with h812 | h812
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h813 | h813
                    · linarith only [h693, h771, h813, hc34, hlam, hphi, ht45, u5elo3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h815 | h815
                      · linarith only [h693, h771, h815, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h817 | h817
                        · rcases h0bigk with h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c
                          · have p818_0 := h818c.1
                            have p818_1 := h818c.2.1
                            have p818_2 := h818c.2.2.1
                            have p818_3 := h818c.2.2.2
                            linarith only [hlam, p818_0]
                          · have p818_0 := h818c.1
                            have p818_1 := h818c.2.1
                            have p818_2 := h818c.2.2.1
                            have p818_3 := h818c.2.2.2
                            linarith only [h0, hlam, p818_1]
                          · have p818_0 := h818c.1
                            have p818_1 := h818c.2.1
                            have p818_2 := h818c.2.2.1
                            have p818_3 := h818c.2.2.2
                            linarith only [h468, hlam, p818_0]
                          · have p818_0 := h818c.1
                            have p818_1 := h818c.2.1
                            have p818_2 := h818c.2.2.1
                            have p818_3 := h818c.2.2.2
                            linarith only [h624, hlam, p818_1]
                          · have p818_0 := h818c.1
                            have p818_1 := h818c.2.1
                            have p818_2 := h818c.2.2.1
                            have p818_3 := h818c.2.2.2
                            linarith only [h468, h771, hc05, hlam, hphi, p818_1, u5elo3]
                          · have p818_0 := h818c.1
                            have p818_1 := h818c.2.1
                            have p818_2 := h818c.2.2.1
                            have p818_3 := h818c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p818_1]
                          · have p818_0 := h818c.1
                            have p818_1 := h818c.2.1
                            have p818_2 := h818c.2.2.1
                            have p818_3 := h818c.2.2.2
                            linarith only [hlam, p818_0]
                          · have p818_0 := h818c.1
                            have p818_1 := h818c.2.1
                            have p818_2 := h818c.2.2.1
                            have p818_3 := h818c.2.2.2
                            linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p818_1, u2elo1]
                          · have p818_0 := h818c.1
                            have p818_1 := h818c.2.1
                            have p818_2 := h818c.2.2.1
                            have p818_3 := h818c.2.2.2
                            linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p818_1, u2elo1]
                          · have p818_0 := h818c.1
                            have p818_1 := h818c.2.1
                            have p818_2 := h818c.2.2.1
                            have p818_3 := h818c.2.2.2
                            linarith only [h0, h468, h771, hc01, hlam, hphi, ht12, p818_1, u2elo1]
                          · have p818_0 := h818c.1
                            have p818_1 := h818c.2.1
                            have p818_2 := h818c.2.2.1
                            have p818_3 := h818c.2.2.2
                            linarith only [hc01, hlam, hphi, ht12, ht23, p818_1, u3elo0]
                          · have p818_0 := h818c.1
                            have p818_1 := h818c.2.1
                            have p818_2 := h818c.2.2.1
                            have p818_3 := h818c.2.2.2
                            linarith only [h693, hlam, p818_1]
                          · have p818_0 := h818c.1
                            have p818_1 := h818c.2.1
                            have p818_2 := h818c.2.2.1
                            have p818_3 := h818c.2.2.2
                            linarith only [hlam, p818_0]
                          · have p818_0 := h818c.1
                            have p818_1 := h818c.2.1
                            have p818_2 := h818c.2.2.1
                            have p818_3 := h818c.2.2.2
                            linarith only [h695, hlam, p818_1]
                          · have p818_0 := h818c.1
                            have p818_1 := h818c.2.1
                            have p818_2 := h818c.2.2.1
                            have p818_3 := h818c.2.2.2
                            linarith only [h771, hlam, p818_1]
                          · have p818_0 := h818c.1
                            have p818_1 := h818c.2.1
                            have p818_2 := h818c.2.2.1
                            have p818_3 := h818c.2.2.2
                            linarith only [h624, h812, hc01, hlam, hphi, ht12, p818_1, u2elo1]
                          · have p818_0 := h818c.1
                            have p818_1 := h818c.2.1
                            have p818_2 := h818c.2.2.1
                            have p818_3 := h818c.2.2.2
                            linarith only [h694, hlam, p818_0]
                          · have p818_0 := h818c.1
                            have p818_1 := h818c.2.1
                            have p818_2 := h818c.2.2.1
                            have p818_3 := h818c.2.2.2
                            linarith only [h624, h812, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p818_1, u2elo1]
                          · have p818_0 := h818c.1
                            have p818_1 := h818c.2.1
                            have p818_2 := h818c.2.2.1
                            have p818_3 := h818c.2.2.2
                            linarith only [hlam, p818_0]
                          · have p818_0 := h818c.1
                            have p818_1 := h818c.2.1
                            have p818_2 := h818c.2.2.1
                            have p818_3 := h818c.2.2.2
                            linarith only [h695, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p818_1, u3elo3]
                          · have p818_0 := h818c.1
                            have p818_1 := h818c.2.1
                            have p818_2 := h818c.2.2.1
                            have p818_3 := h818c.2.2.2
                            linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p818_1, u5elo0]
                          · have p818_0 := h818c.1
                            have p818_1 := h818c.2.1
                            have p818_2 := h818c.2.2.1
                            have p818_3 := h818c.2.2.2
                            linarith only [h771, hc02, hlam, hphi, ht23, ht34, ht45, p818_1, u5elo3]
                          · have p818_0 := h818c.1
                            have p818_1 := h818c.2.1
                            have p818_2 := h818c.2.2.1
                            have p818_3 := h818c.2.2.2
                            linarith only [h468, h771, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p818_1, u5elo3]
                          · have p818_0 := h818c.1
                            have p818_1 := h818c.2.1
                            have p818_2 := h818c.2.2.1
                            have p818_3 := h818c.2.2.2
                            linarith only [h810, hlam, p818_1]
                          · have p818_0 := h818c.1
                            have p818_1 := h818c.2.1
                            have p818_2 := h818c.2.2.1
                            have p818_3 := h818c.2.2.2
                            linarith only [hlam, p818_0]
                        · linarith only [h468, h695, h817, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h694, h812, hc12, hlam, hphi, u2elo0]
                · linarith only [h0, h811, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h847 | h847
                · rcases m.htr 1 2 4 (by decide) (by decide) with h848 | h848
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h849 | h849
                    · linarith only [h693, h695, h849, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h851 | h851
                      · linarith only [h693, h695, h771, h810, h851, hc05, hlam, hphi, u5elo4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h853 | h853
                        · linarith only [h468, h695, h810, h853, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h468, h695, h853, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h0, h848, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h847, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h858 | h858
          · linarith only [h693, h694, h858, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h860 | h860
            · rcases m.htr 0 4 5 (by decide) (by decide) with h861 | h861
              · rcases m.htr 1 2 3 (by decide) (by decide) with h862 | h862
                · rcases m.htr 1 2 4 (by decide) (by decide) with h863 | h863
                  · linarith only [h694, h863, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h863, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h862, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h693, h694, h861, hc23, hlam, hphi, ht34, ht45, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h868 | h868
              · rcases m.htr 1 2 3 (by decide) (by decide) with h869 | h869
                · rcases m.htr 1 2 4 (by decide) (by decide) with h870 | h870
                  · linarith only [h693, h694, h870, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h0, h870, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h869, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h693, h694, h868, hc23, hlam, hphi, ht34, ht45, u5elo4]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h875 | h875
        · rcases m.htr 0 3 4 (by decide) (by decide) with h876 | h876
          · rcases m.htr 0 3 5 (by decide) (by decide) with h877 | h877
            · rcases m.htr 0 4 5 (by decide) (by decide) with h878 | h878
              · rcases m.htr 1 2 3 (by decide) (by decide) with h879 | h879
                · linarith only [h693, h875, h879, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · linarith only [h0, h879, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h882 | h882
                · linarith only [h693, h875, h882, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · linarith only [h0, h882, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h693, h875, h877, hc24, hlam, hphi, ht45, u5elo3]
          · linarith only [h693, h875, h876, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h887 | h887
          · rcases m.htr 0 3 5 (by decide) (by decide) with h888 | h888
            · rcases m.htr 0 4 5 (by decide) (by decide) with h889 | h889
              · rcases m.htr 1 2 3 (by decide) (by decide) with h890 | h890
                · linarith only [h693, h890, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h890, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h893 | h893
                · linarith only [h0, h693, h893, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h893, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h887, h888, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h897 | h897
            · rcases m.htr 0 4 5 (by decide) (by decide) with h898 | h898
              · rcases m.htr 1 2 3 (by decide) (by decide) with h899 | h899
                · linarith only [h0, h693, h899, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h899, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · linarith only [h887, h897, h898, hc35, hlam, hphi, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h903 | h903
              · rcases m.htr 1 2 3 (by decide) (by decide) with h904 | h904
                · linarith only [h0, h693, h904, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h904, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h907 | h907
                · linarith only [h0, h693, h907, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h907, hc01, hlam, hphi, ht12, ht23, u3elo2]

theorem r1l7_20_12_13_15_H_I_L_0_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_13_15_H_I_L_0_L_0_L_0_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_20_12_13_15_H_I_L_0_L_0_L_0_x1 m hb0 hb2 hb3 hb5 h0

end R2N4
