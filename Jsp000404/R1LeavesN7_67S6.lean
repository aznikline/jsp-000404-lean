import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_67S5

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_13_M_LI_L_R_L_I_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h219 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h2ehi := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h479 | h479
  · rcases m.htr 0 2 3 (by decide) (by decide) with h480 | h480
    · rcases m.htr 0 2 4 (by decide) (by decide) with h481 | h481
      · rcases m.htr 0 2 5 (by decide) (by decide) with h482 | h482
        · rcases m.htr 0 3 4 (by decide) (by decide) with h483 | h483
          · rcases m.htr 0 3 5 (by decide) (by decide) with h484 | h484
            · rcases m.htr 0 4 5 (by decide) (by decide) with h485 | h485
              · rcases m.htr 1 2 3 (by decide) (by decide) with h486 | h486
                · rcases m.htr 1 2 5 (by decide) (by decide) with h487 | h487
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h488 | h488
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h489 | h489
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h490 | h490
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h491 | h491
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h492 | h492
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h493 | h493
                              · linarith only [h480, h490, h493, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                              · linarith only [h480, h490, h492, h493, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · linarith only [h480, h483, h485, h492, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                          · linarith only [h480, h484, h491, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                        · linarith only [h480, h483, h490, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                      · linarith only [h219, h479, h487, h489, hc35, hlam, hphi, ht23, u2ehi4]
                    · linarith only [h219, h480, h483, h488, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h479, h482, h487, hlam]
                · linarith only [h0, h479, h482, h486, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h503 | h503
                · rcases m.htr 1 2 5 (by decide) (by decide) with h504 | h504
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h505 | h505
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h506 | h506
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h507 | h507
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h508 | h508
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h509 | h509
                            · linarith only [h481, h485, h509, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h511 | h511
                              · linarith only [h480, h481, h485, h507, h511, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                              · rcases h0bigk with h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c
                                · have p513_0 := h513c.1
                                  have p513_1 := h513c.2.1
                                  have p513_2 := h513c.2.2.1
                                  have p513_3 := h513c.2.2.2
                                  linarith only [hlam, p513_0]
                                · have p513_0 := h513c.1
                                  have p513_1 := h513c.2.1
                                  have p513_2 := h513c.2.2.1
                                  have p513_3 := h513c.2.2.2
                                  linarith only [h0, hlam, p513_1]
                                · have p513_0 := h513c.1
                                  have p513_1 := h513c.2.1
                                  have p513_2 := h513c.2.2.1
                                  have p513_3 := h513c.2.2.2
                                  linarith only [h219, hlam, p513_0]
                                · have p513_0 := h513c.1
                                  have p513_1 := h513c.2.1
                                  have p513_2 := h513c.2.2.1
                                  have p513_3 := h513c.2.2.2
                                  linarith only [h481, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p513_1, u0elo0, u2ehi3]
                                · have p513_0 := h513c.1
                                  have p513_1 := h513c.2.1
                                  have p513_2 := h513c.2.2.1
                                  have p513_3 := h513c.2.2.2
                                  linarith only [h219, h479, h503, h504, h509, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p513_1, u2ehi3]
                                · have p513_0 := h513c.1
                                  have p513_1 := h513c.2.1
                                  have p513_2 := h513c.2.2.1
                                  have p513_3 := h513c.2.2.2
                                  linarith only [h479, h504, h509, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p513_1, u0elo1, u2ehi3]
                                · have p513_0 := h513c.1
                                  have p513_1 := h513c.2.1
                                  have p513_2 := h513c.2.2.1
                                  have p513_3 := h513c.2.2.2
                                  linarith only [hlam, p513_0]
                                · have p513_0 := h513c.1
                                  have p513_1 := h513c.2.1
                                  have p513_2 := h513c.2.2.1
                                  have p513_3 := h513c.2.2.2
                                  linarith only [h219, h479, h504, h509, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p513_1, u0elo1, u2ehi3]
                                · have p513_0 := h513c.1
                                  have p513_1 := h513c.2.1
                                  have p513_2 := h513c.2.2.1
                                  have p513_3 := h513c.2.2.2
                                  linarith only [h481, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p513_1, u0elo1, u2ehi3]
                                · have p513_0 := h513c.1
                                  have p513_1 := h513c.2.1
                                  have p513_2 := h513c.2.2.1
                                  have p513_3 := h513c.2.2.2
                                  linarith only [h479, h504, h509, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p513_1, u0elo1, u2ehi3]
                                · have p513_0 := h513c.1
                                  have p513_1 := h513c.2.1
                                  have p513_2 := h513c.2.2.1
                                  have p513_3 := h513c.2.2.2
                                  linarith only [h479, h504, h509, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p513_1, u0elo2, u2ehi3]
                                · have p513_0 := h513c.1
                                  have p513_1 := h513c.2.1
                                  have p513_2 := h513c.2.2.1
                                  have p513_3 := h513c.2.2.2
                                  linarith only [h480, hlam, p513_1]
                                · have p513_0 := h513c.1
                                  have p513_1 := h513c.2.1
                                  have p513_2 := h513c.2.2.1
                                  have p513_3 := h513c.2.2.2
                                  linarith only [hlam, p513_0]
                                · have p513_0 := h513c.1
                                  have p513_1 := h513c.2.1
                                  have p513_2 := h513c.2.2.1
                                  have p513_3 := h513c.2.2.2
                                  linarith only [h480, h481, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p513_1, u0elo1, u2ehi3]
                                · have p513_0 := h513c.1
                                  have p513_1 := h513c.2.1
                                  have p513_2 := h513c.2.2.1
                                  have p513_3 := h513c.2.2.2
                                  linarith only [h479, h480, h504, h509, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p513_1, u0elo1, u2ehi3]
                                · have p513_0 := h513c.1
                                  have p513_1 := h513c.2.1
                                  have p513_2 := h513c.2.2.1
                                  have p513_3 := h513c.2.2.2
                                  linarith only [h479, h504, h509, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p513_1, u0elo3, u2ehi3]
                                · have p513_0 := h513c.1
                                  have p513_1 := h513c.2.1
                                  have p513_2 := h513c.2.2.1
                                  have p513_3 := h513c.2.2.2
                                  linarith only [h481, hlam, p513_0]
                                · have p513_0 := h513c.1
                                  have p513_1 := h513c.2.1
                                  have p513_2 := h513c.2.2.1
                                  have p513_3 := h513c.2.2.2
                                  linarith only [h483, hlam, p513_0]
                                · have p513_0 := h513c.1
                                  have p513_1 := h513c.2.1
                                  have p513_2 := h513c.2.2.1
                                  have p513_3 := h513c.2.2.2
                                  linarith only [hlam, p513_0]
                                · have p513_0 := h513c.1
                                  have p513_1 := h513c.2.1
                                  have p513_2 := h513c.2.2.1
                                  have p513_3 := h513c.2.2.2
                                  linarith only [h485, hlam, p513_0]
                                · have p513_0 := h513c.1
                                  have p513_1 := h513c.2.1
                                  have p513_2 := h513c.2.2.1
                                  have p513_3 := h513c.2.2.2
                                  linarith only [h479, hlam, p513_0]
                                · have p513_0 := h513c.1
                                  have p513_1 := h513c.2.1
                                  have p513_2 := h513c.2.2.1
                                  have p513_3 := h513c.2.2.2
                                  linarith only [h482, hlam, p513_1]
                                · have p513_0 := h513c.1
                                  have p513_1 := h513c.2.1
                                  have p513_2 := h513c.2.2.1
                                  have p513_3 := h513c.2.2.2
                                  linarith only [h484, hlam, p513_0]
                                · have p513_0 := h513c.1
                                  have p513_1 := h513c.2.1
                                  have p513_2 := h513c.2.2.1
                                  have p513_3 := h513c.2.2.2
                                  linarith only [h481, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p513_1, u0elo4, u2ehi3]
                                · have p513_0 := h513c.1
                                  have p513_1 := h513c.2.1
                                  have p513_2 := h513c.2.2.1
                                  have p513_3 := h513c.2.2.2
                                  linarith only [hlam, p513_0]
                          · linarith only [h480, h484, h508, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                        · linarith only [h480, h483, h507, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                      · linarith only [h219, h479, h504, h506, hc35, hlam, hphi, ht23, u2ehi4]
                    · linarith only [h219, h480, h483, h505, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h479, h481, h485, h504, hc25, hlam, hphi, u2ehi3]
                · linarith only [h0, h479, h481, h485, h503, hc23, hlam, hphi, u2ehi3]
            · linarith only [h219, h479, h484, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h546 | h546
            · rcases m.htr 0 4 5 (by decide) (by decide) with h547 | h547
              · rcases m.htr 1 2 3 (by decide) (by decide) with h548 | h548
                · rcases m.htr 1 2 5 (by decide) (by decide) with h549 | h549
                  · linarith only [h219, h479, h483, h549, hc34, hlam, hphi, ht23, u2ehi4]
                  · linarith only [h0, h480, h549, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h480, h548, hlam]
              · linarith only [h219, h479, h483, h547, hlam]
            · linarith only [h219, h479, h546, hlam]
        · linarith only [h480, h482, hc25, hlam, hphi, u2ehi2]
      · linarith only [h480, h481, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h557 | h557
      · linarith only [h480, h557, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h559 | h559
        · linarith only [h480, h559, hc23, hlam, hphi, u2ehi4]
        · linarith only [h0, h479, h559, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h562 | h562
    · rcases m.htr 0 2 4 (by decide) (by decide) with h563 | h563
      · rcases m.htr 0 2 5 (by decide) (by decide) with h564 | h564
        · rcases m.htr 0 3 4 (by decide) (by decide) with h565 | h565
          · rcases m.htr 0 3 5 (by decide) (by decide) with h566 | h566
            · rcases m.htr 0 4 5 (by decide) (by decide) with h567 | h567
              · rcases m.htr 1 2 3 (by decide) (by decide) with h568 | h568
                · rcases m.htr 1 2 5 (by decide) (by decide) with h569 | h569
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h570 | h570
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h571 | h571
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h572 | h572
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h573 | h573
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h574 | h574
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h575 | h575
                              · linarith only [h562, h572, h575, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                              · linarith only [h562, h572, h574, h575, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · linarith only [h562, h565, h567, h574, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                          · linarith only [h562, h566, h573, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                        · linarith only [h562, h565, h572, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                      · linarith only [h219, h562, h566, h571, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h219, h565, h570, hlam]
                  · linarith only [h0, h562, h569, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h564, h568, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h585 | h585
                · rcases m.htr 1 2 5 (by decide) (by decide) with h586 | h586
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h587 | h587
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h588 | h588
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h589 | h589
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h590 | h590
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h591 | h591
                            · linarith only [h563, h567, h591, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h593 | h593
                              · linarith only [h562, h563, h567, h589, h593, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                              · rcases h0bigk with h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c
                                · have p595_0 := h595c.1
                                  have p595_1 := h595c.2.1
                                  have p595_2 := h595c.2.2.1
                                  have p595_3 := h595c.2.2.2
                                  linarith only [hlam, p595_0]
                                · have p595_0 := h595c.1
                                  have p595_1 := h595c.2.1
                                  have p595_2 := h595c.2.2.1
                                  have p595_3 := h595c.2.2.2
                                  linarith only [h0, hlam, p595_1]
                                · have p595_0 := h595c.1
                                  have p595_1 := h595c.2.1
                                  have p595_2 := h595c.2.2.1
                                  have p595_3 := h595c.2.2.2
                                  linarith only [h219, hlam, p595_0]
                                · have p595_0 := h595c.1
                                  have p595_1 := h595c.2.1
                                  have p595_2 := h595c.2.2.1
                                  have p595_3 := h595c.2.2.2
                                  linarith only [h563, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p595_1, u0elo0, u2ehi3]
                                · have p595_0 := h595c.1
                                  have p595_1 := h595c.2.1
                                  have p595_2 := h595c.2.2.1
                                  have p595_3 := h595c.2.2.2
                                  linarith only [h479, hlam, p595_1]
                                · have p595_0 := h595c.1
                                  have p595_1 := h595c.2.1
                                  have p595_2 := h595c.2.2.1
                                  have p595_3 := h595c.2.2.2
                                  rcases p595_3 (m.d 0 1) (by simp) with h601 | h601
                                  · linarith only [h0, h601, hlam]
                                  · rcases p595_3 (m.d 0 2) (by simp) with h603 | h603
                                    · rcases p595_3 (m.d 0 3) (by simp) with h604 | h604
                                      · linarith only [h562, h604, hlam]
                                      · linarith only [h219, h604, hlam]
                                    · linarith only [h0, h603, hlam]
                                · have p595_0 := h595c.1
                                  have p595_1 := h595c.2.1
                                  have p595_2 := h595c.2.2.1
                                  have p595_3 := h595c.2.2.2
                                  linarith only [hlam, p595_0]
                                · have p595_0 := h595c.1
                                  have p595_1 := h595c.2.1
                                  have p595_2 := h595c.2.2.1
                                  have p595_3 := h595c.2.2.2
                                  linarith only [h562, h590, h593, hc34, hlam, hphi, ht0b, ht45, ht5b, p595_1, u0elo1]
                                · have p595_0 := h595c.1
                                  have p595_1 := h595c.2.1
                                  have p595_2 := h595c.2.2.1
                                  have p595_3 := h595c.2.2.2
                                  linarith only [h563, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p595_1, u0elo1, u2ehi3]
                                · have p595_0 := h595c.1
                                  have p595_1 := h595c.2.1
                                  have p595_2 := h595c.2.2.1
                                  have p595_3 := h595c.2.2.2
                                  linarith only [h564, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p595_1, u0elo1, u2ehi4]
                                · have p595_0 := h595c.1
                                  have p595_1 := h595c.2.1
                                  have p595_2 := h595c.2.2.1
                                  have p595_3 := h595c.2.2.2
                                  rcases p595_3 (m.d 0 1) (by simp) with h612 | h612
                                  · linarith only [h219, h612, hlam]
                                  · rcases p595_3 (m.d 0 2) (by simp) with h614 | h614
                                    · rcases p595_3 (m.d 0 3) (by simp) with h615 | h615
                                      · rcases p595_3 (m.d 0 4) (by simp) with h616 | h616
                                        · linarith only [h565, h616, hlam]
                                        · linarith only [h563, h616, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p595_1, u0elo2, u2ehi3]
                                      · linarith only [h219, h615, hlam]
                                    · linarith only [h0, h614, hlam]
                                · have p595_0 := h595c.1
                                  have p595_1 := h595c.2.1
                                  have p595_2 := h595c.2.2.1
                                  have p595_3 := h595c.2.2.2
                                  linarith only [h562, hlam, p595_1]
                                · have p595_0 := h595c.1
                                  have p595_1 := h595c.2.1
                                  have p595_2 := h595c.2.2.1
                                  have p595_3 := h595c.2.2.2
                                  linarith only [hlam, p595_0]
                                · have p595_0 := h595c.1
                                  have p595_1 := h595c.2.1
                                  have p595_2 := h595c.2.2.1
                                  have p595_3 := h595c.2.2.2
                                  linarith only [h562, h563, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p595_1, u0elo1, u2ehi3]
                                · have p595_0 := h595c.1
                                  have p595_1 := h595c.2.1
                                  have p595_2 := h595c.2.2.1
                                  have p595_3 := h595c.2.2.2
                                  linarith only [h562, h563, h567, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p595_1, u0elo1, u2ehi3]
                                · have p595_0 := h595c.1
                                  have p595_1 := h595c.2.1
                                  have p595_2 := h595c.2.2.1
                                  have p595_3 := h595c.2.2.2
                                  linarith only [h567, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p595_1]
                                · have p595_0 := h595c.1
                                  have p595_1 := h595c.2.1
                                  have p595_2 := h595c.2.2.1
                                  have p595_3 := h595c.2.2.2
                                  linarith only [h563, hlam, p595_0]
                                · have p595_0 := h595c.1
                                  have p595_1 := h595c.2.1
                                  have p595_2 := h595c.2.2.1
                                  have p595_3 := h595c.2.2.2
                                  linarith only [h565, hlam, p595_0]
                                · have p595_0 := h595c.1
                                  have p595_1 := h595c.2.1
                                  have p595_2 := h595c.2.2.1
                                  have p595_3 := h595c.2.2.2
                                  linarith only [hlam, p595_0]
                                · have p595_0 := h595c.1
                                  have p595_1 := h595c.2.1
                                  have p595_2 := h595c.2.2.1
                                  have p595_3 := h595c.2.2.2
                                  linarith only [h567, hlam, p595_0]
                                · have p595_0 := h595c.1
                                  have p595_1 := h595c.2.1
                                  have p595_2 := h595c.2.2.1
                                  have p595_3 := h595c.2.2.2
                                  rcases p595_3 (m.d 0 1) (by simp) with h630 | h630
                                  · linarith only [h479, h630, hlam]
                                  · rcases p595_3 (m.d 0 2) (by simp) with h632 | h632
                                    · rcases p595_3 (m.d 0 3) (by simp) with h633 | h633
                                      · rcases p595_3 (m.d 0 4) (by simp) with h634 | h634
                                        · linarith only [h567, h634, hlam]
                                        · linarith only [h563, h634, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p595_1, u0elo4, u2ehi3]
                                      · linarith only [h219, h633, hlam]
                                    · linarith only [h0, h632, hlam]
                                · have p595_0 := h595c.1
                                  have p595_1 := h595c.2.1
                                  have p595_2 := h595c.2.2.1
                                  have p595_3 := h595c.2.2.2
                                  linarith only [h564, hlam, p595_1]
                                · have p595_0 := h595c.1
                                  have p595_1 := h595c.2.1
                                  have p595_2 := h595c.2.2.1
                                  have p595_3 := h595c.2.2.2
                                  linarith only [h566, hlam, p595_0]
                                · have p595_0 := h595c.1
                                  have p595_1 := h595c.2.1
                                  have p595_2 := h595c.2.2.1
                                  have p595_3 := h595c.2.2.2
                                  linarith only [h562, h563, h566, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p595_1, u0elo1, u2ehi3]
                                · have p595_0 := h595c.1
                                  have p595_1 := h595c.2.1
                                  have p595_2 := h595c.2.2.1
                                  have p595_3 := h595c.2.2.2
                                  linarith only [hlam, p595_0]
                          · linarith only [h562, h566, h590, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                        · linarith only [h562, h565, h589, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                      · linarith only [h219, h566, h588, hlam]
                    · linarith only [h219, h565, h587, hlam]
                  · linarith only [h0, h562, h586, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h562, h585, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h649 | h649
              · linarith only [h565, h566, h649, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h651 | h651
                · rcases m.htr 1 2 5 (by decide) (by decide) with h652 | h652
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h653 | h653
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h654 | h654
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h655 | h655
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h656 | h656
                          · linarith only [h562, h566, h656, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h658 | h658
                            · linarith only [h563, h649, h658, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h660 | h660
                              · linarith only [h563, h564, h649, h655, h656, h660, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                              · rcases h0bigk with h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c
                                · have p662_0 := h662c.1
                                  have p662_1 := h662c.2.1
                                  have p662_2 := h662c.2.2.1
                                  have p662_3 := h662c.2.2.2
                                  linarith only [hlam, p662_0]
                                · have p662_0 := h662c.1
                                  have p662_1 := h662c.2.1
                                  have p662_2 := h662c.2.2.1
                                  have p662_3 := h662c.2.2.2
                                  linarith only [h0, hlam, p662_1]
                                · have p662_0 := h662c.1
                                  have p662_1 := h662c.2.1
                                  have p662_2 := h662c.2.2.1
                                  have p662_3 := h662c.2.2.2
                                  linarith only [h219, hlam, p662_0]
                                · have p662_0 := h662c.1
                                  have p662_1 := h662c.2.1
                                  have p662_2 := h662c.2.2.1
                                  have p662_3 := h662c.2.2.2
                                  linarith only [h219, h563, h566, h651, h654, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p662_1, u2ehi3]
                                · have p662_0 := h662c.1
                                  have p662_1 := h662c.2.1
                                  have p662_2 := h662c.2.2.1
                                  have p662_3 := h662c.2.2.2
                                  linarith only [h479, hlam, p662_1]
                                · have p662_0 := h662c.1
                                  have p662_1 := h662c.2.1
                                  have p662_2 := h662c.2.2.1
                                  have p662_3 := h662c.2.2.2
                                  rcases p662_3 (m.d 0 1) (by simp) with h668 | h668
                                  · linarith only [h0, h668, hlam]
                                  · rcases p662_3 (m.d 0 2) (by simp) with h670 | h670
                                    · rcases p662_3 (m.d 0 3) (by simp) with h671 | h671
                                      · linarith only [h562, h671, hlam]
                                      · linarith only [h219, h671, hlam]
                                    · linarith only [h0, h670, hlam]
                                · have p662_0 := h662c.1
                                  have p662_1 := h662c.2.1
                                  have p662_2 := h662c.2.2.1
                                  have p662_3 := h662c.2.2.2
                                  linarith only [hlam, p662_0]
                                · have p662_0 := h662c.1
                                  have p662_1 := h662c.2.1
                                  have p662_2 := h662c.2.2.1
                                  have p662_3 := h662c.2.2.2
                                  linarith only [h562, h655, hc34, hlam, hphi, ht0b, ht45, ht5b, p662_1, u0elo1]
                                · have p662_0 := h662c.1
                                  have p662_1 := h662c.2.1
                                  have p662_2 := h662c.2.2.1
                                  have p662_3 := h662c.2.2.2
                                  linarith only [h563, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p662_1, u0elo1, u2ehi3]
                                · have p662_0 := h662c.1
                                  have p662_1 := h662c.2.1
                                  have p662_2 := h662c.2.2.1
                                  have p662_3 := h662c.2.2.2
                                  linarith only [h564, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p662_1, u0elo1, u2ehi4]
                                · have p662_0 := h662c.1
                                  have p662_1 := h662c.2.1
                                  have p662_2 := h662c.2.2.1
                                  have p662_3 := h662c.2.2.2
                                  linarith only [h566, h651, h654, hc01, hc12, hlam, hphi, p662_1]
                                · have p662_0 := h662c.1
                                  have p662_1 := h662c.2.1
                                  have p662_2 := h662c.2.2.1
                                  have p662_3 := h662c.2.2.2
                                  linarith only [h562, hlam, p662_1]
                                · have p662_0 := h662c.1
                                  have p662_1 := h662c.2.1
                                  have p662_2 := h662c.2.2.1
                                  have p662_3 := h662c.2.2.2
                                  linarith only [hlam, p662_0]
                                · have p662_0 := h662c.1
                                  have p662_1 := h662c.2.1
                                  have p662_2 := h662c.2.2.1
                                  have p662_3 := h662c.2.2.2
                                  linarith only [h562, h563, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p662_1, u0elo1, u2ehi3]
                                · have p662_0 := h662c.1
                                  have p662_1 := h662c.2.1
                                  have p662_2 := h662c.2.2.1
                                  have p662_3 := h662c.2.2.2
                                  linarith only [h566, hlam, p662_1]
                                · have p662_0 := h662c.1
                                  have p662_1 := h662c.2.1
                                  have p662_2 := h662c.2.2.1
                                  have p662_3 := h662c.2.2.2
                                  linarith only [h565, h566, h651, h654, hc01, hc12, hlam, hphi, p662_1]
                                · have p662_0 := h662c.1
                                  have p662_1 := h662c.2.1
                                  have p662_2 := h662c.2.2.1
                                  have p662_3 := h662c.2.2.2
                                  linarith only [h563, hlam, p662_0]
                                · have p662_0 := h662c.1
                                  have p662_1 := h662c.2.1
                                  have p662_2 := h662c.2.2.1
                                  have p662_3 := h662c.2.2.2
                                  linarith only [h565, hlam, p662_0]
                                · have p662_0 := h662c.1
                                  have p662_1 := h662c.2.1
                                  have p662_2 := h662c.2.2.1
                                  have p662_3 := h662c.2.2.2
                                  linarith only [hlam, p662_0]
                                · have p662_0 := h662c.1
                                  have p662_1 := h662c.2.1
                                  have p662_2 := h662c.2.2.1
                                  have p662_3 := h662c.2.2.2
                                  linarith only [h649, hlam, p662_0]
                                · have p662_0 := h662c.1
                                  have p662_1 := h662c.2.1
                                  have p662_2 := h662c.2.2.1
                                  have p662_3 := h662c.2.2.2
                                  linarith only [h566, h651, h654, hc01, hc12, hlam, hphi, p662_1]
                                · have p662_0 := h662c.1
                                  have p662_1 := h662c.2.1
                                  have p662_2 := h662c.2.2.1
                                  have p662_3 := h662c.2.2.2
                                  linarith only [h564, hlam, p662_1]
                                · have p662_0 := h662c.1
                                  have p662_1 := h662c.2.1
                                  have p662_2 := h662c.2.2.1
                                  have p662_3 := h662c.2.2.2
                                  linarith only [h219, h566, h651, h654, hc01, hc12, hlam, hphi, p662_1]
                                · have p662_0 := h662c.1
                                  have p662_1 := h662c.2.1
                                  have p662_2 := h662c.2.2.1
                                  have p662_3 := h662c.2.2.2
                                  linarith only [h563, h566, h651, h654, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p662_1, u2ehi3]
                                · have p662_0 := h662c.1
                                  have p662_1 := h662c.2.1
                                  have p662_2 := h662c.2.2.1
                                  have p662_3 := h662c.2.2.2
                                  linarith only [hlam, p662_0]
                        · linarith only [h565, h655, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h695 | h695
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h696 | h696
                          · linarith only [h219, h654, h696, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h698 | h698
                            · linarith only [h563, h649, h698, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h700 | h700
                              · linarith only [h562, h649, h695, h700, hc05, hlam, hphi, ht0b, ht5b, u0elo1]
                              · rcases h0bigk with h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [hlam, p702_0]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [h0, hlam, p702_1]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [h219, hlam, p702_0]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [h563, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p702_1, u0elo0, u2ehi3]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [h479, hlam, p702_1]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  rcases p702_3 (m.d 0 1) (by simp) with h708 | h708
                                  · linarith only [h0, h708, hlam]
                                  · rcases p702_3 (m.d 0 2) (by simp) with h710 | h710
                                    · rcases p702_3 (m.d 0 3) (by simp) with h711 | h711
                                      · linarith only [h562, h711, hlam]
                                      · linarith only [h219, h711, hlam]
                                    · linarith only [h0, h710, hlam]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [hlam, p702_0]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [h563, h565, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p702_1, u0elo1, u2ehi3]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [h563, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p702_1, u0elo1, u2ehi3]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [h563, h565, h566, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p702_1, u0elo1, u2ehi3]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [h219, h654, hc01, hc35, hlam, hphi, ht12, ht23, p702_1]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [h562, hlam, p702_1]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [hlam, p702_0]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [h219, h563, h654, h700, hc24, hc45, hlam, hphi, p702_1]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [h566, hlam, p702_1]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [h219, h565, h654, h700, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p702_1]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [h563, hlam, p702_0]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [h565, hlam, p702_0]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [hlam, p702_0]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [h649, hlam, p702_0]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  rcases p702_3 (m.d 0 1) (by simp) with h729 | h729
                                  · linarith only [h479, h729, hlam]
                                  · rcases p702_3 (m.d 0 2) (by simp) with h731 | h731
                                    · rcases p702_3 (m.d 0 3) (by simp) with h732 | h732
                                      · linarith only [h566, h732, hlam]
                                      · linarith only [h219, h732, hlam]
                                    · linarith only [h0, h731, hlam]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [h564, hlam, p702_1]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [h562, h695, hc34, hlam, hphi, ht0b, ht45, ht5b, p702_1, u0elo4]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [h563, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p702_1, u0elo4, u2ehi3]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [hlam, p702_0]
                        · linarith only [h565, h695, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi2]
                    · linarith only [h219, h565, h653, hlam]
                  · linarith only [h0, h562, h652, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h562, h651, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h744 | h744
            · rcases m.htr 0 4 5 (by decide) (by decide) with h745 | h745
              · rcases m.htr 1 2 3 (by decide) (by decide) with h746 | h746
                · rcases m.htr 1 2 5 (by decide) (by decide) with h747 | h747
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h748 | h748
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h749 | h749
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h750 | h750
                        · linarith only [h562, h565, h750, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h752 | h752
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h753 | h753
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h754 | h754
                              · rcases h0bigk with h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c
                                · have p755_0 := h755c.1
                                  have p755_1 := h755c.2.1
                                  have p755_2 := h755c.2.2.1
                                  have p755_3 := h755c.2.2.2
                                  linarith only [hlam, p755_0]
                                · have p755_0 := h755c.1
                                  have p755_1 := h755c.2.1
                                  have p755_2 := h755c.2.2.1
                                  have p755_3 := h755c.2.2.2
                                  linarith only [h0, hlam, p755_1]
                                · have p755_0 := h755c.1
                                  have p755_1 := h755c.2.1
                                  have p755_2 := h755c.2.2.1
                                  have p755_3 := h755c.2.2.2
                                  linarith only [h219, hlam, p755_0]
                                · have p755_0 := h755c.1
                                  have p755_1 := h755c.2.1
                                  have p755_2 := h755c.2.2.1
                                  have p755_3 := h755c.2.2.2
                                  linarith only [h564, h565, h744, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p755_1, u0elo0, u2ehi4]
                                · have p755_0 := h755c.1
                                  have p755_1 := h755c.2.1
                                  have p755_2 := h755c.2.2.1
                                  have p755_3 := h755c.2.2.2
                                  linarith only [h479, hlam, p755_1]
                                · have p755_0 := h755c.1
                                  have p755_1 := h755c.2.1
                                  have p755_2 := h755c.2.2.1
                                  have p755_3 := h755c.2.2.2
                                  rcases p755_3 (m.d 0 1) (by simp) with h761 | h761
                                  · linarith only [h0, h761, hlam]
                                  · rcases p755_3 (m.d 0 2) (by simp) with h763 | h763
                                    · rcases p755_3 (m.d 0 3) (by simp) with h764 | h764
                                      · linarith only [h562, h764, hlam]
                                      · linarith only [h219, h764, hlam]
                                    · linarith only [h0, h763, hlam]
                                · have p755_0 := h755c.1
                                  have p755_1 := h755c.2.1
                                  have p755_2 := h755c.2.2.1
                                  have p755_3 := h755c.2.2.2
                                  linarith only [hlam, p755_0]
                                · have p755_0 := h755c.1
                                  have p755_1 := h755c.2.1
                                  have p755_2 := h755c.2.2.1
                                  have p755_3 := h755c.2.2.2
                                  linarith only [h564, h744, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p755_1, u0elo1, u2ehi4]
                                · have p755_0 := h755c.1
                                  have p755_1 := h755c.2.1
                                  have p755_2 := h755c.2.2.1
                                  have p755_3 := h755c.2.2.2
                                  linarith only [h564, h565, h744, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p755_1, u0elo1, u2ehi4]
                                · have p755_0 := h755c.1
                                  have p755_1 := h755c.2.1
                                  have p755_2 := h755c.2.2.1
                                  have p755_3 := h755c.2.2.2
                                  linarith only [h564, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p755_1, u0elo1, u2ehi4]
                                · have p755_0 := h755c.1
                                  have p755_1 := h755c.2.1
                                  have p755_2 := h755c.2.2.1
                                  have p755_3 := h755c.2.2.2
                                  linarith only [h565, h746, h748, hc01, hc12, hlam, hphi, p755_1]
                                · have p755_0 := h755c.1
                                  have p755_1 := h755c.2.1
                                  have p755_2 := h755c.2.2.1
                                  have p755_3 := h755c.2.2.2
                                  linarith only [h562, hlam, p755_1]
                                · have p755_0 := h755c.1
                                  have p755_1 := h755c.2.1
                                  have p755_2 := h755c.2.2.1
                                  have p755_3 := h755c.2.2.2
                                  linarith only [hlam, p755_0]
                                · have p755_0 := h755c.1
                                  have p755_1 := h755c.2.1
                                  have p755_2 := h755c.2.2.1
                                  have p755_3 := h755c.2.2.2
                                  linarith only [h565, hlam, p755_1]
                                · have p755_0 := h755c.1
                                  have p755_1 := h755c.2.1
                                  have p755_2 := h755c.2.2.1
                                  have p755_3 := h755c.2.2.2
                                  linarith only [h564, h565, h746, h748, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p755_1, u2ehi4]
                                · have p755_0 := h755c.1
                                  have p755_1 := h755c.2.1
                                  have p755_2 := h755c.2.2.1
                                  have p755_3 := h755c.2.2.2
                                  linarith only [h565, h746, h748, hc01, hc12, hlam, hphi, p755_1]
                                · have p755_0 := h755c.1
                                  have p755_1 := h755c.2.1
                                  have p755_2 := h755c.2.2.1
                                  have p755_3 := h755c.2.2.2
                                  linarith only [h563, hlam, p755_0]
                                · have p755_0 := h755c.1
                                  have p755_1 := h755c.2.1
                                  have p755_2 := h755c.2.2.1
                                  have p755_3 := h755c.2.2.2
                                  linarith only [h562, h563, h752, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p755_1, u0elo1, u2ehi4]
                                · have p755_0 := h755c.1
                                  have p755_1 := h755c.2.1
                                  have p755_2 := h755c.2.2.1
                                  have p755_3 := h755c.2.2.2
                                  linarith only [hlam, p755_0]
                                · have p755_0 := h755c.1
                                  have p755_1 := h755c.2.1
                                  have p755_2 := h755c.2.2.1
                                  have p755_3 := h755c.2.2.2
                                  linarith only [h564, h565, h748, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p755_1, u2ehi4]
                                · have p755_0 := h755c.1
                                  have p755_1 := h755c.2.1
                                  have p755_2 := h755c.2.2.1
                                  have p755_3 := h755c.2.2.2
                                  linarith only [h565, h744, h748, hc01, hc13, hlam, hphi, p755_1]
                                · have p755_0 := h755c.1
                                  have p755_1 := h755c.2.1
                                  have p755_2 := h755c.2.2.1
                                  have p755_3 := h755c.2.2.2
                                  linarith only [h564, hlam, p755_1]
                                · have p755_0 := h755c.1
                                  have p755_1 := h755c.2.1
                                  have p755_2 := h755c.2.2.1
                                  have p755_3 := h755c.2.2.2
                                  linarith only [h744, hlam, p755_0]
                                · have p755_0 := h755c.1
                                  have p755_1 := h755c.2.1
                                  have p755_2 := h755c.2.2.1
                                  have p755_3 := h755c.2.2.2
                                  linarith only [h745, hlam, p755_1]
                                · have p755_0 := h755c.1
                                  have p755_1 := h755c.2.1
                                  have p755_2 := h755c.2.2.1
                                  have p755_3 := h755c.2.2.2
                                  linarith only [hlam, p755_0]
                              · linarith only [h562, h565, h752, h754, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                            · linarith only [h565, h744, h745, h750, h752, h753, hc34, hlam, hphi, ht23, u2ehi4]
                          · linarith only [h565, h744, h746, h748, h752, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h565, h744, h748, h749, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h791 | h791
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h792 | h792
                        · linarith only [h219, h748, h792, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h794 | h794
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h795 | h795
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h796 | h796
                              · rcases h0bigk with h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [hlam, p797_0]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [h0, hlam, p797_1]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [h219, hlam, p797_0]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [h219, h563, h748, h792, h794, hc04, hc34, hlam, hphi, ht0b, ht23, ht45, ht5b, p797_1, u0elo1, u2ehi4]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [h479, hlam, p797_1]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  rcases p797_3 (m.d 0 1) (by simp) with h803 | h803
                                  · linarith only [h0, h803, hlam]
                                  · rcases p797_3 (m.d 0 2) (by simp) with h805 | h805
                                    · rcases p797_3 (m.d 0 3) (by simp) with h806 | h806
                                      · linarith only [h562, h806, hlam]
                                      · linarith only [h219, h806, hlam]
                                    · linarith only [h0, h805, hlam]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [hlam, p797_0]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [h564, h744, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p797_1, u0elo1, u2ehi4]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [h563, h792, h794, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p797_1, u0elo1, u2ehi4]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [h564, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p797_1, u0elo1, u2ehi4]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [h219, h748, hc01, hc34, hlam, hphi, ht12, ht23, p797_1]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [h562, hlam, p797_1]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [hlam, p797_0]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [h565, hlam, p797_1]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [h219, h564, h748, hc34, hlam, hphi, ht23, p797_1, u2ehi4]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  rcases p797_3 (m.d 0 1) (by simp) with h819 | h819
                                  · linarith only [h819, hlam, p797_0]
                                  · rcases p797_3 (m.d 0 2) (by simp) with h821 | h821
                                    · rcases p797_3 (m.d 0 3) (by simp) with h822 | h822
                                      · linarith only [h565, h822, hlam]
                                      · linarith only [h219, h822, hlam]
                                    · linarith only [h0, h821, hlam]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [h563, hlam, p797_0]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [h562, h794, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p797_1, u0elo3, u2ehi4]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [hlam, p797_0]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [h563, h564, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p797_1, u0elo1, u2ehi4]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [h479, h748, h791, hc01, hc34, hlam, hphi, ht12, ht23, p797_1]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [h564, hlam, p797_1]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [h744, hlam, p797_0]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [h745, hlam, p797_1]
                                · have p797_0 := h797c.1
                                  have p797_1 := h797c.2.1
                                  have p797_2 := h797c.2.2.1
                                  have p797_3 := h797c.2.2.2
                                  linarith only [hlam, p797_0]
                              · linarith only [h219, h748, h796, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                            · linarith only [h219, h744, h745, h748, h792, h794, h795, hc34, hlam, hphi, ht23, u2ehi4]
                          · linarith only [h219, h744, h748, h794, hc23, hc34, hlam, hphi]
                      · linarith only [h219, h744, h791, hlam]
                  · linarith only [h0, h562, h747, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h562, h746, hlam]
              · linarith only [h565, h744, h745, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h842 | h842
              · rcases m.htr 1 2 3 (by decide) (by decide) with h843 | h843
                · rcases m.htr 1 2 5 (by decide) (by decide) with h844 | h844
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h845 | h845
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h846 | h846
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h847 | h847
                        · linarith only [h562, h565, h847, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h849 | h849
                          · linarith only [h562, h564, h744, h849, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h851 | h851
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h852 | h852
                              · rcases h0bigk with h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c
                                · have p853_0 := h853c.1
                                  have p853_1 := h853c.2.1
                                  have p853_2 := h853c.2.2.1
                                  have p853_3 := h853c.2.2.2
                                  linarith only [hlam, p853_0]
                                · have p853_0 := h853c.1
                                  have p853_1 := h853c.2.1
                                  have p853_2 := h853c.2.2.1
                                  have p853_3 := h853c.2.2.2
                                  linarith only [h0, hlam, p853_1]
                                · have p853_0 := h853c.1
                                  have p853_1 := h853c.2.1
                                  have p853_2 := h853c.2.2.1
                                  have p853_3 := h853c.2.2.2
                                  linarith only [h219, hlam, p853_0]
                                · have p853_0 := h853c.1
                                  have p853_1 := h853c.2.1
                                  have p853_2 := h853c.2.2.1
                                  have p853_3 := h853c.2.2.2
                                  linarith only [h562, h744, h842, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p853_1, u0elo0, u2ehi2]
                                · have p853_0 := h853c.1
                                  have p853_1 := h853c.2.1
                                  have p853_2 := h853c.2.2.1
                                  have p853_3 := h853c.2.2.2
                                  linarith only [h479, hlam, p853_1]
                                · have p853_0 := h853c.1
                                  have p853_1 := h853c.2.1
                                  have p853_2 := h853c.2.2.1
                                  have p853_3 := h853c.2.2.2
                                  rcases p853_3 (m.d 0 1) (by simp) with h859 | h859
                                  · linarith only [h0, h859, hlam]
                                  · rcases p853_3 (m.d 0 2) (by simp) with h861 | h861
                                    · rcases p853_3 (m.d 0 3) (by simp) with h862 | h862
                                      · linarith only [h562, h862, hlam]
                                      · linarith only [h219, h862, hlam]
                                    · linarith only [h0, h861, hlam]
                                · have p853_0 := h853c.1
                                  have p853_1 := h853c.2.1
                                  have p853_2 := h853c.2.2.1
                                  have p853_3 := h853c.2.2.2
                                  linarith only [hlam, p853_0]
                                · have p853_0 := h853c.1
                                  have p853_1 := h853c.2.1
                                  have p853_2 := h853c.2.2.1
                                  have p853_3 := h853c.2.2.2
                                  linarith only [h562, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p853_1, u0elo1, u2ehi2]
                                · have p853_0 := h853c.1
                                  have p853_1 := h853c.2.1
                                  have p853_2 := h853c.2.2.1
                                  have p853_3 := h853c.2.2.2
                                  linarith only [h562, h744, h842, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p853_1, u0elo1, u2ehi2]
                                · have p853_0 := h853c.1
                                  have p853_1 := h853c.2.1
                                  have p853_2 := h853c.2.2.1
                                  have p853_3 := h853c.2.2.2
                                  linarith only [h562, h744, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p853_1, u0elo1, u2ehi2]
                                · have p853_0 := h853c.1
                                  have p853_1 := h853c.2.1
                                  have p853_2 := h853c.2.2.1
                                  have p853_3 := h853c.2.2.2
                                  linarith only [h744, h843, h845, h852, hc01, hc12, hlam, hphi, p853_1]
                                · have p853_0 := h853c.1
                                  have p853_1 := h853c.2.1
                                  have p853_2 := h853c.2.2.1
                                  have p853_3 := h853c.2.2.2
                                  linarith only [h562, hlam, p853_1]
                                · have p853_0 := h853c.1
                                  have p853_1 := h853c.2.1
                                  have p853_2 := h853c.2.2.1
                                  have p853_3 := h853c.2.2.2
                                  linarith only [hlam, p853_0]
                                · have p853_0 := h853c.1
                                  have p853_1 := h853c.2.1
                                  have p853_2 := h853c.2.2.1
                                  have p853_3 := h853c.2.2.2
                                  linarith only [h565, hlam, p853_1]
                                · have p853_0 := h853c.1
                                  have p853_1 := h853c.2.1
                                  have p853_2 := h853c.2.2.1
                                  have p853_3 := h853c.2.2.2
                                  linarith only [h744, hlam, p853_1]
                                · have p853_0 := h853c.1
                                  have p853_1 := h853c.2.1
                                  have p853_2 := h853c.2.2.1
                                  have p853_3 := h853c.2.2.2
                                  linarith only [h565, h843, h845, hc01, hc12, hlam, hphi, p853_1]
                                · have p853_0 := h853c.1
                                  have p853_1 := h853c.2.1
                                  have p853_2 := h853c.2.2.1
                                  have p853_3 := h853c.2.2.2
                                  linarith only [h563, hlam, p853_0]
                                · have p853_0 := h853c.1
                                  have p853_1 := h853c.2.1
                                  have p853_2 := h853c.2.2.1
                                  have p853_3 := h853c.2.2.2
                                  linarith only [h562, h565, h843, h845, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p853_1, u2ehi2]
                                · have p853_0 := h853c.1
                                  have p853_1 := h853c.2.1
                                  have p853_2 := h853c.2.2.1
                                  have p853_3 := h853c.2.2.2
                                  linarith only [hlam, p853_0]
                                · have p853_0 := h853c.1
                                  have p853_1 := h853c.2.1
                                  have p853_2 := h853c.2.2.1
                                  have p853_3 := h853c.2.2.2
                                  linarith only [h562, h565, h744, h843, h845, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p853_1, u2ehi2]
                                · have p853_0 := h853c.1
                                  have p853_1 := h853c.2.1
                                  have p853_2 := h853c.2.2.1
                                  have p853_3 := h853c.2.2.2
                                  linarith only [h565, h842, h843, h845, hc01, hc12, hlam, hphi, p853_1]
                                · have p853_0 := h853c.1
                                  have p853_1 := h853c.2.1
                                  have p853_2 := h853c.2.2.1
                                  have p853_3 := h853c.2.2.2
                                  linarith only [h564, hlam, p853_1]
                                · have p853_0 := h853c.1
                                  have p853_1 := h853c.2.1
                                  have p853_2 := h853c.2.2.1
                                  have p853_3 := h853c.2.2.2
                                  linarith only [h562, h564, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p853_1, u0elo1, u2ehi2]
                                · have p853_0 := h853c.1
                                  have p853_1 := h853c.2.1
                                  have p853_2 := h853c.2.2.1
                                  have p853_3 := h853c.2.2.2
                                  linarith only [h842, hlam, p853_1]
                                · have p853_0 := h853c.1
                                  have p853_1 := h853c.2.1
                                  have p853_2 := h853c.2.2.1
                                  have p853_3 := h853c.2.2.2
                                  linarith only [hlam, p853_0]
                              · linarith only [h562, h565, h852, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                            · linarith only [h842, h851, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi3]
                      · linarith only [h563, h565, h845, h846, hc35, hlam, hphi, ht23, u2ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h888 | h888
                      · linarith only [h562, h744, h845, h888, hc34, hlam, hphi, ht23, u2ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h890 | h890
                        · linarith only [h219, h562, h845, h890, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h892 | h892
                          · linarith only [h479, h562, h888, h892, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h894 | h894
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h895 | h895
                              · rcases h0bigk with h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [hlam, p896_0]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [h0, hlam, p896_1]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [h219, hlam, p896_0]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [h219, h888, h895, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p896_1]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [h479, hlam, p896_1]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  rcases p896_3 (m.d 0 1) (by simp) with h902 | h902
                                  · linarith only [h0, h902, hlam]
                                  · rcases p896_3 (m.d 0 2) (by simp) with h904 | h904
                                    · rcases p896_3 (m.d 0 3) (by simp) with h905 | h905
                                      · linarith only [h562, h905, hlam]
                                      · linarith only [h219, h905, hlam]
                                    · linarith only [h0, h904, hlam]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [hlam, p896_0]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [h562, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p896_1, u0elo1, u2ehi2]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [h563, h892, h894, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p896_1, u0elo1, u2ehi2]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [h562, h744, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p896_1, u0elo1, u2ehi2]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [h219, h888, h895, hc01, hc34, hlam, hphi, ht12, ht23, p896_1]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [h562, hlam, p896_1]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [hlam, p896_0]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [h565, hlam, p896_1]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [h744, hlam, p896_1]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  rcases p896_3 (m.d 0 1) (by simp) with h918 | h918
                                  · linarith only [h918, hlam, p896_0]
                                  · rcases p896_3 (m.d 0 2) (by simp) with h920 | h920
                                    · rcases p896_3 (m.d 0 3) (by simp) with h921 | h921
                                      · linarith only [h565, h921, hlam]
                                      · linarith only [h219, h921, hlam]
                                    · linarith only [h0, h920, hlam]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [h563, hlam, p896_0]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [h562, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p896_1, u0elo3, u2ehi2]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [hlam, p896_0]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [h562, h563, h744, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p896_1, u0elo1, u2ehi2]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  rcases p896_3 (m.d 0 1) (by simp) with h929 | h929
                                  · linarith only [h479, h929, hlam]
                                  · rcases p896_3 (m.d 0 2) (by simp) with h931 | h931
                                    · rcases p896_3 (m.d 0 3) (by simp) with h932 | h932
                                      · linarith only [h744, h932, hlam]
                                      · linarith only [h219, h932, hlam]
                                    · linarith only [h0, h931, hlam]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [h564, hlam, p896_1]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [h562, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p896_1, u0elo4, u2ehi2]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [h842, hlam, p896_1]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [hlam, p896_0]
                              · linarith only [h563, h845, h894, h895, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · linarith only [h563, h842, h894, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                  · linarith only [h0, h562, h844, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h562, h843, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h944 | h944
                · rcases m.htr 1 2 5 (by decide) (by decide) with h945 | h945
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h946 | h946
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h947 | h947
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h948 | h948
                        · linarith only [h562, h565, h948, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h950 | h950
                          · linarith only [h562, h744, h950, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h952 | h952
                            · linarith only [h563, h842, h952, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h954 | h954
                              · linarith only [h563, h842, h944, h946, h954, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · linarith only [h562, h565, h954, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h562, h565, h946, h947, hc35, hlam, hphi, ht23, u2ehi2]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h958 | h958
                      · linarith only [h562, h744, h946, h958, hc34, hlam, hphi, ht23, u2ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h960 | h960
                        · linarith only [h219, h562, h946, h960, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h962 | h962
                          · linarith only [h219, h479, h562, h946, h958, h962, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h964 | h964
                            · linarith only [h563, h842, h964, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h966 | h966
                              · linarith only [h562, h565, h842, h966, hc34, hlam, hphi, ht23, u2ehi2]
                              · linarith only [h219, h946, h966, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h0, h562, h945, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h562, h944, hlam]
        · linarith only [h562, h564, hc25, hlam, hphi, u2ehi2]
      · linarith only [h562, h563, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h973 | h973
      · linarith only [h562, h973, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h975 | h975
        · linarith only [h562, h975, hc23, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h977 | h977
          · rcases m.htr 0 3 5 (by decide) (by decide) with h978 | h978
            · rcases m.htr 0 4 5 (by decide) (by decide) with h979 | h979
              · rcases m.htr 1 2 3 (by decide) (by decide) with h980 | h980
                · rcases m.htr 1 2 5 (by decide) (by decide) with h981 | h981
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h982 | h982
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h983 | h983
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h984 | h984
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h985 | h985
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h986 | h986
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h987 | h987
                              · rcases h0bigk with h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [hlam, p988_0]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h0, hlam, p988_1]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h219, hlam, p988_0]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h975, h979, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p988_1, u0elo0, u2ehi0]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h479, hlam, p988_1]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h562, h980, hc01, hc12, hlam, hphi, p988_1]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [hlam, p988_0]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h562, hlam, p988_0]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h973, hlam, p988_1]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h975, hlam, p988_0]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h562, h980, hc01, hc12, hlam, hphi, p988_1]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h562, h980, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p988_1, u2ehi0]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [hlam, p988_0]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h562, h973, h980, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p988_1, u2ehi0]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h562, h975, h980, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p988_1, u2ehi0]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h973, h980, h984, hc01, hc12, hlam, hphi, p988_1]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h973, h980, h984, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p988_1, u2ehi0]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h977, hlam, p988_0]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [hlam, p988_0]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h973, h975, h980, h984, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p988_1, u2ehi0]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h975, h980, h984, h986, hc01, hc12, hlam, hphi, p988_1]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h975, h980, h984, h986, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p988_1, u2ehi0]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h978, hlam, p988_0]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h979, hlam, p988_1]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [hlam, p988_0]
                              · rcases h0bigk with h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c
                                · have p1014_0 := h1014c.1
                                  have p1014_1 := h1014c.2.1
                                  have p1014_2 := h1014c.2.2.1
                                  have p1014_3 := h1014c.2.2.2
                                  linarith only [hlam, p1014_0]
                                · have p1014_0 := h1014c.1
                                  have p1014_1 := h1014c.2.1
                                  have p1014_2 := h1014c.2.2.1
                                  have p1014_3 := h1014c.2.2.2
                                  linarith only [h0, hlam, p1014_1]
                                · have p1014_0 := h1014c.1
                                  have p1014_1 := h1014c.2.1
                                  have p1014_2 := h1014c.2.2.1
                                  have p1014_3 := h1014c.2.2.2
                                  linarith only [h219, hlam, p1014_0]
                                · have p1014_0 := h1014c.1
                                  have p1014_1 := h1014c.2.1
                                  have p1014_2 := h1014c.2.2.1
                                  have p1014_3 := h1014c.2.2.2
                                  linarith only [h979, h987, hc34, hlam, hphi, ht0b, ht45, ht5b, p1014_1, u0elo0]
                                · have p1014_0 := h1014c.1
                                  have p1014_1 := h1014c.2.1
                                  have p1014_2 := h1014c.2.2.1
                                  have p1014_3 := h1014c.2.2.2
                                  linarith only [h479, hlam, p1014_1]
                                · have p1014_0 := h1014c.1
                                  have p1014_1 := h1014c.2.1
                                  have p1014_2 := h1014c.2.2.1
                                  have p1014_3 := h1014c.2.2.2
                                  linarith only [h562, h980, hc01, hc12, hlam, hphi, p1014_1]
                                · have p1014_0 := h1014c.1
                                  have p1014_1 := h1014c.2.1
                                  have p1014_2 := h1014c.2.2.1
                                  have p1014_3 := h1014c.2.2.2
                                  linarith only [hlam, p1014_0]
                                · have p1014_0 := h1014c.1
                                  have p1014_1 := h1014c.2.1
                                  have p1014_2 := h1014c.2.2.1
                                  have p1014_3 := h1014c.2.2.2
                                  linarith only [h562, hlam, p1014_0]
                                · have p1014_0 := h1014c.1
                                  have p1014_1 := h1014c.2.1
                                  have p1014_2 := h1014c.2.2.1
                                  have p1014_3 := h1014c.2.2.2
                                  linarith only [h973, hlam, p1014_1]
                                · have p1014_0 := h1014c.1
                                  have p1014_1 := h1014c.2.1
                                  have p1014_2 := h1014c.2.2.1
                                  have p1014_3 := h1014c.2.2.2
                                  linarith only [h975, hlam, p1014_0]
                                · have p1014_0 := h1014c.1
                                  have p1014_1 := h1014c.2.1
                                  have p1014_2 := h1014c.2.2.1
                                  have p1014_3 := h1014c.2.2.2
                                  linarith only [h562, h980, hc01, hc12, hlam, hphi, p1014_1]
                                · have p1014_0 := h1014c.1
                                  have p1014_1 := h1014c.2.1
                                  have p1014_2 := h1014c.2.2.1
                                  have p1014_3 := h1014c.2.2.2
                                  linarith only [h562, h980, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1014_1, u2ehi0]
                                · have p1014_0 := h1014c.1
                                  have p1014_1 := h1014c.2.1
                                  have p1014_2 := h1014c.2.2.1
                                  have p1014_3 := h1014c.2.2.2
                                  linarith only [hlam, p1014_0]
                                · have p1014_0 := h1014c.1
                                  have p1014_1 := h1014c.2.1
                                  have p1014_2 := h1014c.2.2.1
                                  have p1014_3 := h1014c.2.2.2
                                  linarith only [h562, h979, h980, h987, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1014_1]
                                · have p1014_0 := h1014c.1
                                  have p1014_1 := h1014c.2.1
                                  have p1014_2 := h1014c.2.2.1
                                  have p1014_3 := h1014c.2.2.2
                                  linarith only [h479, h562, h980, hc01, hc12, hlam, hphi, p1014_1]
                                · have p1014_0 := h1014c.1
                                  have p1014_1 := h1014c.2.1
                                  have p1014_2 := h1014c.2.2.1
                                  have p1014_3 := h1014c.2.2.2
                                  linarith only [h973, h980, h984, hc01, hc12, hlam, hphi, p1014_1]
                                · have p1014_0 := h1014c.1
                                  have p1014_1 := h1014c.2.1
                                  have p1014_2 := h1014c.2.2.1
                                  have p1014_3 := h1014c.2.2.2
                                  linarith only [h973, h980, h984, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1014_1, u2ehi0]
                                · have p1014_0 := h1014c.1
                                  have p1014_1 := h1014c.2.1
                                  have p1014_2 := h1014c.2.2.1
                                  have p1014_3 := h1014c.2.2.2
                                  linarith only [h977, hlam, p1014_0]
                                · have p1014_0 := h1014c.1
                                  have p1014_1 := h1014c.2.1
                                  have p1014_2 := h1014c.2.2.1
                                  have p1014_3 := h1014c.2.2.2
                                  linarith only [hlam, p1014_0]
                                · have p1014_0 := h1014c.1
                                  have p1014_1 := h1014c.2.1
                                  have p1014_2 := h1014c.2.2.1
                                  have p1014_3 := h1014c.2.2.2
                                  linarith only [h973, h975, h980, h984, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1014_1, u2ehi0]
                                · have p1014_0 := h1014c.1
                                  have p1014_1 := h1014c.2.1
                                  have p1014_2 := h1014c.2.2.1
                                  have p1014_3 := h1014c.2.2.2
                                  linarith only [h975, h980, h984, h986, hc01, hc12, hlam, hphi, p1014_1]
                                · have p1014_0 := h1014c.1
                                  have p1014_1 := h1014c.2.1
                                  have p1014_2 := h1014c.2.2.1
                                  have p1014_3 := h1014c.2.2.2
                                  linarith only [h975, h980, h984, h986, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1014_1, u2ehi0]
                                · have p1014_0 := h1014c.1
                                  have p1014_1 := h1014c.2.1
                                  have p1014_2 := h1014c.2.2.1
                                  have p1014_3 := h1014c.2.2.2
                                  linarith only [h978, hlam, p1014_0]
                                · have p1014_0 := h1014c.1
                                  have p1014_1 := h1014c.2.1
                                  have p1014_2 := h1014c.2.2.1
                                  have p1014_3 := h1014c.2.2.2
                                  linarith only [h979, hlam, p1014_1]
                                · have p1014_0 := h1014c.1
                                  have p1014_1 := h1014c.2.1
                                  have p1014_2 := h1014c.2.2.1
                                  have p1014_3 := h1014c.2.2.2
                                  linarith only [hlam, p1014_0]
                            · linarith only [h973, h986, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                          · linarith only [h562, h985, hc35, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h562, h984, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h562, h978, h980, h983, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi0]
                    · linarith only [h562, h977, h980, h982, hlam]
                  · linarith only [h980, h981, hc25, hlam, hphi, u2ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1046 | h1046
                  · linarith only [h1046, h980, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1048 | h1048
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1049 | h1049
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1050 | h1050
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1051 | h1051
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1052 | h1052
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1053 | h1053
                              · rcases h0bigk with h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c
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
                                  linarith only [h219, hlam, p1054_0]
                                · have p1054_0 := h1054c.1
                                  have p1054_1 := h1054c.2.1
                                  have p1054_2 := h1054c.2.2.1
                                  have p1054_3 := h1054c.2.2.2
                                  linarith only [h975, h979, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1054_1, u0elo0, u2ehi0]
                                · have p1054_0 := h1054c.1
                                  have p1054_1 := h1054c.2.1
                                  have p1054_2 := h1054c.2.2.1
                                  have p1054_3 := h1054c.2.2.2
                                  linarith only [h479, hlam, p1054_1]
                                · have p1054_0 := h1054c.1
                                  have p1054_1 := h1054c.2.1
                                  have p1054_2 := h1054c.2.2.1
                                  have p1054_3 := h1054c.2.2.2
                                  linarith only [h0, h1046, h1050, h1052, hc01, hc23, hlam, hphi, ht12, p1054_1]
                                · have p1054_0 := h1054c.1
                                  have p1054_1 := h1054c.2.1
                                  have p1054_2 := h1054c.2.2.1
                                  have p1054_3 := h1054c.2.2.2
                                  linarith only [hlam, p1054_0]
                                · have p1054_0 := h1054c.1
                                  have p1054_1 := h1054c.2.1
                                  have p1054_2 := h1054c.2.2.1
                                  have p1054_3 := h1054c.2.2.2
                                  linarith only [h562, hlam, p1054_0]
                                · have p1054_0 := h1054c.1
                                  have p1054_1 := h1054c.2.1
                                  have p1054_2 := h1054c.2.2.1
                                  have p1054_3 := h1054c.2.2.2
                                  linarith only [h973, hlam, p1054_1]
                                · have p1054_0 := h1054c.1
                                  have p1054_1 := h1054c.2.1
                                  have p1054_2 := h1054c.2.2.1
                                  have p1054_3 := h1054c.2.2.2
                                  linarith only [h975, hlam, p1054_0]
                                · have p1054_0 := h1054c.1
                                  have p1054_1 := h1054c.2.1
                                  have p1054_2 := h1054c.2.2.1
                                  have p1054_3 := h1054c.2.2.2
                                  rcases p1054_3 (m.d 0 1) (by simp) with h1065 | h1065
                                  · linarith only [h1065, h219, hlam]
                                  · rcases p1054_3 (m.d 0 2) (by simp) with h1067 | h1067
                                    · linarith only [h1067, h562, hlam]
                                    · linarith only [h0, h1067, hlam]
                                · have p1054_0 := h1054c.1
                                  have p1054_1 := h1054c.2.1
                                  have p1054_2 := h1054c.2.2.1
                                  have p1054_3 := h1054c.2.2.2
                                  linarith only [hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1054_1, u0elo2, u2ehi0]
                                · have p1054_0 := h1054c.1
                                  have p1054_1 := h1054c.2.1
                                  have p1054_2 := h1054c.2.2.1
                                  have p1054_3 := h1054c.2.2.2
                                  linarith only [hlam, p1054_0]
                                · have p1054_0 := h1054c.1
                                  have p1054_1 := h1054c.2.1
                                  have p1054_2 := h1054c.2.2.1
                                  have p1054_3 := h1054c.2.2.2
                                  linarith only [h975, h979, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1054_1, u0elo2, u2ehi0]
                                · have p1054_0 := h1054c.1
                                  have p1054_1 := h1054c.2.1
                                  have p1054_2 := h1054c.2.2.1
                                  have p1054_3 := h1054c.2.2.2
                                  linarith only [h975, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1054_1, u0elo2, u2ehi0]
                                · have p1054_0 := h1054c.1
                                  have p1054_1 := h1054c.2.1
                                  have p1054_2 := h1054c.2.2.1
                                  have p1054_3 := h1054c.2.2.2
                                  rcases p1054_3 (m.d 0 1) (by simp) with h1074 | h1074
                                  · linarith only [h1074, hlam, p1054_0]
                                  · rcases p1054_3 (m.d 0 2) (by simp) with h1076 | h1076
                                    · linarith only [h1076, h973, hlam]
                                    · linarith only [h0, h1076, hlam]
                                · have p1054_0 := h1054c.1
                                  have p1054_1 := h1054c.2.1
                                  have p1054_2 := h1054c.2.2.1
                                  have p1054_3 := h1054c.2.2.2
                                  linarith only [hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1054_1, u0elo3, u2ehi0]
                                · have p1054_0 := h1054c.1
                                  have p1054_1 := h1054c.2.1
                                  have p1054_2 := h1054c.2.2.1
                                  have p1054_3 := h1054c.2.2.2
                                  linarith only [h977, hlam, p1054_0]
                                · have p1054_0 := h1054c.1
                                  have p1054_1 := h1054c.2.1
                                  have p1054_2 := h1054c.2.2.1
                                  have p1054_3 := h1054c.2.2.2
                                  linarith only [hlam, p1054_0]
                                · have p1054_0 := h1054c.1
                                  have p1054_1 := h1054c.2.1
                                  have p1054_2 := h1054c.2.2.1
                                  have p1054_3 := h1054c.2.2.2
                                  linarith only [h975, h977, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1054_1, u0elo2, u2ehi0]
                                · have p1054_0 := h1054c.1
                                  have p1054_1 := h1054c.2.1
                                  have p1054_2 := h1054c.2.2.1
                                  have p1054_3 := h1054c.2.2.2
                                  rcases p1054_3 (m.d 0 1) (by simp) with h1083 | h1083
                                  · linarith only [h1083, h479, hlam]
                                  · rcases p1054_3 (m.d 0 2) (by simp) with h1085 | h1085
                                    · linarith only [h1085, h975, hlam]
                                    · linarith only [h0, h1085, hlam]
                                · have p1054_0 := h1054c.1
                                  have p1054_1 := h1054c.2.1
                                  have p1054_2 := h1054c.2.2.1
                                  have p1054_3 := h1054c.2.2.2
                                  linarith only [hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1054_1, u0elo4, u2ehi0]
                                · have p1054_0 := h1054c.1
                                  have p1054_1 := h1054c.2.1
                                  have p1054_2 := h1054c.2.2.1
                                  have p1054_3 := h1054c.2.2.2
                                  linarith only [h978, hlam, p1054_0]
                                · have p1054_0 := h1054c.1
                                  have p1054_1 := h1054c.2.1
                                  have p1054_2 := h1054c.2.2.1
                                  have p1054_3 := h1054c.2.2.2
                                  linarith only [h979, hlam, p1054_1]
                                · have p1054_0 := h1054c.1
                                  have p1054_1 := h1054c.2.1
                                  have p1054_2 := h1054c.2.2.1
                                  have p1054_3 := h1054c.2.2.2
                                  linarith only [hlam, p1054_0]
                              · rcases h0bigk with h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c
                                · have p1092_0 := h1092c.1
                                  have p1092_1 := h1092c.2.1
                                  have p1092_2 := h1092c.2.2.1
                                  have p1092_3 := h1092c.2.2.2
                                  linarith only [hlam, p1092_0]
                                · have p1092_0 := h1092c.1
                                  have p1092_1 := h1092c.2.1
                                  have p1092_2 := h1092c.2.2.1
                                  have p1092_3 := h1092c.2.2.2
                                  linarith only [h0, hlam, p1092_1]
                                · have p1092_0 := h1092c.1
                                  have p1092_1 := h1092c.2.1
                                  have p1092_2 := h1092c.2.2.1
                                  have p1092_3 := h1092c.2.2.2
                                  linarith only [h219, hlam, p1092_0]
                                · have p1092_0 := h1092c.1
                                  have p1092_1 := h1092c.2.1
                                  have p1092_2 := h1092c.2.2.1
                                  have p1092_3 := h1092c.2.2.2
                                  linarith only [h1053, h979, hc34, hlam, hphi, ht0b, ht45, ht5b, p1092_1, u0elo0]
                                · have p1092_0 := h1092c.1
                                  have p1092_1 := h1092c.2.1
                                  have p1092_2 := h1092c.2.2.1
                                  have p1092_3 := h1092c.2.2.2
                                  linarith only [h479, hlam, p1092_1]
                                · have p1092_0 := h1092c.1
                                  have p1092_1 := h1092c.2.1
                                  have p1092_2 := h1092c.2.2.1
                                  have p1092_3 := h1092c.2.2.2
                                  linarith only [h0, h1046, h1050, h1052, hc01, hc23, hlam, hphi, ht12, p1092_1]
                                · have p1092_0 := h1092c.1
                                  have p1092_1 := h1092c.2.1
                                  have p1092_2 := h1092c.2.2.1
                                  have p1092_3 := h1092c.2.2.2
                                  linarith only [hlam, p1092_0]
                                · have p1092_0 := h1092c.1
                                  have p1092_1 := h1092c.2.1
                                  have p1092_2 := h1092c.2.2.1
                                  have p1092_3 := h1092c.2.2.2
                                  linarith only [h562, hlam, p1092_0]
                                · have p1092_0 := h1092c.1
                                  have p1092_1 := h1092c.2.1
                                  have p1092_2 := h1092c.2.2.1
                                  have p1092_3 := h1092c.2.2.2
                                  linarith only [h973, hlam, p1092_1]
                                · have p1092_0 := h1092c.1
                                  have p1092_1 := h1092c.2.1
                                  have p1092_2 := h1092c.2.2.1
                                  have p1092_3 := h1092c.2.2.2
                                  linarith only [h975, hlam, p1092_0]
                                · have p1092_0 := h1092c.1
                                  have p1092_1 := h1092c.2.1
                                  have p1092_2 := h1092c.2.2.1
                                  have p1092_3 := h1092c.2.2.2
                                  rcases p1092_3 (m.d 0 1) (by simp) with h1103 | h1103
                                  · linarith only [h1103, h219, hlam]
                                  · rcases p1092_3 (m.d 0 2) (by simp) with h1105 | h1105
                                    · linarith only [h1105, h562, hlam]
                                    · linarith only [h0, h1105, hlam]
                                · have p1092_0 := h1092c.1
                                  have p1092_1 := h1092c.2.1
                                  have p1092_2 := h1092c.2.2.1
                                  have p1092_3 := h1092c.2.2.2
                                  linarith only [hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1092_1, u0elo2, u2ehi0]
                                · have p1092_0 := h1092c.1
                                  have p1092_1 := h1092c.2.1
                                  have p1092_2 := h1092c.2.2.1
                                  have p1092_3 := h1092c.2.2.2
                                  linarith only [hlam, p1092_0]
                                · have p1092_0 := h1092c.1
                                  have p1092_1 := h1092c.2.1
                                  have p1092_2 := h1092c.2.2.1
                                  have p1092_3 := h1092c.2.2.2
                                  linarith only [h1053, h979, hc34, hlam, hphi, ht0b, ht45, ht5b, p1092_1, u0elo2]
                                · have p1092_0 := h1092c.1
                                  have p1092_1 := h1092c.2.1
                                  have p1092_2 := h1092c.2.2.1
                                  have p1092_3 := h1092c.2.2.2
                                  linarith only [h975, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1092_1, u0elo2, u2ehi0]
                                · have p1092_0 := h1092c.1
                                  have p1092_1 := h1092c.2.1
                                  have p1092_2 := h1092c.2.2.1
                                  have p1092_3 := h1092c.2.2.2
                                  rcases p1092_3 (m.d 0 1) (by simp) with h1112 | h1112
                                  · linarith only [h1112, hlam, p1092_0]
                                  · rcases p1092_3 (m.d 0 2) (by simp) with h1114 | h1114
                                    · linarith only [h1114, h973, hlam]
                                    · linarith only [h0, h1114, hlam]
                                · have p1092_0 := h1092c.1
                                  have p1092_1 := h1092c.2.1
                                  have p1092_2 := h1092c.2.2.1
                                  have p1092_3 := h1092c.2.2.2
                                  linarith only [hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1092_1, u0elo3, u2ehi0]
                                · have p1092_0 := h1092c.1
                                  have p1092_1 := h1092c.2.1
                                  have p1092_2 := h1092c.2.2.1
                                  have p1092_3 := h1092c.2.2.2
                                  linarith only [h977, hlam, p1092_0]
                                · have p1092_0 := h1092c.1
                                  have p1092_1 := h1092c.2.1
                                  have p1092_2 := h1092c.2.2.1
                                  have p1092_3 := h1092c.2.2.2
                                  linarith only [hlam, p1092_0]
                                · have p1092_0 := h1092c.1
                                  have p1092_1 := h1092c.2.1
                                  have p1092_2 := h1092c.2.2.1
                                  have p1092_3 := h1092c.2.2.2
                                  linarith only [h975, h977, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1092_1, u0elo2, u2ehi0]
                                · have p1092_0 := h1092c.1
                                  have p1092_1 := h1092c.2.1
                                  have p1092_2 := h1092c.2.2.1
                                  have p1092_3 := h1092c.2.2.2
                                  rcases p1092_3 (m.d 0 1) (by simp) with h1121 | h1121
                                  · linarith only [h1121, h479, hlam]
                                  · rcases p1092_3 (m.d 0 2) (by simp) with h1123 | h1123
                                    · linarith only [h1123, h975, hlam]
                                    · linarith only [h0, h1123, hlam]
                                · have p1092_0 := h1092c.1
                                  have p1092_1 := h1092c.2.1
                                  have p1092_2 := h1092c.2.2.1
                                  have p1092_3 := h1092c.2.2.2
                                  linarith only [hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1092_1, u0elo4, u2ehi0]
                                · have p1092_0 := h1092c.1
                                  have p1092_1 := h1092c.2.1
                                  have p1092_2 := h1092c.2.2.1
                                  have p1092_3 := h1092c.2.2.2
                                  linarith only [h978, hlam, p1092_0]
                                · have p1092_0 := h1092c.1
                                  have p1092_1 := h1092c.2.1
                                  have p1092_2 := h1092c.2.2.1
                                  have p1092_3 := h1092c.2.2.2
                                  linarith only [h979, hlam, p1092_1]
                                · have p1092_0 := h1092c.1
                                  have p1092_1 := h1092c.2.1
                                  have p1092_2 := h1092c.2.2.1
                                  have p1092_3 := h1092c.2.2.2
                                  linarith only [hlam, p1092_0]
                            · linarith only [h1052, h973, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                          · linarith only [h1051, h562, hc35, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h1050, h562, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h1049, h978, h980, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi1]
                    · linarith only [h1048, h219, h977, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1135 | h1135
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1136 | h1136
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1137 | h1137
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1138 | h1138
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1139 | h1139
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1140 | h1140
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1141 | h1141
                            · linarith only [h1141, h973, h979, hc24, hlam, hphi, u2ehi0]
                            · linarith only [h1141, h973, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                          · linarith only [h1140, h562, h978, hlam]
                        · linarith only [h1139, h562, h977, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi0]
                      · linarith only [h1135, h1138, h562, h978, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi0]
                    · linarith only [h1135, h1137, h562, h977, hlam]
                  · linarith only [h1135, h1136, hc25, hlam, hphi, u2ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1149 | h1149
                  · linarith only [h1135, h1149, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1151 | h1151
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1152 | h1152
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1153 | h1153
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1154 | h1154
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1155 | h1155
                            · linarith only [h1155, h973, h979, hc24, hlam, hphi, u2ehi0]
                            · linarith only [h1155, h973, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                          · linarith only [h1154, h978, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi2]
                        · linarith only [h1153, h562, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h1152, h219, h978, hlam]
                    · linarith only [h1151, h219, h977, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1162 | h1162
              · linarith only [h1162, h977, h978, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1164 | h1164
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1165 | h1165
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1166 | h1166
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1167 | h1167
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1168 | h1168
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1169 | h1169
                          · linarith only [h1169, h562, h978, hc23, hlam, hphi, u2ehi0]
                          · linarith only [h1164, h1167, h1169, h562, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · linarith only [h1164, h1167, h1168, h562, h977, h978, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h1164, h1167, h562, hc35, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h1164, h1166, h562, h977, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi0]
                  · linarith only [h1164, h1165, h562, hc25, hlam, hphi, u2ehi0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1176 | h1176
                  · linarith only [h1164, h1176, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1178 | h1178
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1179 | h1179
                      · linarith only [h1164, h1179, h562, h978, hc23, hlam, hphi, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1181 | h1181
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1182 | h1182
                          · linarith only [h1179, h1182, h219, h973, h977, hc23, hlam, hphi, u2ehi0]
                          · linarith only [h1182, h562, hc35, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h1164, h1181, h977, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi1]
                    · linarith only [h1178, h977, h978, hc13, hc35, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1187 | h1187
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1188 | h1188
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1189 | h1189
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1190 | h1190
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1191 | h1191
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1192 | h1192
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1193 | h1193
                        · linarith only [h1187, h1189, h1193, h977, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h1193, h562, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h1187, h1191, h1192, h975, h977, hc35, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h1189, h1191, h562, hc34, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1189, h1190, h562, hc25, hlam, hphi, u2ehi0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1199 | h1199
                  · linarith only [h1189, h1199, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1201 | h1201
                    · linarith only [h1187, h1189, h1201, h975, h977, hc23, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1203 | h1203
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1204 | h1204
                        · linarith only [h1199, h1201, h1203, h1204, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h1204, h562, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h1187, h1203, h219, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
              · linarith only [h1187, h1188, h977, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1209 | h1209
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1210 | h1210
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1211 | h1211
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1212 | h1212
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1213 | h1213
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1214 | h1214
                        · linarith only [h1214, h562, h977, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h1210, h1212, h1214, h562, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h1212, h1213, h977, hc03, hc35, hlam, hphi]
                    · linarith only [h1210, h1212, h562, hc34, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1210, h1211, h562, hc25, hlam, hphi, u2ehi0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1220 | h1220
                  · linarith only [h1210, h1220, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1222 | h1222
                    · linarith only [h1210, h1222, h562, h977, hc23, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1224 | h1224
                      · linarith only [h1187, h1222, h1224, h562, hc34, hlam, hphi, ht23, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1226 | h1226
                        · linarith only [h1210, h1222, h1226, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h1226, h562, hc34, hlam, hphi, ht23, u2ehi0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1229 | h1229
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1230 | h1230
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1231 | h1231
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1232 | h1232
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1233 | h1233
                        · linarith only [h1233, h562, h977, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h1233, h562, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h1231, h1232, h562, h977, hc35, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h1229, h1231, h562, hc34, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1229, h1230, h562, hc25, hlam, hphi, u2ehi0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1239 | h1239
                  · linarith only [h1229, h1239, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1241 | h1241
                    · linarith only [h1229, h1241, h562, h977, hc23, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1243 | h1243
                      · linarith only [h1187, h1241, h1243, h562, hc34, hlam, hphi, ht23, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1245 | h1245
                        · linarith only [h1229, h1241, h1245, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h1245, h562, hc34, hlam, hphi, ht23, u2ehi0]

theorem r1l7_20_12_13_M_LI_L_R_L_I_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h2ehi := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h219 | h219
  · exact r1l7_20_12_13_M_LI_L_R_L_I_x1_x0 m hb0 hb2 hb3 h0 h219
  · exact r1l7_20_12_13_M_LI_L_R_L_I_x1_x1 m hb0 hb2 hb3 h0 h219

theorem r1l7_20_12_13_M_LI_L_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h2ehi := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_13_M_LI_L_R_L_I_x0 m hb0 hb2 hb3 h0
  · exact r1l7_20_12_13_M_LI_L_R_L_I_x1 m hb0 hb2 hb3 h0

end R2N4
