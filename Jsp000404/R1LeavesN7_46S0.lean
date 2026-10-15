import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5094000 in
theorem r1l7_10_12_23_L_I_L_R_M_IR_s0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h451 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h452 | h452
  · rcases m.htr 0 2 4 (by decide) (by decide) with h453 | h453
    · rcases m.htr 0 2 5 (by decide) (by decide) with h454 | h454
      · rcases m.htr 0 3 4 (by decide) (by decide) with h455 | h455
        · rcases m.htr 0 3 5 (by decide) (by decide) with h456 | h456
          · rcases m.htr 0 4 5 (by decide) (by decide) with h457 | h457
            · rcases m.htr 1 2 3 (by decide) (by decide) with h458 | h458
              · rcases m.htr 1 2 4 (by decide) (by decide) with h459 | h459
                · rcases m.htr 1 2 5 (by decide) (by decide) with h460 | h460
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h461 | h461
                    · linarith only [h0, h451, h461, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h451, h455, h458, h461, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h0, h451, h454, h460, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                · linarith only [h0, h451, h453, h455, h459, hlam]
              · linarith only [h0, h451, h453, h455, h458, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h467 | h467
              · rcases m.htr 1 2 4 (by decide) (by decide) with h468 | h468
                · rcases m.htr 1 2 5 (by decide) (by decide) with h469 | h469
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h470 | h470
                    · linarith only [h0, h451, h470, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h451, h455, h470, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                  · linarith only [h0, h451, h467, h469, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h451, h453, h467, h468, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
              · linarith only [h0, h451, h467, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · linarith only [h455, h456, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h477 | h477
          · linarith only [h455, h477, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h479 | h479
            · rcases m.htr 1 2 3 (by decide) (by decide) with h480 | h480
              · rcases m.htr 1 2 4 (by decide) (by decide) with h481 | h481
                · rcases m.htr 1 2 5 (by decide) (by decide) with h482 | h482
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h483 | h483
                    · linarith only [h451, h455, h483, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h485 | h485
                      · linarith only [h451, h477, h485, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h487 | h487
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h488 | h488
                          · linarith only [h451, h455, h480, h488, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h490 | h490
                            · linarith only [h451, h477, h480, h490, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h492 | h492
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h493 | h493
                                · rcases h0bigk with h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [hlam, p494_0]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h0, hlam, p494_1]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h0, h451, h480, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p494_1, u2ehi2]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h0, h451, h477, h479, h480, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p494_1, u2ehi2]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h0, h451, h477, h480, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p494_1, u2ehi2]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h0, h451, h480, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p494_1, u2ehi2]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [hlam, p494_0]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    rcases p494_3 (m.d 0 1) (by simp) with h502 | h502
                                    · linarith only [h0, h502, hlam]
                                    · linarith only [h451, h502, hlam]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    rcases p494_3 (m.d 0 1) (by simp) with h505 | h505
                                    · linarith only [h0, h505, hlam]
                                    · linarith only [h0, h451, h480, h505, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p494_1, u2ehi2]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    rcases p494_3 (m.d 0 1) (by simp) with h508 | h508
                                    · linarith only [h0, h508, hlam]
                                    · linarith only [h0, h451, h480, h508, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p494_1, u2ehi2]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h451, hlam, p494_1]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h452, hlam, p494_1]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [hlam, p494_0]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h455, hlam, p494_1]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h477, hlam, p494_1]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h451, h480, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p494_1, u2ehi2]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h453, hlam, p494_0]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h451, h455, h480, hc34, hlam, hphi, ht23, p494_1, u2ehi2]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [hlam, p494_0]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h454, h455, hc34, hlam, hphi, ht23, p494_1, u2ehi4]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h451, h480, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p494_1, u2ehi2]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h454, hlam, p494_1]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h451, h477, h480, hc35, hlam, hphi, ht23, p494_1, u2ehi2]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [h479, hlam, p494_1]
                                  · have p494_0 := h494c.1
                                    have p494_1 := h494c.2.1
                                    have p494_2 := h494c.2.2.1
                                    have p494_3 := h494c.2.2.2
                                    linarith only [hlam, p494_0]
                                · linarith only [h0, h453, h492, h493, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h455, h479, h488, h492, hc34, hlam, hphi, ht23, u2ehi2]
                        · linarith only [h455, h479, h481, h487, hc34, hlam, hphi, ht23, u2ehi3]
                  · linarith only [h0, h451, h480, h482, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h451, h480, h481, hc24, hlam, hphi, u2ehi2]
              · linarith only [h0, h451, h480, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h532 | h532
              · rcases m.htr 1 2 4 (by decide) (by decide) with h533 | h533
                · rcases m.htr 1 2 5 (by decide) (by decide) with h534 | h534
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h535 | h535
                    · linarith only [h0, h451, h535, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h537 | h537
                      · linarith only [h0, h451, h537, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h539 | h539
                        · linarith only [h451, h455, h479, h532, h535, h539, hc34, hlam, hphi, ht23, u2ehi2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h541 | h541
                          · linarith only [h0, h451, h532, h541, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h543 | h543
                            · linarith only [h451, h477, h532, h543, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h545 | h545
                              · linarith only [h453, h479, h545, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h547 | h547
                                · linarith only [h453, h479, h547, hc34, hlam, hphi, ht23, u2ehi3]
                                · linarith only [h451, h455, h532, h547, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h0, h451, h454, h532, h534, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h0, h451, h532, h533, hc24, hlam, hphi, u2ehi2]
              · linarith only [h0, h451, h532, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
      · linarith only [h452, h454, hc25, hlam, hphi, u2ehi2]
    · linarith only [h452, h453, hc24, hlam, hphi, u2ehi2]
  · linarith only [h0, h451, h452, hlam]

end R2N4
