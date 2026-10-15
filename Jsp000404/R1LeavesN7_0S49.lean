import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 17120000 in
set_option maxHeartbeats 17120000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h23337 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h29475 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h19744 := hg19744
  have h22010 := hg22010
  rcases m.htr 0 4 5 (by decide) (by decide) with h29476 | h29476
  · rcases m.htr 1 2 3 (by decide) (by decide) with h29477 | h29477
    · linarith only [h0, h29477, h4, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h29479 | h29479
      · linarith only [h0, h19744, h29479, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h29481 | h29481
        · linarith only [h0, h22010, h29481, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h29483 | h29483
          · linarith only [h1, h23337, h29475, h29483, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h29485 | h29485
            · rcases m.htr 1 4 5 (by decide) (by decide) with h29486 | h29486
              · rcases m.htr 2 3 4 (by decide) (by decide) with h29487 | h29487
                · rcases m.htr 2 3 5 (by decide) (by decide) with h29488 | h29488
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h29489 | h29489
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h29490 | h29490
                      · rcases h1bigk with h29491c | h29491c | h29491c | h29491c | h29491c | h29491c | h29491c | h29491c | h29491c | h29491c | h29491c | h29491c | h29491c | h29491c | h29491c | h29491c | h29491c | h29491c | h29491c | h29491c | h29491c | h29491c | h29491c | h29491c | h29491c
                        · have p29491_0 := h29491c.1
                          have p29491_1 := h29491c.2.1
                          have p29491_2 := h29491c.2.2.1
                          have p29491_3 := h29491c.2.2.2
                          linarith only [hlam, p29491_0]
                        · have p29491_0 := h29491c.1
                          have p29491_1 := h29491c.2.1
                          have p29491_2 := h29491c.2.2.1
                          have p29491_3 := h29491c.2.2.2
                          rcases p29491_3 (m.d 0 1) (by simp) with h29493 | h29493
                          · rcases p29491_3 (m.d 1 2) (by simp) with h29494 | h29494
                            · linarith only [h29494, hlam, p29491_0]
                            · rcases p29491_3 (m.d 1 3) (by simp) with h29496 | h29496
                              · linarith only [h1, h29496, hlam]
                              · linarith only [h29477, h29496, hlam]
                          · linarith only [h29493, hlam, p29491_0]
                        · have p29491_0 := h29491c.1
                          have p29491_1 := h29491c.2.1
                          have p29491_2 := h29491c.2.2.1
                          have p29491_3 := h29491c.2.2.2
                          rcases p29491_3 (m.d 0 1) (by simp) with h29500 | h29500
                          · rcases p29491_3 (m.d 1 2) (by simp) with h29501 | h29501
                            · linarith only [h0, h29501, hlam]
                            · rcases p29491_3 (m.d 1 3) (by simp) with h29503 | h29503
                              · linarith only [h29503, hlam, p29491_0]
                              · rcases p29491_3 (m.d 1 4) (by simp) with h29505 | h29505
                                · linarith only [h2, h29505, hlam]
                                · linarith only [h29483, h29505, hlam]
                          · linarith only [h29500, hlam, p29491_0]
                        · have p29491_0 := h29491c.1
                          have p29491_1 := h29491c.2.1
                          have p29491_2 := h29491c.2.2.1
                          have p29491_3 := h29491c.2.2.2
                          rcases p29491_3 (m.d 0 1) (by simp) with h29509 | h29509
                          · rcases p29491_3 (m.d 1 2) (by simp) with h29510 | h29510
                            · linarith only [h0, h29510, hlam]
                            · rcases p29491_3 (m.d 1 3) (by simp) with h29512 | h29512
                              · linarith only [h1, h29512, hlam]
                              · rcases p29491_3 (m.d 1 4) (by simp) with h29514 | h29514
                                · linarith only [h29514, hlam, p29491_0]
                                · rcases p29491_3 (m.d 1 5) (by simp) with h29516 | h29516
                                  · linarith only [h29516, h3, hlam]
                                  · rcases h1emax with h29518 | h29518 | h29518 | h29518 | h29518
                                    · linarith only [h1, h29485, h29490, h29518, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                    · rcases h2bigk with h29520c | h29520c | h29520c | h29520c | h29520c | h29520c | h29520c | h29520c | h29520c | h29520c | h29520c | h29520c | h29520c | h29520c | h29520c | h29520c | h29520c | h29520c | h29520c | h29520c | h29520c | h29520c | h29520c | h29520c | h29520c
                                      · have p29520_0 := h29520c.1
                                        have p29520_1 := h29520c.2.1
                                        have p29520_2 := h29520c.2.2.1
                                        have p29520_3 := h29520c.2.2.2
                                        linarith only [hlam, p29520_0]
                                      · have p29520_0 := h29520c.1
                                        have p29520_1 := h29520c.2.1
                                        have p29520_2 := h29520c.2.2.1
                                        have p29520_3 := h29520c.2.2.2
                                        linarith only [h22010, h23337, h29475, h29487, hc12, hc24, hlam, hphi, p29520_1]
                                      · have p29520_0 := h29520c.1
                                        have p29520_1 := h29520c.2.1
                                        have p29520_2 := h29520c.2.2.1
                                        have p29520_3 := h29520c.2.2.2
                                        linarith only [h4, hlam, p29520_0]
                                      · have p29520_0 := h29520c.1
                                        have p29520_1 := h29520c.2.1
                                        have p29520_2 := h29520c.2.2.1
                                        have p29520_3 := h29520c.2.2.2
                                        linarith only [h19744, hlam, p29520_0]
                                      · have p29520_0 := h29520c.1
                                        have p29520_1 := h29520c.2.1
                                        have p29520_2 := h29520c.2.2.1
                                        have p29520_3 := h29520c.2.2.2
                                        linarith only [h22010, hlam, p29520_0]
                                      · have p29520_0 := h29520c.1
                                        have p29520_1 := h29520c.2.1
                                        have p29520_2 := h29520c.2.2.1
                                        have p29520_3 := h29520c.2.2.2
                                        linarith only [h0, hlam, p29520_1]
                                      · have p29520_0 := h29520c.1
                                        have p29520_1 := h29520c.2.1
                                        have p29520_2 := h29520c.2.2.1
                                        have p29520_3 := h29520c.2.2.2
                                        linarith only [hlam, p29520_0]
                                      · have p29520_0 := h29520c.1
                                        have p29520_1 := h29520c.2.1
                                        have p29520_2 := h29520c.2.2.1
                                        have p29520_3 := h29520c.2.2.2
                                        linarith only [h29477, hlam, p29520_0]
                                      · have p29520_0 := h29520c.1
                                        have p29520_1 := h29520c.2.1
                                        have p29520_2 := h29520c.2.2.1
                                        have p29520_3 := h29520c.2.2.2
                                        linarith only [h29479, hlam, p29520_0]
                                      · have p29520_0 := h29520c.1
                                        have p29520_1 := h29520c.2.1
                                        have p29520_2 := h29520c.2.2.1
                                        have p29520_3 := h29520c.2.2.2
                                        linarith only [h29481, hlam, p29520_0]
                                      · have p29520_0 := h29520c.1
                                        have p29520_1 := h29520c.2.1
                                        have p29520_2 := h29520c.2.2.1
                                        have p29520_3 := h29520c.2.2.2
                                        rcases p29520_3 (m.d 0 2) (by simp) with h29531 | h29531
                                        · linarith only [h29531, hlam, p29520_0]
                                        · rcases p29520_3 (m.d 1 2) (by simp) with h29533 | h29533
                                          · linarith only [h29477, h29533, hlam]
                                          · rcases p29520_3 (m.d 2 3) (by simp) with h29535 | h29535
                                            · rcases p29520_3 (m.d 2 4) (by simp) with h29536 | h29536
                                              · linarith only [h29487, h29536, hlam]
                                              · linarith only [h19744, h29536, hlam]
                                            · linarith only [h29535, hlam, p29520_0]
                                      · have p29520_0 := h29520c.1
                                        have p29520_1 := h29520c.2.1
                                        have p29520_2 := h29520c.2.2.1
                                        have p29520_3 := h29520c.2.2.2
                                        rcases p29520_3 (m.d 0 2) (by simp) with h29540 | h29540
                                        · linarith only [h29540, h4, hlam]
                                        · linarith only [h0, h29540, hlam]
                                      · have p29520_0 := h29520c.1
                                        have p29520_1 := h29520c.2.1
                                        have p29520_2 := h29520c.2.2.1
                                        have p29520_3 := h29520c.2.2.2
                                        linarith only [hlam, p29520_0]
                                      · have p29520_0 := h29520c.1
                                        have p29520_1 := h29520c.2.1
                                        have p29520_2 := h29520c.2.2.1
                                        have p29520_3 := h29520c.2.2.2
                                        linarith only [h19744, hc02, hc23, hlam, hphi, p29520_1]
                                      · have p29520_0 := h29520c.1
                                        have p29520_1 := h29520c.2.1
                                        have p29520_2 := h29520c.2.2.1
                                        have p29520_3 := h29520c.2.2.2
                                        linarith only [h0, h22010, hc12, hc23, hlam, hphi, p29520_1]
                                      · have p29520_0 := h29520c.1
                                        have p29520_1 := h29520c.2.1
                                        have p29520_2 := h29520c.2.2.1
                                        have p29520_3 := h29520c.2.2.2
                                        rcases p29520_3 (m.d 0 2) (by simp) with h29546 | h29546
                                        · linarith only [h29546, hlam, p29520_0]
                                        · rcases p29520_3 (m.d 1 2) (by simp) with h29548 | h29548
                                          · linarith only [h29479, h29548, hlam]
                                          · rcases p29520_3 (m.d 2 3) (by simp) with h29550 | h29550
                                            · rcases p29520_3 (m.d 2 4) (by simp) with h29551 | h29551
                                              · rcases p29520_3 (m.d 2 5) (by simp) with h29552 | h29552
                                                · linarith only [h29489, h29552, hlam]
                                                · linarith only [h22010, h29552, hlam]
                                              · linarith only [h29551, hlam, p29520_0]
                                            · linarith only [h29550, h4, hlam]
                                      · have p29520_0 := h29520c.1
                                        have p29520_1 := h29520c.2.1
                                        have p29520_2 := h29520c.2.2.1
                                        have p29520_3 := h29520c.2.2.2
                                        rcases p29520_3 (m.d 0 2) (by simp) with h29557 | h29557
                                        · linarith only [h19744, h29557, hlam]
                                        · linarith only [h0, h29557, hlam]
                                      · have p29520_0 := h29520c.1
                                        have p29520_1 := h29520c.2.1
                                        have p29520_2 := h29520c.2.2.1
                                        have p29520_3 := h29520c.2.2.2
                                        linarith only [h29487, hlam, p29520_0]
                                      · have p29520_0 := h29520c.1
                                        have p29520_1 := h29520c.2.1
                                        have p29520_2 := h29520c.2.2.1
                                        have p29520_3 := h29520c.2.2.2
                                        linarith only [hlam, p29520_0]
                                      · have p29520_0 := h29520c.1
                                        have p29520_1 := h29520c.2.1
                                        have p29520_2 := h29520c.2.2.1
                                        have p29520_3 := h29520c.2.2.2
                                        linarith only [h0, h22010, hc12, hc24, hlam, hphi, p29520_1]
                                      · have p29520_0 := h29520c.1
                                        have p29520_1 := h29520c.2.1
                                        have p29520_2 := h29520c.2.2.1
                                        have p29520_3 := h29520c.2.2.2
                                        rcases p29520_3 (m.d 0 2) (by simp) with h29563 | h29563
                                        · linarith only [h29563, hlam, p29520_0]
                                        · rcases p29520_3 (m.d 1 2) (by simp) with h29565 | h29565
                                          · linarith only [h29481, h29565, hlam]
                                          · rcases p29520_3 (m.d 2 3) (by simp) with h29567 | h29567
                                            · rcases p29520_3 (m.d 2 4) (by simp) with h29568 | h29568
                                              · rcases p29520_3 (m.d 2 5) (by simp) with h29569 | h29569
                                                · rcases h4bigk with h29570c | h29570c | h29570c | h29570c | h29570c | h29570c | h29570c | h29570c | h29570c | h29570c | h29570c | h29570c | h29570c | h29570c | h29570c | h29570c | h29570c | h29570c | h29570c | h29570c | h29570c | h29570c | h29570c | h29570c | h29570c
                                                  · have p29570_0 := h29570c.1
                                                    have p29570_1 := h29570c.2.1
                                                    have p29570_2 := h29570c.2.2.1
                                                    have p29570_3 := h29570c.2.2.2
                                                    linarith only [hlam, p29570_0]
                                                  · have p29570_0 := h29570c.1
                                                    have p29570_1 := h29570c.2.1
                                                    have p29570_2 := h29570c.2.2.1
                                                    have p29570_3 := h29570c.2.2.2
                                                    linarith only [h23337, h29479, h29487, hc12, hc23, hlam, hphi, p29570_1]
                                                  · have p29570_0 := h29570c.1
                                                    have p29570_1 := h29570c.2.1
                                                    have p29570_2 := h29570c.2.2.1
                                                    have p29570_3 := h29570c.2.2.2
                                                    linarith only [h19744, hlam, p29570_1]
                                                  · have p29570_0 := h29570c.1
                                                    have p29570_1 := h29570c.2.1
                                                    have p29570_2 := h29570c.2.2.1
                                                    have p29570_3 := h29570c.2.2.2
                                                    linarith only [h23337, hlam, p29570_1]
                                                  · have p29570_0 := h29570c.1
                                                    have p29570_1 := h29570c.2.1
                                                    have p29570_2 := h29570c.2.2.1
                                                    have p29570_3 := h29570c.2.2.2
                                                    rcases p29570_3 (m.d 0 4) (by simp) with h29575 | h29575
                                                    · rcases p29570_3 (m.d 1 4) (by simp) with h29576 | h29576
                                                      · linarith only [h2, h29576, hlam]
                                                      · linarith only [h29486, h29576, hlam]
                                                    · linarith only [h29575, hlam, p29570_0]
                                                  · have p29570_0 := h29570c.1
                                                    have p29570_1 := h29570c.2.1
                                                    have p29570_2 := h29570c.2.2.1
                                                    have p29570_3 := h29570c.2.2.2
                                                    linarith only [h2, hlam, p29570_0]
                                                  · have p29570_0 := h29570c.1
                                                    have p29570_1 := h29570c.2.1
                                                    have p29570_2 := h29570c.2.2.1
                                                    have p29570_3 := h29570c.2.2.2
                                                    linarith only [hlam, p29570_0]
                                                  · have p29570_0 := h29570c.1
                                                    have p29570_1 := h29570c.2.1
                                                    have p29570_2 := h29570c.2.2.1
                                                    have p29570_3 := h29570c.2.2.2
                                                    linarith only [h29479, hlam, p29570_1]
                                                  · have p29570_0 := h29570c.1
                                                    have p29570_1 := h29570c.2.1
                                                    have p29570_2 := h29570c.2.2.1
                                                    have p29570_3 := h29570c.2.2.2
                                                    linarith only [h29483, hlam, p29570_1]
                                                  · have p29570_0 := h29570c.1
                                                    have p29570_1 := h29570c.2.1
                                                    have p29570_2 := h29570c.2.2.1
                                                    have p29570_3 := h29570c.2.2.2
                                                    linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p29491_1, p29570_1]
                                                  · have p29570_0 := h29570c.1
                                                    have p29570_1 := h29570c.2.1
                                                    have p29570_2 := h29570c.2.2.1
                                                    have p29570_3 := h29570c.2.2.2
                                                    rcases p29570_3 (m.d 0 4) (by simp) with h29585 | h29585
                                                    · linarith only [h19744, h29585, hlam]
                                                    · rcases p29570_3 (m.d 1 4) (by simp) with h29587 | h29587
                                                      · linarith only [h29479, h29587, hlam]
                                                      · rcases p29570_3 (m.d 2 4) (by simp) with h29589 | h29589
                                                        · rcases p29570_3 (m.d 3 4) (by simp) with h29590 | h29590
                                                          · linarith only [h29487, h29590, hlam]
                                                          · linarith only [h23337, h29590, hlam]
                                                        · linarith only [h19744, h29589, hlam]
                                                  · have p29570_0 := h29570c.1
                                                    have p29570_1 := h29570c.2.1
                                                    have p29570_2 := h29570c.2.2.1
                                                    have p29570_3 := h29570c.2.2.2
                                                    rcases p29570_3 (m.d 0 4) (by simp) with h29594 | h29594
                                                    · linarith only [h19744, h29594, hlam]
                                                    · linarith only [h2, h29594, hlam]
                                                  · have p29570_0 := h29570c.1
                                                    have p29570_1 := h29570c.2.1
                                                    have p29570_2 := h29570c.2.2.1
                                                    have p29570_3 := h29570c.2.2.2
                                                    linarith only [hlam, p29570_0]
                                                  · have p29570_0 := h29570c.1
                                                    have p29570_1 := h29570c.2.1
                                                    have p29570_2 := h29570c.2.2.1
                                                    have p29570_3 := h29570c.2.2.2
                                                    linarith only [h1, h23337, h29485, h29487, h29490, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p29570_1]
                                                  · have p29570_0 := h29570c.1
                                                    have p29570_1 := h29570c.2.1
                                                    have p29570_2 := h29570c.2.2.1
                                                    have p29570_3 := h29570c.2.2.2
                                                    rcases p29570_3 (m.d 0 4) (by simp) with h29599 | h29599
                                                    · linarith only [h19744, h29599, hlam]
                                                    · linarith only [h29476, h29599, hlam]
                                                  · have p29570_0 := h29570c.1
                                                    have p29570_1 := h29570c.2.1
                                                    have p29570_2 := h29570c.2.2.1
                                                    have p29570_3 := h29570c.2.2.2
                                                    linarith only [h1, h23337, h29485, h29487, h29490, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p29570_1]
                                                  · have p29570_0 := h29570c.1
                                                    have p29570_1 := h29570c.2.1
                                                    have p29570_2 := h29570c.2.2.1
                                                    have p29570_3 := h29570c.2.2.2
                                                    linarith only [h29479, h29487, hc12, hc23, hlam, hphi, p29570_1]
                                                  · have p29570_0 := h29570c.1
                                                    have p29570_1 := h29570c.2.1
                                                    have p29570_2 := h29570c.2.2.1
                                                    have p29570_3 := h29570c.2.2.2
                                                    linarith only [h29487, hlam, p29570_0]
                                                  · have p29570_0 := h29570c.1
                                                    have p29570_1 := h29570c.2.1
                                                    have p29570_2 := h29570c.2.2.1
                                                    have p29570_3 := h29570c.2.2.2
                                                    linarith only [hlam, p29570_0]
                                                  · have p29570_0 := h29570c.1
                                                    have p29570_1 := h29570c.2.1
                                                    have p29570_2 := h29570c.2.2.1
                                                    have p29570_3 := h29570c.2.2.2
                                                    rcases p29570_3 (m.d 0 4) (by simp) with h29606 | h29606
                                                    · linarith only [h23337, h29606, hlam]
                                                    · linarith only [h29476, h29606, hlam]
                                                  · have p29570_0 := h29570c.1
                                                    have p29570_1 := h29570c.2.1
                                                    have p29570_2 := h29570c.2.2.1
                                                    have p29570_3 := h29570c.2.2.2
                                                    linarith only [h29476, hlam, p29570_0]
                                                  · have p29570_0 := h29570c.1
                                                    have p29570_1 := h29570c.2.1
                                                    have p29570_2 := h29570c.2.2.1
                                                    have p29570_3 := h29570c.2.2.2
                                                    linarith only [h29486, hlam, p29570_0]
                                                  · have p29570_0 := h29570c.1
                                                    have p29570_1 := h29570c.2.1
                                                    have p29570_2 := h29570c.2.2.1
                                                    have p29570_3 := h29570c.2.2.2
                                                    linarith only [h29489, hlam, p29570_0]
                                                  · have p29570_0 := h29570c.1
                                                    have p29570_1 := h29570c.2.1
                                                    have p29570_2 := h29570c.2.2.1
                                                    have p29570_3 := h29570c.2.2.2
                                                    linarith only [h29490, hlam, p29570_0]
                                                  · have p29570_0 := h29570c.1
                                                    have p29570_1 := h29570c.2.1
                                                    have p29570_2 := h29570c.2.2.1
                                                    have p29570_3 := h29570c.2.2.2
                                                    linarith only [hlam, p29570_0]
                                                · linarith only [h29569, hlam, p29520_0]
                                              · linarith only [h19744, h29568, hlam]
                                            · linarith only [h29567, h4, hlam]
                                      · have p29520_0 := h29520c.1
                                        have p29520_1 := h29520c.2.1
                                        have p29520_2 := h29520c.2.2.1
                                        have p29520_3 := h29520c.2.2.2
                                        rcases p29520_3 (m.d 0 2) (by simp) with h29617 | h29617
                                        · linarith only [h22010, h29617, hlam]
                                        · linarith only [h0, h29617, hlam]
                                      · have p29520_0 := h29520c.1
                                        have p29520_1 := h29520c.2.1
                                        have p29520_2 := h29520c.2.2.1
                                        have p29520_3 := h29520c.2.2.2
                                        linarith only [h29488, hlam, p29520_0]
                                      · have p29520_0 := h29520c.1
                                        have p29520_1 := h29520c.2.1
                                        have p29520_2 := h29520c.2.2.1
                                        have p29520_3 := h29520c.2.2.2
                                        linarith only [h29489, hlam, p29520_1]
                                      · have p29520_0 := h29520c.1
                                        have p29520_1 := h29520c.2.1
                                        have p29520_2 := h29520c.2.2.1
                                        have p29520_3 := h29520c.2.2.2
                                        linarith only [hlam, p29520_0]
                                    · rcases h2bigk with h29623c | h29623c | h29623c | h29623c | h29623c | h29623c | h29623c | h29623c | h29623c | h29623c | h29623c | h29623c | h29623c | h29623c | h29623c | h29623c | h29623c | h29623c | h29623c | h29623c | h29623c | h29623c | h29623c | h29623c | h29623c
                                      · have p29623_0 := h29623c.1
                                        have p29623_1 := h29623c.2.1
                                        have p29623_2 := h29623c.2.2.1
                                        have p29623_3 := h29623c.2.2.2
                                        linarith only [hlam, p29623_0]
                                      · have p29623_0 := h29623c.1
                                        have p29623_1 := h29623c.2.1
                                        have p29623_2 := h29623c.2.2.1
                                        have p29623_3 := h29623c.2.2.2
                                        linarith only [h4, hc12, hc23, hlam, hphi, p29623_1]
                                      · have p29623_0 := h29623c.1
                                        have p29623_1 := h29623c.2.1
                                        have p29623_2 := h29623c.2.2.1
                                        have p29623_3 := h29623c.2.2.2
                                        linarith only [h4, hlam, p29623_0]
                                      · have p29623_0 := h29623c.1
                                        have p29623_1 := h29623c.2.1
                                        have p29623_2 := h29623c.2.2.1
                                        have p29623_3 := h29623c.2.2.2
                                        linarith only [h19744, hlam, p29623_0]
                                      · have p29623_0 := h29623c.1
                                        have p29623_1 := h29623c.2.1
                                        have p29623_2 := h29623c.2.2.1
                                        have p29623_3 := h29623c.2.2.2
                                        linarith only [h22010, hlam, p29623_0]
                                      · have p29623_0 := h29623c.1
                                        have p29623_1 := h29623c.2.1
                                        have p29623_2 := h29623c.2.2.1
                                        have p29623_3 := h29623c.2.2.2
                                        linarith only [h0, hlam, p29623_1]
                                      · have p29623_0 := h29623c.1
                                        have p29623_1 := h29623c.2.1
                                        have p29623_2 := h29623c.2.2.1
                                        have p29623_3 := h29623c.2.2.2
                                        linarith only [hlam, p29623_0]
                                      · have p29623_0 := h29623c.1
                                        have p29623_1 := h29623c.2.1
                                        have p29623_2 := h29623c.2.2.1
                                        have p29623_3 := h29623c.2.2.2
                                        linarith only [h29477, hlam, p29623_0]
                                      · have p29623_0 := h29623c.1
                                        have p29623_1 := h29623c.2.1
                                        have p29623_2 := h29623c.2.2.1
                                        have p29623_3 := h29623c.2.2.2
                                        linarith only [h29479, hlam, p29623_0]
                                      · have p29623_0 := h29623c.1
                                        have p29623_1 := h29623c.2.1
                                        have p29623_2 := h29623c.2.2.1
                                        have p29623_3 := h29623c.2.2.2
                                        linarith only [h29481, hlam, p29623_0]
                                      · have p29623_0 := h29623c.1
                                        have p29623_1 := h29623c.2.1
                                        have p29623_2 := h29623c.2.2.1
                                        have p29623_3 := h29623c.2.2.2
                                        rcases p29623_3 (m.d 0 2) (by simp) with h29634 | h29634
                                        · linarith only [h29634, hlam, p29623_0]
                                        · rcases p29623_3 (m.d 1 2) (by simp) with h29636 | h29636
                                          · linarith only [h29477, h29636, hlam]
                                          · rcases p29623_3 (m.d 2 3) (by simp) with h29638 | h29638
                                            · rcases p29623_3 (m.d 2 4) (by simp) with h29639 | h29639
                                              · linarith only [h29487, h29639, hlam]
                                              · linarith only [h19744, h29639, hlam]
                                            · linarith only [h29638, hlam, p29623_0]
                                      · have p29623_0 := h29623c.1
                                        have p29623_1 := h29623c.2.1
                                        have p29623_2 := h29623c.2.2.1
                                        have p29623_3 := h29623c.2.2.2
                                        rcases p29623_3 (m.d 0 2) (by simp) with h29643 | h29643
                                        · linarith only [h29643, h4, hlam]
                                        · linarith only [h0, h29643, hlam]
                                      · have p29623_0 := h29623c.1
                                        have p29623_1 := h29623c.2.1
                                        have p29623_2 := h29623c.2.2.1
                                        have p29623_3 := h29623c.2.2.2
                                        linarith only [hlam, p29623_0]
                                      · have p29623_0 := h29623c.1
                                        have p29623_1 := h29623c.2.1
                                        have p29623_2 := h29623c.2.2.1
                                        have p29623_3 := h29623c.2.2.2
                                        linarith only [h19744, hc02, hc23, hlam, hphi, p29623_1]
                                      · have p29623_0 := h29623c.1
                                        have p29623_1 := h29623c.2.1
                                        have p29623_2 := h29623c.2.2.1
                                        have p29623_3 := h29623c.2.2.2
                                        linarith only [h0, h22010, hc12, hc23, hlam, hphi, p29623_1]
                                      · have p29623_0 := h29623c.1
                                        have p29623_1 := h29623c.2.1
                                        have p29623_2 := h29623c.2.2.1
                                        have p29623_3 := h29623c.2.2.2
                                        rcases p29623_3 (m.d 0 2) (by simp) with h29649 | h29649
                                        · linarith only [h29649, hlam, p29623_0]
                                        · rcases p29623_3 (m.d 1 2) (by simp) with h29651 | h29651
                                          · linarith only [h29479, h29651, hlam]
                                          · rcases p29623_3 (m.d 2 3) (by simp) with h29653 | h29653
                                            · rcases p29623_3 (m.d 2 4) (by simp) with h29654 | h29654
                                              · rcases p29623_3 (m.d 2 5) (by simp) with h29655 | h29655
                                                · linarith only [h29489, h29655, hlam]
                                                · linarith only [h22010, h29655, hlam]
                                              · linarith only [h29654, hlam, p29623_0]
                                            · linarith only [h29653, h4, hlam]
                                      · have p29623_0 := h29623c.1
                                        have p29623_1 := h29623c.2.1
                                        have p29623_2 := h29623c.2.2.1
                                        have p29623_3 := h29623c.2.2.2
                                        rcases p29623_3 (m.d 0 2) (by simp) with h29660 | h29660
                                        · linarith only [h19744, h29660, hlam]
                                        · linarith only [h0, h29660, hlam]
                                      · have p29623_0 := h29623c.1
                                        have p29623_1 := h29623c.2.1
                                        have p29623_2 := h29623c.2.2.1
                                        have p29623_3 := h29623c.2.2.2
                                        linarith only [h29487, hlam, p29623_0]
                                      · have p29623_0 := h29623c.1
                                        have p29623_1 := h29623c.2.1
                                        have p29623_2 := h29623c.2.2.1
                                        have p29623_3 := h29623c.2.2.2
                                        linarith only [hlam, p29623_0]
                                      · have p29623_0 := h29623c.1
                                        have p29623_1 := h29623c.2.1
                                        have p29623_2 := h29623c.2.2.1
                                        have p29623_3 := h29623c.2.2.2
                                        linarith only [h0, h22010, hc12, hc24, hlam, hphi, p29623_1]
                                      · have p29623_0 := h29623c.1
                                        have p29623_1 := h29623c.2.1
                                        have p29623_2 := h29623c.2.2.1
                                        have p29623_3 := h29623c.2.2.2
                                        rcases p29623_3 (m.d 0 2) (by simp) with h29666 | h29666
                                        · linarith only [h29666, hlam, p29623_0]
                                        · rcases p29623_3 (m.d 1 2) (by simp) with h29668 | h29668
                                          · linarith only [h29481, h29668, hlam]
                                          · rcases p29623_3 (m.d 2 3) (by simp) with h29670 | h29670
                                            · rcases p29623_3 (m.d 2 4) (by simp) with h29671 | h29671
                                              · rcases p29623_3 (m.d 2 5) (by simp) with h29672 | h29672
                                                · rcases h4bigk with h29673c | h29673c | h29673c | h29673c | h29673c | h29673c | h29673c | h29673c | h29673c | h29673c | h29673c | h29673c | h29673c | h29673c | h29673c | h29673c | h29673c | h29673c | h29673c | h29673c | h29673c | h29673c | h29673c | h29673c | h29673c
                                                  · have p29673_0 := h29673c.1
                                                    have p29673_1 := h29673c.2.1
                                                    have p29673_2 := h29673c.2.2.1
                                                    have p29673_3 := h29673c.2.2.2
                                                    linarith only [hlam, p29673_0]
                                                  · have p29673_0 := h29673c.1
                                                    have p29673_1 := h29673c.2.1
                                                    have p29673_2 := h29673c.2.2.1
                                                    have p29673_3 := h29673c.2.2.2
                                                    linarith only [h23337, h29483, h29485, h29487, h29490, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p29673_1]
                                                  · have p29673_0 := h29673c.1
                                                    have p29673_1 := h29673c.2.1
                                                    have p29673_2 := h29673c.2.2.1
                                                    have p29673_3 := h29673c.2.2.2
                                                    linarith only [h19744, hlam, p29673_1]
                                                  · have p29673_0 := h29673c.1
                                                    have p29673_1 := h29673c.2.1
                                                    have p29673_2 := h29673c.2.2.1
                                                    have p29673_3 := h29673c.2.2.2
                                                    linarith only [h23337, hlam, p29673_1]
                                                  · have p29673_0 := h29673c.1
                                                    have p29673_1 := h29673c.2.1
                                                    have p29673_2 := h29673c.2.2.1
                                                    have p29673_3 := h29673c.2.2.2
                                                    rcases p29673_3 (m.d 0 4) (by simp) with h29678 | h29678
                                                    · rcases p29673_3 (m.d 1 4) (by simp) with h29679 | h29679
                                                      · linarith only [h2, h29679, hlam]
                                                      · linarith only [h29486, h29679, hlam]
                                                    · linarith only [h29678, hlam, p29673_0]
                                                  · have p29673_0 := h29673c.1
                                                    have p29673_1 := h29673c.2.1
                                                    have p29673_2 := h29673c.2.2.1
                                                    have p29673_3 := h29673c.2.2.2
                                                    linarith only [h2, hlam, p29673_0]
                                                  · have p29673_0 := h29673c.1
                                                    have p29673_1 := h29673c.2.1
                                                    have p29673_2 := h29673c.2.2.1
                                                    have p29673_3 := h29673c.2.2.2
                                                    linarith only [hlam, p29673_0]
                                                  · have p29673_0 := h29673c.1
                                                    have p29673_1 := h29673c.2.1
                                                    have p29673_2 := h29673c.2.2.1
                                                    have p29673_3 := h29673c.2.2.2
                                                    linarith only [h29479, hlam, p29673_1]
                                                  · have p29673_0 := h29673c.1
                                                    have p29673_1 := h29673c.2.1
                                                    have p29673_2 := h29673c.2.2.1
                                                    have p29673_3 := h29673c.2.2.2
                                                    linarith only [h29483, hlam, p29673_1]
                                                  · have p29673_0 := h29673c.1
                                                    have p29673_1 := h29673c.2.1
                                                    have p29673_2 := h29673c.2.2.1
                                                    have p29673_3 := h29673c.2.2.2
                                                    linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p29491_1, p29673_1]
                                                  · have p29673_0 := h29673c.1
                                                    have p29673_1 := h29673c.2.1
                                                    have p29673_2 := h29673c.2.2.1
                                                    have p29673_3 := h29673c.2.2.2
                                                    rcases p29673_3 (m.d 0 4) (by simp) with h29688 | h29688
                                                    · linarith only [h19744, h29688, hlam]
                                                    · rcases p29673_3 (m.d 1 4) (by simp) with h29690 | h29690
                                                      · linarith only [h29479, h29690, hlam]
                                                      · rcases p29673_3 (m.d 2 4) (by simp) with h29692 | h29692
                                                        · rcases p29673_3 (m.d 3 4) (by simp) with h29693 | h29693
                                                          · linarith only [h29487, h29693, hlam]
                                                          · linarith only [h23337, h29693, hlam]
                                                        · linarith only [h19744, h29692, hlam]
                                                  · have p29673_0 := h29673c.1
                                                    have p29673_1 := h29673c.2.1
                                                    have p29673_2 := h29673c.2.2.1
                                                    have p29673_3 := h29673c.2.2.2
                                                    rcases p29673_3 (m.d 0 4) (by simp) with h29697 | h29697
                                                    · linarith only [h19744, h29697, hlam]
                                                    · linarith only [h2, h29697, hlam]
                                                  · have p29673_0 := h29673c.1
                                                    have p29673_1 := h29673c.2.1
                                                    have p29673_2 := h29673c.2.2.1
                                                    have p29673_3 := h29673c.2.2.2
                                                    linarith only [hlam, p29673_0]
                                                  · have p29673_0 := h29673c.1
                                                    have p29673_1 := h29673c.2.1
                                                    have p29673_2 := h29673c.2.2.1
                                                    have p29673_3 := h29673c.2.2.2
                                                    linarith only [h1, h23337, h29485, h29487, h29490, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p29673_1]
                                                  · have p29673_0 := h29673c.1
                                                    have p29673_1 := h29673c.2.1
                                                    have p29673_2 := h29673c.2.2.1
                                                    have p29673_3 := h29673c.2.2.2
                                                    rcases p29673_3 (m.d 0 4) (by simp) with h29702 | h29702
                                                    · linarith only [h19744, h29702, hlam]
                                                    · linarith only [h29476, h29702, hlam]
                                                  · have p29673_0 := h29673c.1
                                                    have p29673_1 := h29673c.2.1
                                                    have p29673_2 := h29673c.2.2.1
                                                    have p29673_3 := h29673c.2.2.2
                                                    linarith only [h1, h23337, h29485, h29487, h29490, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p29673_1]
                                                  · have p29673_0 := h29673c.1
                                                    have p29673_1 := h29673c.2.1
                                                    have p29673_2 := h29673c.2.2.1
                                                    have p29673_3 := h29673c.2.2.2
                                                    linarith only [h29479, h29487, hc12, hc23, hlam, hphi, p29673_1]
                                                  · have p29673_0 := h29673c.1
                                                    have p29673_1 := h29673c.2.1
                                                    have p29673_2 := h29673c.2.2.1
                                                    have p29673_3 := h29673c.2.2.2
                                                    linarith only [h29487, hlam, p29673_0]
                                                  · have p29673_0 := h29673c.1
                                                    have p29673_1 := h29673c.2.1
                                                    have p29673_2 := h29673c.2.2.1
                                                    have p29673_3 := h29673c.2.2.2
                                                    linarith only [hlam, p29673_0]
                                                  · have p29673_0 := h29673c.1
                                                    have p29673_1 := h29673c.2.1
                                                    have p29673_2 := h29673c.2.2.1
                                                    have p29673_3 := h29673c.2.2.2
                                                    rcases p29673_3 (m.d 0 4) (by simp) with h29709 | h29709
                                                    · linarith only [h23337, h29709, hlam]
                                                    · linarith only [h29476, h29709, hlam]
                                                  · have p29673_0 := h29673c.1
                                                    have p29673_1 := h29673c.2.1
                                                    have p29673_2 := h29673c.2.2.1
                                                    have p29673_3 := h29673c.2.2.2
                                                    linarith only [h29476, hlam, p29673_0]
                                                  · have p29673_0 := h29673c.1
                                                    have p29673_1 := h29673c.2.1
                                                    have p29673_2 := h29673c.2.2.1
                                                    have p29673_3 := h29673c.2.2.2
                                                    linarith only [h29486, hlam, p29673_0]
                                                  · have p29673_0 := h29673c.1
                                                    have p29673_1 := h29673c.2.1
                                                    have p29673_2 := h29673c.2.2.1
                                                    have p29673_3 := h29673c.2.2.2
                                                    linarith only [h29489, hlam, p29673_0]
                                                  · have p29673_0 := h29673c.1
                                                    have p29673_1 := h29673c.2.1
                                                    have p29673_2 := h29673c.2.2.1
                                                    have p29673_3 := h29673c.2.2.2
                                                    linarith only [h29490, hlam, p29673_0]
                                                  · have p29673_0 := h29673c.1
                                                    have p29673_1 := h29673c.2.1
                                                    have p29673_2 := h29673c.2.2.1
                                                    have p29673_3 := h29673c.2.2.2
                                                    linarith only [hlam, p29673_0]
                                                · linarith only [h29672, hlam, p29623_0]
                                              · linarith only [h19744, h29671, hlam]
                                            · linarith only [h29670, h4, hlam]
                                      · have p29623_0 := h29623c.1
                                        have p29623_1 := h29623c.2.1
                                        have p29623_2 := h29623c.2.2.1
                                        have p29623_3 := h29623c.2.2.2
                                        rcases p29623_3 (m.d 0 2) (by simp) with h29720 | h29720
                                        · linarith only [h22010, h29720, hlam]
                                        · linarith only [h0, h29720, hlam]
                                      · have p29623_0 := h29623c.1
                                        have p29623_1 := h29623c.2.1
                                        have p29623_2 := h29623c.2.2.1
                                        have p29623_3 := h29623c.2.2.2
                                        linarith only [h29488, hlam, p29623_0]
                                      · have p29623_0 := h29623c.1
                                        have p29623_1 := h29623c.2.1
                                        have p29623_2 := h29623c.2.2.1
                                        have p29623_3 := h29623c.2.2.2
                                        linarith only [h29489, hlam, p29623_1]
                                      · have p29623_0 := h29623c.1
                                        have p29623_1 := h29623c.2.1
                                        have p29623_2 := h29623c.2.2.1
                                        have p29623_3 := h29623c.2.2.2
                                        linarith only [hlam, p29623_0]
                                    · rcases h2bigk with h29726c | h29726c | h29726c | h29726c | h29726c | h29726c | h29726c | h29726c | h29726c | h29726c | h29726c | h29726c | h29726c | h29726c | h29726c | h29726c | h29726c | h29726c | h29726c | h29726c | h29726c | h29726c | h29726c | h29726c | h29726c
                                      · have p29726_0 := h29726c.1
                                        have p29726_1 := h29726c.2.1
                                        have p29726_2 := h29726c.2.2.1
                                        have p29726_3 := h29726c.2.2.2
                                        linarith only [hlam, p29726_0]
                                      · have p29726_0 := h29726c.1
                                        have p29726_1 := h29726c.2.1
                                        have p29726_2 := h29726c.2.2.1
                                        have p29726_3 := h29726c.2.2.2
                                        linarith only [h4, hc12, hc23, hlam, hphi, p29726_1]
                                      · have p29726_0 := h29726c.1
                                        have p29726_1 := h29726c.2.1
                                        have p29726_2 := h29726c.2.2.1
                                        have p29726_3 := h29726c.2.2.2
                                        linarith only [h4, hlam, p29726_0]
                                      · have p29726_0 := h29726c.1
                                        have p29726_1 := h29726c.2.1
                                        have p29726_2 := h29726c.2.2.1
                                        have p29726_3 := h29726c.2.2.2
                                        linarith only [h19744, hlam, p29726_0]
                                      · have p29726_0 := h29726c.1
                                        have p29726_1 := h29726c.2.1
                                        have p29726_2 := h29726c.2.2.1
                                        have p29726_3 := h29726c.2.2.2
                                        linarith only [h22010, hlam, p29726_0]
                                      · have p29726_0 := h29726c.1
                                        have p29726_1 := h29726c.2.1
                                        have p29726_2 := h29726c.2.2.1
                                        have p29726_3 := h29726c.2.2.2
                                        linarith only [h0, hlam, p29726_1]
                                      · have p29726_0 := h29726c.1
                                        have p29726_1 := h29726c.2.1
                                        have p29726_2 := h29726c.2.2.1
                                        have p29726_3 := h29726c.2.2.2
                                        linarith only [hlam, p29726_0]
                                      · have p29726_0 := h29726c.1
                                        have p29726_1 := h29726c.2.1
                                        have p29726_2 := h29726c.2.2.1
                                        have p29726_3 := h29726c.2.2.2
                                        linarith only [h29477, hlam, p29726_0]
                                      · have p29726_0 := h29726c.1
                                        have p29726_1 := h29726c.2.1
                                        have p29726_2 := h29726c.2.2.1
                                        have p29726_3 := h29726c.2.2.2
                                        linarith only [h29479, hlam, p29726_0]
                                      · have p29726_0 := h29726c.1
                                        have p29726_1 := h29726c.2.1
                                        have p29726_2 := h29726c.2.2.1
                                        have p29726_3 := h29726c.2.2.2
                                        linarith only [h29481, hlam, p29726_0]
                                      · have p29726_0 := h29726c.1
                                        have p29726_1 := h29726c.2.1
                                        have p29726_2 := h29726c.2.2.1
                                        have p29726_3 := h29726c.2.2.2
                                        rcases p29726_3 (m.d 0 2) (by simp) with h29737 | h29737
                                        · linarith only [h29737, hlam, p29726_0]
                                        · rcases p29726_3 (m.d 1 2) (by simp) with h29739 | h29739
                                          · linarith only [h29477, h29739, hlam]
                                          · rcases p29726_3 (m.d 2 3) (by simp) with h29741 | h29741
                                            · rcases p29726_3 (m.d 2 4) (by simp) with h29742 | h29742
                                              · linarith only [h29487, h29742, hlam]
                                              · linarith only [h19744, h29742, hlam]
                                            · linarith only [h29741, hlam, p29726_0]
                                      · have p29726_0 := h29726c.1
                                        have p29726_1 := h29726c.2.1
                                        have p29726_2 := h29726c.2.2.1
                                        have p29726_3 := h29726c.2.2.2
                                        rcases p29726_3 (m.d 0 2) (by simp) with h29746 | h29746
                                        · linarith only [h29746, h4, hlam]
                                        · linarith only [h0, h29746, hlam]
                                      · have p29726_0 := h29726c.1
                                        have p29726_1 := h29726c.2.1
                                        have p29726_2 := h29726c.2.2.1
                                        have p29726_3 := h29726c.2.2.2
                                        linarith only [hlam, p29726_0]
                                      · have p29726_0 := h29726c.1
                                        have p29726_1 := h29726c.2.1
                                        have p29726_2 := h29726c.2.2.1
                                        have p29726_3 := h29726c.2.2.2
                                        linarith only [h19744, hc02, hc23, hlam, hphi, p29726_1]
                                      · have p29726_0 := h29726c.1
                                        have p29726_1 := h29726c.2.1
                                        have p29726_2 := h29726c.2.2.1
                                        have p29726_3 := h29726c.2.2.2
                                        linarith only [h0, h22010, hc12, hc23, hlam, hphi, p29726_1]
                                      · have p29726_0 := h29726c.1
                                        have p29726_1 := h29726c.2.1
                                        have p29726_2 := h29726c.2.2.1
                                        have p29726_3 := h29726c.2.2.2
                                        rcases p29726_3 (m.d 0 2) (by simp) with h29752 | h29752
                                        · linarith only [h29752, hlam, p29726_0]
                                        · rcases p29726_3 (m.d 1 2) (by simp) with h29754 | h29754
                                          · linarith only [h29479, h29754, hlam]
                                          · rcases p29726_3 (m.d 2 3) (by simp) with h29756 | h29756
                                            · rcases p29726_3 (m.d 2 4) (by simp) with h29757 | h29757
                                              · rcases p29726_3 (m.d 2 5) (by simp) with h29758 | h29758
                                                · linarith only [h29489, h29758, hlam]
                                                · linarith only [h22010, h29758, hlam]
                                              · linarith only [h29757, hlam, p29726_0]
                                            · linarith only [h29756, h4, hlam]
                                      · have p29726_0 := h29726c.1
                                        have p29726_1 := h29726c.2.1
                                        have p29726_2 := h29726c.2.2.1
                                        have p29726_3 := h29726c.2.2.2
                                        rcases p29726_3 (m.d 0 2) (by simp) with h29763 | h29763
                                        · linarith only [h19744, h29763, hlam]
                                        · linarith only [h0, h29763, hlam]
                                      · have p29726_0 := h29726c.1
                                        have p29726_1 := h29726c.2.1
                                        have p29726_2 := h29726c.2.2.1
                                        have p29726_3 := h29726c.2.2.2
                                        linarith only [h29487, hlam, p29726_0]
                                      · have p29726_0 := h29726c.1
                                        have p29726_1 := h29726c.2.1
                                        have p29726_2 := h29726c.2.2.1
                                        have p29726_3 := h29726c.2.2.2
                                        linarith only [hlam, p29726_0]
                                      · have p29726_0 := h29726c.1
                                        have p29726_1 := h29726c.2.1
                                        have p29726_2 := h29726c.2.2.1
                                        have p29726_3 := h29726c.2.2.2
                                        linarith only [h0, h22010, hc12, hc24, hlam, hphi, p29726_1]
                                      · have p29726_0 := h29726c.1
                                        have p29726_1 := h29726c.2.1
                                        have p29726_2 := h29726c.2.2.1
                                        have p29726_3 := h29726c.2.2.2
                                        rcases p29726_3 (m.d 0 2) (by simp) with h29769 | h29769
                                        · linarith only [h29769, hlam, p29726_0]
                                        · rcases p29726_3 (m.d 1 2) (by simp) with h29771 | h29771
                                          · linarith only [h29481, h29771, hlam]
                                          · rcases p29726_3 (m.d 2 3) (by simp) with h29773 | h29773
                                            · rcases p29726_3 (m.d 2 4) (by simp) with h29774 | h29774
                                              · rcases p29726_3 (m.d 2 5) (by simp) with h29775 | h29775
                                                · rcases h4bigk with h29776c | h29776c | h29776c | h29776c | h29776c | h29776c | h29776c | h29776c | h29776c | h29776c | h29776c | h29776c | h29776c | h29776c | h29776c | h29776c | h29776c | h29776c | h29776c | h29776c | h29776c | h29776c | h29776c | h29776c | h29776c
                                                  · have p29776_0 := h29776c.1
                                                    have p29776_1 := h29776c.2.1
                                                    have p29776_2 := h29776c.2.2.1
                                                    have p29776_3 := h29776c.2.2.2
                                                    linarith only [hlam, p29776_0]
                                                  · have p29776_0 := h29776c.1
                                                    have p29776_1 := h29776c.2.1
                                                    have p29776_2 := h29776c.2.2.1
                                                    have p29776_3 := h29776c.2.2.2
                                                    linarith only [h23337, h29483, h29485, h29487, h29490, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p29776_1]
                                                  · have p29776_0 := h29776c.1
                                                    have p29776_1 := h29776c.2.1
                                                    have p29776_2 := h29776c.2.2.1
                                                    have p29776_3 := h29776c.2.2.2
                                                    linarith only [h19744, hlam, p29776_1]
                                                  · have p29776_0 := h29776c.1
                                                    have p29776_1 := h29776c.2.1
                                                    have p29776_2 := h29776c.2.2.1
                                                    have p29776_3 := h29776c.2.2.2
                                                    linarith only [h23337, hlam, p29776_1]
                                                  · have p29776_0 := h29776c.1
                                                    have p29776_1 := h29776c.2.1
                                                    have p29776_2 := h29776c.2.2.1
                                                    have p29776_3 := h29776c.2.2.2
                                                    rcases p29776_3 (m.d 0 4) (by simp) with h29781 | h29781
                                                    · rcases p29776_3 (m.d 1 4) (by simp) with h29782 | h29782
                                                      · linarith only [h2, h29782, hlam]
                                                      · linarith only [h29486, h29782, hlam]
                                                    · linarith only [h29781, hlam, p29776_0]
                                                  · have p29776_0 := h29776c.1
                                                    have p29776_1 := h29776c.2.1
                                                    have p29776_2 := h29776c.2.2.1
                                                    have p29776_3 := h29776c.2.2.2
                                                    linarith only [h2, hlam, p29776_0]
                                                  · have p29776_0 := h29776c.1
                                                    have p29776_1 := h29776c.2.1
                                                    have p29776_2 := h29776c.2.2.1
                                                    have p29776_3 := h29776c.2.2.2
                                                    linarith only [hlam, p29776_0]
                                                  · have p29776_0 := h29776c.1
                                                    have p29776_1 := h29776c.2.1
                                                    have p29776_2 := h29776c.2.2.1
                                                    have p29776_3 := h29776c.2.2.2
                                                    linarith only [h29479, hlam, p29776_1]
                                                  · have p29776_0 := h29776c.1
                                                    have p29776_1 := h29776c.2.1
                                                    have p29776_2 := h29776c.2.2.1
                                                    have p29776_3 := h29776c.2.2.2
                                                    linarith only [h29483, hlam, p29776_1]
                                                  · have p29776_0 := h29776c.1
                                                    have p29776_1 := h29776c.2.1
                                                    have p29776_2 := h29776c.2.2.1
                                                    have p29776_3 := h29776c.2.2.2
                                                    linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p29491_1, p29776_1]
                                                  · have p29776_0 := h29776c.1
                                                    have p29776_1 := h29776c.2.1
                                                    have p29776_2 := h29776c.2.2.1
                                                    have p29776_3 := h29776c.2.2.2
                                                    rcases p29776_3 (m.d 0 4) (by simp) with h29791 | h29791
                                                    · linarith only [h19744, h29791, hlam]
                                                    · rcases p29776_3 (m.d 1 4) (by simp) with h29793 | h29793
                                                      · linarith only [h29479, h29793, hlam]
                                                      · rcases p29776_3 (m.d 2 4) (by simp) with h29795 | h29795
                                                        · rcases p29776_3 (m.d 3 4) (by simp) with h29796 | h29796
                                                          · linarith only [h29487, h29796, hlam]
                                                          · linarith only [h23337, h29796, hlam]
                                                        · linarith only [h19744, h29795, hlam]
                                                  · have p29776_0 := h29776c.1
                                                    have p29776_1 := h29776c.2.1
                                                    have p29776_2 := h29776c.2.2.1
                                                    have p29776_3 := h29776c.2.2.2
                                                    rcases p29776_3 (m.d 0 4) (by simp) with h29800 | h29800
                                                    · linarith only [h19744, h29800, hlam]
                                                    · linarith only [h2, h29800, hlam]
                                                  · have p29776_0 := h29776c.1
                                                    have p29776_1 := h29776c.2.1
                                                    have p29776_2 := h29776c.2.2.1
                                                    have p29776_3 := h29776c.2.2.2
                                                    linarith only [hlam, p29776_0]
                                                  · have p29776_0 := h29776c.1
                                                    have p29776_1 := h29776c.2.1
                                                    have p29776_2 := h29776c.2.2.1
                                                    have p29776_3 := h29776c.2.2.2
                                                    linarith only [h1, h23337, h29485, h29487, h29490, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p29776_1]
                                                  · have p29776_0 := h29776c.1
                                                    have p29776_1 := h29776c.2.1
                                                    have p29776_2 := h29776c.2.2.1
                                                    have p29776_3 := h29776c.2.2.2
                                                    rcases p29776_3 (m.d 0 4) (by simp) with h29805 | h29805
                                                    · linarith only [h19744, h29805, hlam]
                                                    · linarith only [h29476, h29805, hlam]
                                                  · have p29776_0 := h29776c.1
                                                    have p29776_1 := h29776c.2.1
                                                    have p29776_2 := h29776c.2.2.1
                                                    have p29776_3 := h29776c.2.2.2
                                                    linarith only [h1, h23337, h29485, h29487, h29490, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p29776_1]
                                                  · have p29776_0 := h29776c.1
                                                    have p29776_1 := h29776c.2.1
                                                    have p29776_2 := h29776c.2.2.1
                                                    have p29776_3 := h29776c.2.2.2
                                                    linarith only [h29479, h29487, hc12, hc23, hlam, hphi, p29776_1]
                                                  · have p29776_0 := h29776c.1
                                                    have p29776_1 := h29776c.2.1
                                                    have p29776_2 := h29776c.2.2.1
                                                    have p29776_3 := h29776c.2.2.2
                                                    linarith only [h29487, hlam, p29776_0]
                                                  · have p29776_0 := h29776c.1
                                                    have p29776_1 := h29776c.2.1
                                                    have p29776_2 := h29776c.2.2.1
                                                    have p29776_3 := h29776c.2.2.2
                                                    linarith only [hlam, p29776_0]
                                                  · have p29776_0 := h29776c.1
                                                    have p29776_1 := h29776c.2.1
                                                    have p29776_2 := h29776c.2.2.1
                                                    have p29776_3 := h29776c.2.2.2
                                                    rcases p29776_3 (m.d 0 4) (by simp) with h29812 | h29812
                                                    · linarith only [h23337, h29812, hlam]
                                                    · linarith only [h29476, h29812, hlam]
                                                  · have p29776_0 := h29776c.1
                                                    have p29776_1 := h29776c.2.1
                                                    have p29776_2 := h29776c.2.2.1
                                                    have p29776_3 := h29776c.2.2.2
                                                    linarith only [h29476, hlam, p29776_0]
                                                  · have p29776_0 := h29776c.1
                                                    have p29776_1 := h29776c.2.1
                                                    have p29776_2 := h29776c.2.2.1
                                                    have p29776_3 := h29776c.2.2.2
                                                    linarith only [h29486, hlam, p29776_0]
                                                  · have p29776_0 := h29776c.1
                                                    have p29776_1 := h29776c.2.1
                                                    have p29776_2 := h29776c.2.2.1
                                                    have p29776_3 := h29776c.2.2.2
                                                    linarith only [h29489, hlam, p29776_0]
                                                  · have p29776_0 := h29776c.1
                                                    have p29776_1 := h29776c.2.1
                                                    have p29776_2 := h29776c.2.2.1
                                                    have p29776_3 := h29776c.2.2.2
                                                    linarith only [h29490, hlam, p29776_0]
                                                  · have p29776_0 := h29776c.1
                                                    have p29776_1 := h29776c.2.1
                                                    have p29776_2 := h29776c.2.2.1
                                                    have p29776_3 := h29776c.2.2.2
                                                    linarith only [hlam, p29776_0]
                                                · linarith only [h29775, hlam, p29726_0]
                                              · linarith only [h19744, h29774, hlam]
                                            · linarith only [h29773, h4, hlam]
                                      · have p29726_0 := h29726c.1
                                        have p29726_1 := h29726c.2.1
                                        have p29726_2 := h29726c.2.2.1
                                        have p29726_3 := h29726c.2.2.2
                                        rcases p29726_3 (m.d 0 2) (by simp) with h29823 | h29823
                                        · linarith only [h22010, h29823, hlam]
                                        · linarith only [h0, h29823, hlam]
                                      · have p29726_0 := h29726c.1
                                        have p29726_1 := h29726c.2.1
                                        have p29726_2 := h29726c.2.2.1
                                        have p29726_3 := h29726c.2.2.2
                                        linarith only [h29488, hlam, p29726_0]
                                      · have p29726_0 := h29726c.1
                                        have p29726_1 := h29726c.2.1
                                        have p29726_2 := h29726c.2.2.1
                                        have p29726_3 := h29726c.2.2.2
                                        linarith only [h29489, hlam, p29726_1]
                                      · have p29726_0 := h29726c.1
                                        have p29726_1 := h29726c.2.1
                                        have p29726_2 := h29726c.2.2.1
                                        have p29726_3 := h29726c.2.2.2
                                        linarith only [hlam, p29726_0]
                                    · rcases h2bigk with h29829c | h29829c | h29829c | h29829c | h29829c | h29829c | h29829c | h29829c | h29829c | h29829c | h29829c | h29829c | h29829c | h29829c | h29829c | h29829c | h29829c | h29829c | h29829c | h29829c | h29829c | h29829c | h29829c | h29829c | h29829c
                                      · have p29829_0 := h29829c.1
                                        have p29829_1 := h29829c.2.1
                                        have p29829_2 := h29829c.2.2.1
                                        have p29829_3 := h29829c.2.2.2
                                        linarith only [hlam, p29829_0]
                                      · have p29829_0 := h29829c.1
                                        have p29829_1 := h29829c.2.1
                                        have p29829_2 := h29829c.2.2.1
                                        have p29829_3 := h29829c.2.2.2
                                        linarith only [h4, hc12, hc23, hlam, hphi, p29829_1]
                                      · have p29829_0 := h29829c.1
                                        have p29829_1 := h29829c.2.1
                                        have p29829_2 := h29829c.2.2.1
                                        have p29829_3 := h29829c.2.2.2
                                        linarith only [h4, hlam, p29829_0]
                                      · have p29829_0 := h29829c.1
                                        have p29829_1 := h29829c.2.1
                                        have p29829_2 := h29829c.2.2.1
                                        have p29829_3 := h29829c.2.2.2
                                        linarith only [h19744, hlam, p29829_0]
                                      · have p29829_0 := h29829c.1
                                        have p29829_1 := h29829c.2.1
                                        have p29829_2 := h29829c.2.2.1
                                        have p29829_3 := h29829c.2.2.2
                                        linarith only [h22010, hlam, p29829_0]
                                      · have p29829_0 := h29829c.1
                                        have p29829_1 := h29829c.2.1
                                        have p29829_2 := h29829c.2.2.1
                                        have p29829_3 := h29829c.2.2.2
                                        linarith only [h0, hlam, p29829_1]
                                      · have p29829_0 := h29829c.1
                                        have p29829_1 := h29829c.2.1
                                        have p29829_2 := h29829c.2.2.1
                                        have p29829_3 := h29829c.2.2.2
                                        linarith only [hlam, p29829_0]
                                      · have p29829_0 := h29829c.1
                                        have p29829_1 := h29829c.2.1
                                        have p29829_2 := h29829c.2.2.1
                                        have p29829_3 := h29829c.2.2.2
                                        linarith only [h29477, hlam, p29829_0]
                                      · have p29829_0 := h29829c.1
                                        have p29829_1 := h29829c.2.1
                                        have p29829_2 := h29829c.2.2.1
                                        have p29829_3 := h29829c.2.2.2
                                        linarith only [h29479, hlam, p29829_0]
                                      · have p29829_0 := h29829c.1
                                        have p29829_1 := h29829c.2.1
                                        have p29829_2 := h29829c.2.2.1
                                        have p29829_3 := h29829c.2.2.2
                                        linarith only [h29481, hlam, p29829_0]
                                      · have p29829_0 := h29829c.1
                                        have p29829_1 := h29829c.2.1
                                        have p29829_2 := h29829c.2.2.1
                                        have p29829_3 := h29829c.2.2.2
                                        rcases p29829_3 (m.d 0 2) (by simp) with h29840 | h29840
                                        · linarith only [h29840, hlam, p29829_0]
                                        · rcases p29829_3 (m.d 1 2) (by simp) with h29842 | h29842
                                          · linarith only [h29477, h29842, hlam]
                                          · rcases p29829_3 (m.d 2 3) (by simp) with h29844 | h29844
                                            · rcases p29829_3 (m.d 2 4) (by simp) with h29845 | h29845
                                              · linarith only [h29487, h29845, hlam]
                                              · linarith only [h19744, h29845, hlam]
                                            · linarith only [h29844, hlam, p29829_0]
                                      · have p29829_0 := h29829c.1
                                        have p29829_1 := h29829c.2.1
                                        have p29829_2 := h29829c.2.2.1
                                        have p29829_3 := h29829c.2.2.2
                                        rcases p29829_3 (m.d 0 2) (by simp) with h29849 | h29849
                                        · linarith only [h29849, h4, hlam]
                                        · linarith only [h0, h29849, hlam]
                                      · have p29829_0 := h29829c.1
                                        have p29829_1 := h29829c.2.1
                                        have p29829_2 := h29829c.2.2.1
                                        have p29829_3 := h29829c.2.2.2
                                        linarith only [hlam, p29829_0]
                                      · have p29829_0 := h29829c.1
                                        have p29829_1 := h29829c.2.1
                                        have p29829_2 := h29829c.2.2.1
                                        have p29829_3 := h29829c.2.2.2
                                        linarith only [h19744, hc02, hc23, hlam, hphi, p29829_1]
                                      · have p29829_0 := h29829c.1
                                        have p29829_1 := h29829c.2.1
                                        have p29829_2 := h29829c.2.2.1
                                        have p29829_3 := h29829c.2.2.2
                                        linarith only [h0, h22010, hc12, hc23, hlam, hphi, p29829_1]
                                      · have p29829_0 := h29829c.1
                                        have p29829_1 := h29829c.2.1
                                        have p29829_2 := h29829c.2.2.1
                                        have p29829_3 := h29829c.2.2.2
                                        rcases p29829_3 (m.d 0 2) (by simp) with h29855 | h29855
                                        · linarith only [h29855, hlam, p29829_0]
                                        · rcases p29829_3 (m.d 1 2) (by simp) with h29857 | h29857
                                          · linarith only [h29479, h29857, hlam]
                                          · rcases p29829_3 (m.d 2 3) (by simp) with h29859 | h29859
                                            · rcases p29829_3 (m.d 2 4) (by simp) with h29860 | h29860
                                              · rcases p29829_3 (m.d 2 5) (by simp) with h29861 | h29861
                                                · linarith only [h29489, h29861, hlam]
                                                · linarith only [h22010, h29861, hlam]
                                              · linarith only [h29860, hlam, p29829_0]
                                            · linarith only [h29859, h4, hlam]
                                      · have p29829_0 := h29829c.1
                                        have p29829_1 := h29829c.2.1
                                        have p29829_2 := h29829c.2.2.1
                                        have p29829_3 := h29829c.2.2.2
                                        rcases p29829_3 (m.d 0 2) (by simp) with h29866 | h29866
                                        · linarith only [h19744, h29866, hlam]
                                        · linarith only [h0, h29866, hlam]
                                      · have p29829_0 := h29829c.1
                                        have p29829_1 := h29829c.2.1
                                        have p29829_2 := h29829c.2.2.1
                                        have p29829_3 := h29829c.2.2.2
                                        linarith only [h29487, hlam, p29829_0]
                                      · have p29829_0 := h29829c.1
                                        have p29829_1 := h29829c.2.1
                                        have p29829_2 := h29829c.2.2.1
                                        have p29829_3 := h29829c.2.2.2
                                        linarith only [hlam, p29829_0]
                                      · have p29829_0 := h29829c.1
                                        have p29829_1 := h29829c.2.1
                                        have p29829_2 := h29829c.2.2.1
                                        have p29829_3 := h29829c.2.2.2
                                        linarith only [h0, h22010, hc12, hc24, hlam, hphi, p29829_1]
                                      · have p29829_0 := h29829c.1
                                        have p29829_1 := h29829c.2.1
                                        have p29829_2 := h29829c.2.2.1
                                        have p29829_3 := h29829c.2.2.2
                                        rcases p29829_3 (m.d 0 2) (by simp) with h29872 | h29872
                                        · linarith only [h29872, hlam, p29829_0]
                                        · rcases p29829_3 (m.d 1 2) (by simp) with h29874 | h29874
                                          · linarith only [h29481, h29874, hlam]
                                          · rcases p29829_3 (m.d 2 3) (by simp) with h29876 | h29876
                                            · rcases p29829_3 (m.d 2 4) (by simp) with h29877 | h29877
                                              · rcases p29829_3 (m.d 2 5) (by simp) with h29878 | h29878
                                                · rcases h4bigk with h29879c | h29879c | h29879c | h29879c | h29879c | h29879c | h29879c | h29879c | h29879c | h29879c | h29879c | h29879c | h29879c | h29879c | h29879c | h29879c | h29879c | h29879c | h29879c | h29879c | h29879c | h29879c | h29879c | h29879c | h29879c
                                                  · have p29879_0 := h29879c.1
                                                    have p29879_1 := h29879c.2.1
                                                    have p29879_2 := h29879c.2.2.1
                                                    have p29879_3 := h29879c.2.2.2
                                                    linarith only [hlam, p29879_0]
                                                  · have p29879_0 := h29879c.1
                                                    have p29879_1 := h29879c.2.1
                                                    have p29879_2 := h29879c.2.2.1
                                                    have p29879_3 := h29879c.2.2.2
                                                    linarith only [h23337, h29483, h29485, h29487, h29490, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p29879_1]
                                                  · have p29879_0 := h29879c.1
                                                    have p29879_1 := h29879c.2.1
                                                    have p29879_2 := h29879c.2.2.1
                                                    have p29879_3 := h29879c.2.2.2
                                                    linarith only [h19744, hlam, p29879_1]
                                                  · have p29879_0 := h29879c.1
                                                    have p29879_1 := h29879c.2.1
                                                    have p29879_2 := h29879c.2.2.1
                                                    have p29879_3 := h29879c.2.2.2
                                                    linarith only [h23337, hlam, p29879_1]
                                                  · have p29879_0 := h29879c.1
                                                    have p29879_1 := h29879c.2.1
                                                    have p29879_2 := h29879c.2.2.1
                                                    have p29879_3 := h29879c.2.2.2
                                                    rcases p29879_3 (m.d 0 4) (by simp) with h29884 | h29884
                                                    · rcases p29879_3 (m.d 1 4) (by simp) with h29885 | h29885
                                                      · linarith only [h2, h29885, hlam]
                                                      · linarith only [h29486, h29885, hlam]
                                                    · linarith only [h29884, hlam, p29879_0]
                                                  · have p29879_0 := h29879c.1
                                                    have p29879_1 := h29879c.2.1
                                                    have p29879_2 := h29879c.2.2.1
                                                    have p29879_3 := h29879c.2.2.2
                                                    linarith only [h2, hlam, p29879_0]
                                                  · have p29879_0 := h29879c.1
                                                    have p29879_1 := h29879c.2.1
                                                    have p29879_2 := h29879c.2.2.1
                                                    have p29879_3 := h29879c.2.2.2
                                                    linarith only [hlam, p29879_0]
                                                  · have p29879_0 := h29879c.1
                                                    have p29879_1 := h29879c.2.1
                                                    have p29879_2 := h29879c.2.2.1
                                                    have p29879_3 := h29879c.2.2.2
                                                    linarith only [h29479, hlam, p29879_1]
                                                  · have p29879_0 := h29879c.1
                                                    have p29879_1 := h29879c.2.1
                                                    have p29879_2 := h29879c.2.2.1
                                                    have p29879_3 := h29879c.2.2.2
                                                    linarith only [h29483, hlam, p29879_1]
                                                  · have p29879_0 := h29879c.1
                                                    have p29879_1 := h29879c.2.1
                                                    have p29879_2 := h29879c.2.2.1
                                                    have p29879_3 := h29879c.2.2.2
                                                    linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p29491_1, p29879_1]
                                                  · have p29879_0 := h29879c.1
                                                    have p29879_1 := h29879c.2.1
                                                    have p29879_2 := h29879c.2.2.1
                                                    have p29879_3 := h29879c.2.2.2
                                                    rcases p29879_3 (m.d 0 4) (by simp) with h29894 | h29894
                                                    · linarith only [h19744, h29894, hlam]
                                                    · rcases p29879_3 (m.d 1 4) (by simp) with h29896 | h29896
                                                      · linarith only [h29479, h29896, hlam]
                                                      · rcases p29879_3 (m.d 2 4) (by simp) with h29898 | h29898
                                                        · rcases p29879_3 (m.d 3 4) (by simp) with h29899 | h29899
                                                          · linarith only [h29487, h29899, hlam]
                                                          · linarith only [h23337, h29899, hlam]
                                                        · linarith only [h19744, h29898, hlam]
                                                  · have p29879_0 := h29879c.1
                                                    have p29879_1 := h29879c.2.1
                                                    have p29879_2 := h29879c.2.2.1
                                                    have p29879_3 := h29879c.2.2.2
                                                    rcases p29879_3 (m.d 0 4) (by simp) with h29903 | h29903
                                                    · linarith only [h19744, h29903, hlam]
                                                    · linarith only [h2, h29903, hlam]
                                                  · have p29879_0 := h29879c.1
                                                    have p29879_1 := h29879c.2.1
                                                    have p29879_2 := h29879c.2.2.1
                                                    have p29879_3 := h29879c.2.2.2
                                                    linarith only [hlam, p29879_0]
                                                  · have p29879_0 := h29879c.1
                                                    have p29879_1 := h29879c.2.1
                                                    have p29879_2 := h29879c.2.2.1
                                                    have p29879_3 := h29879c.2.2.2
                                                    linarith only [h1, h23337, h29485, h29487, h29490, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p29879_1]
                                                  · have p29879_0 := h29879c.1
                                                    have p29879_1 := h29879c.2.1
                                                    have p29879_2 := h29879c.2.2.1
                                                    have p29879_3 := h29879c.2.2.2
                                                    rcases p29879_3 (m.d 0 4) (by simp) with h29908 | h29908
                                                    · linarith only [h19744, h29908, hlam]
                                                    · linarith only [h29476, h29908, hlam]
                                                  · have p29879_0 := h29879c.1
                                                    have p29879_1 := h29879c.2.1
                                                    have p29879_2 := h29879c.2.2.1
                                                    have p29879_3 := h29879c.2.2.2
                                                    linarith only [h1, h23337, h29485, h29487, h29490, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p29879_1]
                                                  · have p29879_0 := h29879c.1
                                                    have p29879_1 := h29879c.2.1
                                                    have p29879_2 := h29879c.2.2.1
                                                    have p29879_3 := h29879c.2.2.2
                                                    linarith only [h29479, h29487, hc12, hc23, hlam, hphi, p29879_1]
                                                  · have p29879_0 := h29879c.1
                                                    have p29879_1 := h29879c.2.1
                                                    have p29879_2 := h29879c.2.2.1
                                                    have p29879_3 := h29879c.2.2.2
                                                    linarith only [h29487, hlam, p29879_0]
                                                  · have p29879_0 := h29879c.1
                                                    have p29879_1 := h29879c.2.1
                                                    have p29879_2 := h29879c.2.2.1
                                                    have p29879_3 := h29879c.2.2.2
                                                    linarith only [hlam, p29879_0]
                                                  · have p29879_0 := h29879c.1
                                                    have p29879_1 := h29879c.2.1
                                                    have p29879_2 := h29879c.2.2.1
                                                    have p29879_3 := h29879c.2.2.2
                                                    rcases p29879_3 (m.d 0 4) (by simp) with h29915 | h29915
                                                    · linarith only [h23337, h29915, hlam]
                                                    · linarith only [h29476, h29915, hlam]
                                                  · have p29879_0 := h29879c.1
                                                    have p29879_1 := h29879c.2.1
                                                    have p29879_2 := h29879c.2.2.1
                                                    have p29879_3 := h29879c.2.2.2
                                                    linarith only [h29476, hlam, p29879_0]
                                                  · have p29879_0 := h29879c.1
                                                    have p29879_1 := h29879c.2.1
                                                    have p29879_2 := h29879c.2.2.1
                                                    have p29879_3 := h29879c.2.2.2
                                                    linarith only [h29486, hlam, p29879_0]
                                                  · have p29879_0 := h29879c.1
                                                    have p29879_1 := h29879c.2.1
                                                    have p29879_2 := h29879c.2.2.1
                                                    have p29879_3 := h29879c.2.2.2
                                                    linarith only [h29489, hlam, p29879_0]
                                                  · have p29879_0 := h29879c.1
                                                    have p29879_1 := h29879c.2.1
                                                    have p29879_2 := h29879c.2.2.1
                                                    have p29879_3 := h29879c.2.2.2
                                                    linarith only [h29490, hlam, p29879_0]
                                                  · have p29879_0 := h29879c.1
                                                    have p29879_1 := h29879c.2.1
                                                    have p29879_2 := h29879c.2.2.1
                                                    have p29879_3 := h29879c.2.2.2
                                                    linarith only [hlam, p29879_0]
                                                · linarith only [h29878, hlam, p29829_0]
                                              · linarith only [h19744, h29877, hlam]
                                            · linarith only [h29876, h4, hlam]
                                      · have p29829_0 := h29829c.1
                                        have p29829_1 := h29829c.2.1
                                        have p29829_2 := h29829c.2.2.1
                                        have p29829_3 := h29829c.2.2.2
                                        rcases p29829_3 (m.d 0 2) (by simp) with h29926 | h29926
                                        · linarith only [h22010, h29926, hlam]
                                        · linarith only [h0, h29926, hlam]
                                      · have p29829_0 := h29829c.1
                                        have p29829_1 := h29829c.2.1
                                        have p29829_2 := h29829c.2.2.1
                                        have p29829_3 := h29829c.2.2.2
                                        linarith only [h29488, hlam, p29829_0]
                                      · have p29829_0 := h29829c.1
                                        have p29829_1 := h29829c.2.1
                                        have p29829_2 := h29829c.2.2.1
                                        have p29829_3 := h29829c.2.2.2
                                        linarith only [h29489, hlam, p29829_1]
                                      · have p29829_0 := h29829c.1
                                        have p29829_1 := h29829c.2.1
                                        have p29829_2 := h29829c.2.2.1
                                        have p29829_3 := h29829c.2.2.2
                                        linarith only [hlam, p29829_0]
                          · linarith only [h29509, hlam, p29491_0]
                        · have p29491_0 := h29491c.1
                          have p29491_1 := h29491c.2.1
                          have p29491_2 := h29491c.2.2.1
                          have p29491_3 := h29491c.2.2.2
                          rcases p29491_3 (m.d 0 1) (by simp) with h29933 | h29933
                          · rcases p29491_3 (m.d 1 2) (by simp) with h29934 | h29934
                            · linarith only [h0, h29934, hlam]
                            · rcases p29491_3 (m.d 1 3) (by simp) with h29936 | h29936
                              · linarith only [h1, h29936, hlam]
                              · linarith only [h29485, h29936, hlam]
                          · linarith only [h29933, hlam, p29491_0]
                        · have p29491_0 := h29491c.1
                          have p29491_1 := h29491c.2.1
                          have p29491_2 := h29491c.2.2.1
                          have p29491_3 := h29491c.2.2.2
                          linarith only [h0, hlam, p29491_0]
                        · have p29491_0 := h29491c.1
                          have p29491_1 := h29491c.2.1
                          have p29491_2 := h29491c.2.2.1
                          have p29491_3 := h29491c.2.2.2
                          linarith only [hlam, p29491_0]
                        · have p29491_0 := h29491c.1
                          have p29491_1 := h29491c.2.1
                          have p29491_2 := h29491c.2.2.1
                          have p29491_3 := h29491c.2.2.2
                          linarith only [h29477, hlam, p29491_1]
                        · have p29491_0 := h29491c.1
                          have p29491_1 := h29491c.2.1
                          have p29491_2 := h29491c.2.2.1
                          have p29491_3 := h29491c.2.2.2
                          linarith only [h29479, hlam, p29491_1]
                        · have p29491_0 := h29491c.1
                          have p29491_1 := h29491c.2.1
                          have p29491_2 := h29491c.2.2.1
                          have p29491_3 := h29491c.2.2.2
                          linarith only [h29481, hlam, p29491_1]
                        · have p29491_0 := h29491c.1
                          have p29491_1 := h29491c.2.1
                          have p29491_2 := h29491c.2.2.1
                          have p29491_3 := h29491c.2.2.2
                          linarith only [h1, hlam, p29491_0]
                        · have p29491_0 := h29491c.1
                          have p29491_1 := h29491c.2.1
                          have p29491_2 := h29491c.2.2.1
                          have p29491_3 := h29491c.2.2.2
                          linarith only [h1, h23337, h29487, hc12, hc23, hlam, hphi, p29491_1]
                        · have p29491_0 := h29491c.1
                          have p29491_1 := h29491c.2.1
                          have p29491_2 := h29491c.2.2.1
                          have p29491_3 := h29491c.2.2.2
                          linarith only [hlam, p29491_0]
                        · have p29491_0 := h29491c.1
                          have p29491_1 := h29491c.2.1
                          have p29491_2 := h29491c.2.2.1
                          have p29491_3 := h29491c.2.2.2
                          linarith only [h29483, hlam, p29491_0]
                        · have p29491_0 := h29491c.1
                          have p29491_1 := h29491c.2.1
                          have p29491_2 := h29491c.2.2.1
                          have p29491_3 := h29491c.2.2.2
                          linarith only [h1, h23337, h29487, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p29491_1]
                        · have p29491_0 := h29491c.1
                          have p29491_1 := h29491c.2.1
                          have p29491_2 := h29491c.2.2.1
                          have p29491_3 := h29491c.2.2.2
                          linarith only [h2, hlam, p29491_0]
                        · have p29491_0 := h29491c.1
                          have p29491_1 := h29491c.2.1
                          have p29491_2 := h29491c.2.2.1
                          have p29491_3 := h29491c.2.2.2
                          linarith only [h2, h23337, h29487, hc12, hc23, hlam, hphi, p29491_1]
                        · have p29491_0 := h29491c.1
                          have p29491_1 := h29491c.2.1
                          have p29491_2 := h29491c.2.2.1
                          have p29491_3 := h29491c.2.2.2
                          linarith only [h2, h23337, h29485, h29487, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p29491_1]
                        · have p29491_0 := h29491c.1
                          have p29491_1 := h29491c.2.1
                          have p29491_2 := h29491c.2.2.1
                          have p29491_3 := h29491c.2.2.2
                          linarith only [hlam, p29491_0]
                        · have p29491_0 := h29491c.1
                          have p29491_1 := h29491c.2.1
                          have p29491_2 := h29491c.2.2.1
                          have p29491_3 := h29491c.2.2.2
                          linarith only [h2, h23337, h29481, h29487, hc12, hc23, hlam, hphi, p29491_1]
                        · have p29491_0 := h29491c.1
                          have p29491_1 := h29491c.2.1
                          have p29491_2 := h29491c.2.2.1
                          have p29491_3 := h29491c.2.2.2
                          linarith only [h3, hlam, p29491_0]
                        · have p29491_0 := h29491c.1
                          have p29491_1 := h29491c.2.1
                          have p29491_2 := h29491c.2.2.1
                          have p29491_3 := h29491c.2.2.2
                          linarith only [h23337, h29475, h29487, h3, hc12, hc23, hlam, hphi, p29491_1]
                        · have p29491_0 := h29491c.1
                          have p29491_1 := h29491c.2.1
                          have p29491_2 := h29491c.2.2.1
                          have p29491_3 := h29491c.2.2.2
                          linarith only [h29485, hlam, p29491_0]
                        · have p29491_0 := h29491c.1
                          have p29491_1 := h29491c.2.1
                          have p29491_2 := h29491c.2.2.1
                          have p29491_3 := h29491c.2.2.2
                          linarith only [h29486, hlam, p29491_0]
                        · have p29491_0 := h29491c.1
                          have p29491_1 := h29491c.2.1
                          have p29491_2 := h29491c.2.2.1
                          have p29491_3 := h29491c.2.2.2
                          linarith only [hlam, p29491_0]
                      · linarith only [h23337, h29476, h29490, hlam]
                    · linarith only [h0, h1, h19744, h23337, h29485, h29486, h29489, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h23337, h29487, h29488, hc03, hc35, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h29963 | h29963
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h29964 | h29964
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h29965 | h29965
                      · rcases h1bigk with h29966c | h29966c | h29966c | h29966c | h29966c | h29966c | h29966c | h29966c | h29966c | h29966c | h29966c | h29966c | h29966c | h29966c | h29966c | h29966c | h29966c | h29966c | h29966c | h29966c | h29966c | h29966c | h29966c | h29966c | h29966c
                        · have p29966_0 := h29966c.1
                          have p29966_1 := h29966c.2.1
                          have p29966_2 := h29966c.2.2.1
                          have p29966_3 := h29966c.2.2.2
                          linarith only [hlam, p29966_0]
                        · have p29966_0 := h29966c.1
                          have p29966_1 := h29966c.2.1
                          have p29966_2 := h29966c.2.2.1
                          have p29966_3 := h29966c.2.2.2
                          rcases p29966_3 (m.d 0 1) (by simp) with h29968 | h29968
                          · rcases p29966_3 (m.d 1 2) (by simp) with h29969 | h29969
                            · linarith only [h29969, hlam, p29966_0]
                            · rcases p29966_3 (m.d 1 3) (by simp) with h29971 | h29971
                              · linarith only [h1, h29971, hlam]
                              · linarith only [h29477, h29971, hlam]
                          · linarith only [h29968, hlam, p29966_0]
                        · have p29966_0 := h29966c.1
                          have p29966_1 := h29966c.2.1
                          have p29966_2 := h29966c.2.2.1
                          have p29966_3 := h29966c.2.2.2
                          rcases p29966_3 (m.d 0 1) (by simp) with h29975 | h29975
                          · rcases p29966_3 (m.d 1 2) (by simp) with h29976 | h29976
                            · linarith only [h0, h29976, hlam]
                            · rcases p29966_3 (m.d 1 3) (by simp) with h29978 | h29978
                              · linarith only [h29978, hlam, p29966_0]
                              · rcases p29966_3 (m.d 1 4) (by simp) with h29980 | h29980
                                · linarith only [h2, h29980, hlam]
                                · linarith only [h29483, h29980, hlam]
                          · linarith only [h29975, hlam, p29966_0]
                        · have p29966_0 := h29966c.1
                          have p29966_1 := h29966c.2.1
                          have p29966_2 := h29966c.2.2.1
                          have p29966_3 := h29966c.2.2.2
                          rcases p29966_3 (m.d 0 1) (by simp) with h29984 | h29984
                          · rcases p29966_3 (m.d 1 2) (by simp) with h29985 | h29985
                            · linarith only [h0, h29985, hlam]
                            · rcases p29966_3 (m.d 1 3) (by simp) with h29987 | h29987
                              · linarith only [h1, h29987, hlam]
                              · rcases p29966_3 (m.d 1 4) (by simp) with h29989 | h29989
                                · linarith only [h29989, hlam, p29966_0]
                                · rcases p29966_3 (m.d 1 5) (by simp) with h29991 | h29991
                                  · linarith only [h29991, h3, hlam]
                                  · rcases h1emax with h29993 | h29993 | h29993 | h29993 | h29993
                                    · linarith only [h29483, h29485, h29965, h29993, hc45, hlam, hphi, ht01, ht0b, ht5b, p29966_1]
                                    · rcases h2bigk with h29995c | h29995c | h29995c | h29995c | h29995c | h29995c | h29995c | h29995c | h29995c | h29995c | h29995c | h29995c | h29995c | h29995c | h29995c | h29995c | h29995c | h29995c | h29995c | h29995c | h29995c | h29995c | h29995c | h29995c | h29995c
                                      · have p29995_0 := h29995c.1
                                        have p29995_1 := h29995c.2.1
                                        have p29995_2 := h29995c.2.2.1
                                        have p29995_3 := h29995c.2.2.2
                                        linarith only [hlam, p29995_0]
                                      · have p29995_0 := h29995c.1
                                        have p29995_1 := h29995c.2.1
                                        have p29995_2 := h29995c.2.2.1
                                        have p29995_3 := h29995c.2.2.2
                                        linarith only [h29487, h4, hc12, hc34, hlam, hphi, ht23, p29995_1]
                                      · have p29995_0 := h29995c.1
                                        have p29995_1 := h29995c.2.1
                                        have p29995_2 := h29995c.2.2.1
                                        have p29995_3 := h29995c.2.2.2
                                        linarith only [h4, hlam, p29995_0]
                                      · have p29995_0 := h29995c.1
                                        have p29995_1 := h29995c.2.1
                                        have p29995_2 := h29995c.2.2.1
                                        have p29995_3 := h29995c.2.2.2
                                        linarith only [h19744, hlam, p29995_0]
                                      · have p29995_0 := h29995c.1
                                        have p29995_1 := h29995c.2.1
                                        have p29995_2 := h29995c.2.2.1
                                        have p29995_3 := h29995c.2.2.2
                                        linarith only [h22010, hlam, p29995_0]
                                      · have p29995_0 := h29995c.1
                                        have p29995_1 := h29995c.2.1
                                        have p29995_2 := h29995c.2.2.1
                                        have p29995_3 := h29995c.2.2.2
                                        linarith only [h0, hlam, p29995_1]
                                      · have p29995_0 := h29995c.1
                                        have p29995_1 := h29995c.2.1
                                        have p29995_2 := h29995c.2.2.1
                                        have p29995_3 := h29995c.2.2.2
                                        linarith only [hlam, p29995_0]
                                      · have p29995_0 := h29995c.1
                                        have p29995_1 := h29995c.2.1
                                        have p29995_2 := h29995c.2.2.1
                                        have p29995_3 := h29995c.2.2.2
                                        linarith only [h29477, hlam, p29995_0]
                                      · have p29995_0 := h29995c.1
                                        have p29995_1 := h29995c.2.1
                                        have p29995_2 := h29995c.2.2.1
                                        have p29995_3 := h29995c.2.2.2
                                        linarith only [h29479, hlam, p29995_0]
                                      · have p29995_0 := h29995c.1
                                        have p29995_1 := h29995c.2.1
                                        have p29995_2 := h29995c.2.2.1
                                        have p29995_3 := h29995c.2.2.2
                                        linarith only [h29481, hlam, p29995_0]
                                      · have p29995_0 := h29995c.1
                                        have p29995_1 := h29995c.2.1
                                        have p29995_2 := h29995c.2.2.1
                                        have p29995_3 := h29995c.2.2.2
                                        linarith only [h29487, hc02, hc34, hlam, hphi, ht23, p29995_1]
                                      · have p29995_0 := h29995c.1
                                        have p29995_1 := h29995c.2.1
                                        have p29995_2 := h29995c.2.2.1
                                        have p29995_3 := h29995c.2.2.2
                                        linarith only [h29487, hc12, hc34, hlam, hphi, ht23, p29995_1]
                                      · have p29995_0 := h29995c.1
                                        have p29995_1 := h29995c.2.1
                                        have p29995_2 := h29995c.2.2.1
                                        have p29995_3 := h29995c.2.2.2
                                        linarith only [hlam, p29995_0]
                                      · have p29995_0 := h29995c.1
                                        have p29995_1 := h29995c.2.1
                                        have p29995_2 := h29995c.2.2.1
                                        have p29995_3 := h29995c.2.2.2
                                        linarith only [h29487, hlam, p29995_1]
                                      · have p29995_0 := h29995c.1
                                        have p29995_1 := h29995c.2.1
                                        have p29995_2 := h29995c.2.2.1
                                        have p29995_3 := h29995c.2.2.2
                                        linarith only [h0, h22010, h29487, hc12, hc34, hlam, hphi, ht23, p29995_1]
                                      · have p29995_0 := h29995c.1
                                        have p29995_1 := h29995c.2.1
                                        have p29995_2 := h29995c.2.2.1
                                        have p29995_3 := h29995c.2.2.2
                                        rcases p29995_3 (m.d 0 2) (by simp) with h30011 | h30011
                                        · linarith only [h30011, hlam, p29995_0]
                                        · rcases p29995_3 (m.d 1 2) (by simp) with h30013 | h30013
                                          · linarith only [h29479, h30013, hlam]
                                          · rcases p29995_3 (m.d 2 3) (by simp) with h30015 | h30015
                                            · linarith only [h29487, h30015, hlam]
                                            · linarith only [h30015, h4, hlam]
                                      · have p29995_0 := h29995c.1
                                        have p29995_1 := h29995c.2.1
                                        have p29995_2 := h29995c.2.2.1
                                        have p29995_3 := h29995c.2.2.2
                                        rcases p29995_3 (m.d 0 2) (by simp) with h30018 | h30018
                                        · linarith only [h19744, h30018, hlam]
                                        · linarith only [h0, h30018, hlam]
                                      · have p29995_0 := h29995c.1
                                        have p29995_1 := h29995c.2.1
                                        have p29995_2 := h29995c.2.2.1
                                        have p29995_3 := h29995c.2.2.2
                                        linarith only [h0, h4, hc12, hc24, hlam, hphi, p29995_1]
                                      · have p29995_0 := h29995c.1
                                        have p29995_1 := h29995c.2.1
                                        have p29995_2 := h29995c.2.2.1
                                        have p29995_3 := h29995c.2.2.2
                                        linarith only [hlam, p29995_0]
                                      · have p29995_0 := h29995c.1
                                        have p29995_1 := h29995c.2.1
                                        have p29995_2 := h29995c.2.2.1
                                        have p29995_3 := h29995c.2.2.2
                                        linarith only [h0, h22010, h29487, hc12, hc34, hlam, hphi, ht23, p29995_1]
                                      · have p29995_0 := h29995c.1
                                        have p29995_1 := h29995c.2.1
                                        have p29995_2 := h29995c.2.2.1
                                        have p29995_3 := h29995c.2.2.2
                                        linarith only [h0, h29487, h29963, hc12, hc34, hlam, hphi, ht23, p29995_1]
                                      · have p29995_0 := h29995c.1
                                        have p29995_1 := h29995c.2.1
                                        have p29995_2 := h29995c.2.2.1
                                        have p29995_3 := h29995c.2.2.2
                                        linarith only [h29487, h29963, hc12, hc34, hlam, hphi, ht23, p29995_1]
                                      · have p29995_0 := h29995c.1
                                        have p29995_1 := h29995c.2.1
                                        have p29995_2 := h29995c.2.2.1
                                        have p29995_3 := h29995c.2.2.2
                                        linarith only [h29963, hlam, p29995_0]
                                      · have p29995_0 := h29995c.1
                                        have p29995_1 := h29995c.2.1
                                        have p29995_2 := h29995c.2.2.1
                                        have p29995_3 := h29995c.2.2.2
                                        linarith only [h29964, hlam, p29995_1]
                                      · have p29995_0 := h29995c.1
                                        have p29995_1 := h29995c.2.1
                                        have p29995_2 := h29995c.2.2.1
                                        have p29995_3 := h29995c.2.2.2
                                        linarith only [hlam, p29995_0]
                                    · rcases h2bigk with h30029c | h30029c | h30029c | h30029c | h30029c | h30029c | h30029c | h30029c | h30029c | h30029c | h30029c | h30029c | h30029c | h30029c | h30029c | h30029c | h30029c | h30029c | h30029c | h30029c | h30029c | h30029c | h30029c | h30029c | h30029c
                                      · have p30029_0 := h30029c.1
                                        have p30029_1 := h30029c.2.1
                                        have p30029_2 := h30029c.2.2.1
                                        have p30029_3 := h30029c.2.2.2
                                        linarith only [hlam, p30029_0]
                                      · have p30029_0 := h30029c.1
                                        have p30029_1 := h30029c.2.1
                                        have p30029_2 := h30029c.2.2.1
                                        have p30029_3 := h30029c.2.2.2
                                        linarith only [h29487, h4, hc12, hc34, hlam, hphi, ht23, p30029_1]
                                      · have p30029_0 := h30029c.1
                                        have p30029_1 := h30029c.2.1
                                        have p30029_2 := h30029c.2.2.1
                                        have p30029_3 := h30029c.2.2.2
                                        linarith only [h4, hlam, p30029_0]
                                      · have p30029_0 := h30029c.1
                                        have p30029_1 := h30029c.2.1
                                        have p30029_2 := h30029c.2.2.1
                                        have p30029_3 := h30029c.2.2.2
                                        linarith only [h19744, hlam, p30029_0]
                                      · have p30029_0 := h30029c.1
                                        have p30029_1 := h30029c.2.1
                                        have p30029_2 := h30029c.2.2.1
                                        have p30029_3 := h30029c.2.2.2
                                        linarith only [h22010, hlam, p30029_0]
                                      · have p30029_0 := h30029c.1
                                        have p30029_1 := h30029c.2.1
                                        have p30029_2 := h30029c.2.2.1
                                        have p30029_3 := h30029c.2.2.2
                                        linarith only [h0, hlam, p30029_1]
                                      · have p30029_0 := h30029c.1
                                        have p30029_1 := h30029c.2.1
                                        have p30029_2 := h30029c.2.2.1
                                        have p30029_3 := h30029c.2.2.2
                                        linarith only [hlam, p30029_0]
                                      · have p30029_0 := h30029c.1
                                        have p30029_1 := h30029c.2.1
                                        have p30029_2 := h30029c.2.2.1
                                        have p30029_3 := h30029c.2.2.2
                                        linarith only [h29477, hlam, p30029_0]
                                      · have p30029_0 := h30029c.1
                                        have p30029_1 := h30029c.2.1
                                        have p30029_2 := h30029c.2.2.1
                                        have p30029_3 := h30029c.2.2.2
                                        linarith only [h29479, hlam, p30029_0]
                                      · have p30029_0 := h30029c.1
                                        have p30029_1 := h30029c.2.1
                                        have p30029_2 := h30029c.2.2.1
                                        have p30029_3 := h30029c.2.2.2
                                        linarith only [h29481, hlam, p30029_0]
                                      · have p30029_0 := h30029c.1
                                        have p30029_1 := h30029c.2.1
                                        have p30029_2 := h30029c.2.2.1
                                        have p30029_3 := h30029c.2.2.2
                                        linarith only [h29487, hc02, hc34, hlam, hphi, ht23, p30029_1]
                                      · have p30029_0 := h30029c.1
                                        have p30029_1 := h30029c.2.1
                                        have p30029_2 := h30029c.2.2.1
                                        have p30029_3 := h30029c.2.2.2
                                        linarith only [h29487, hc12, hc34, hlam, hphi, ht23, p30029_1]
                                      · have p30029_0 := h30029c.1
                                        have p30029_1 := h30029c.2.1
                                        have p30029_2 := h30029c.2.2.1
                                        have p30029_3 := h30029c.2.2.2
                                        linarith only [hlam, p30029_0]
                                      · have p30029_0 := h30029c.1
                                        have p30029_1 := h30029c.2.1
                                        have p30029_2 := h30029c.2.2.1
                                        have p30029_3 := h30029c.2.2.2
                                        linarith only [h29487, hlam, p30029_1]
                                      · have p30029_0 := h30029c.1
                                        have p30029_1 := h30029c.2.1
                                        have p30029_2 := h30029c.2.2.1
                                        have p30029_3 := h30029c.2.2.2
                                        linarith only [h0, h22010, h29487, hc12, hc34, hlam, hphi, ht23, p30029_1]
                                      · have p30029_0 := h30029c.1
                                        have p30029_1 := h30029c.2.1
                                        have p30029_2 := h30029c.2.2.1
                                        have p30029_3 := h30029c.2.2.2
                                        rcases p30029_3 (m.d 0 2) (by simp) with h30045 | h30045
                                        · linarith only [h30045, hlam, p30029_0]
                                        · rcases p30029_3 (m.d 1 2) (by simp) with h30047 | h30047
                                          · linarith only [h29479, h30047, hlam]
                                          · rcases p30029_3 (m.d 2 3) (by simp) with h30049 | h30049
                                            · linarith only [h29487, h30049, hlam]
                                            · linarith only [h30049, h4, hlam]
                                      · have p30029_0 := h30029c.1
                                        have p30029_1 := h30029c.2.1
                                        have p30029_2 := h30029c.2.2.1
                                        have p30029_3 := h30029c.2.2.2
                                        rcases p30029_3 (m.d 0 2) (by simp) with h30052 | h30052
                                        · linarith only [h19744, h30052, hlam]
                                        · linarith only [h0, h30052, hlam]
                                      · have p30029_0 := h30029c.1
                                        have p30029_1 := h30029c.2.1
                                        have p30029_2 := h30029c.2.2.1
                                        have p30029_3 := h30029c.2.2.2
                                        linarith only [h0, h29487, h4, hc12, hc34, hlam, hphi, ht23, p30029_1]
                                      · have p30029_0 := h30029c.1
                                        have p30029_1 := h30029c.2.1
                                        have p30029_2 := h30029c.2.2.1
                                        have p30029_3 := h30029c.2.2.2
                                        linarith only [hlam, p30029_0]
                                      · have p30029_0 := h30029c.1
                                        have p30029_1 := h30029c.2.1
                                        have p30029_2 := h30029c.2.2.1
                                        have p30029_3 := h30029c.2.2.2
                                        linarith only [h0, h22010, h29487, hc12, hc34, hlam, hphi, ht23, p30029_1]
                                      · have p30029_0 := h30029c.1
                                        have p30029_1 := h30029c.2.1
                                        have p30029_2 := h30029c.2.2.1
                                        have p30029_3 := h30029c.2.2.2
                                        linarith only [h0, h29487, h29963, hc12, hc34, hlam, hphi, ht23, p30029_1]
                                      · have p30029_0 := h30029c.1
                                        have p30029_1 := h30029c.2.1
                                        have p30029_2 := h30029c.2.2.1
                                        have p30029_3 := h30029c.2.2.2
                                        linarith only [h29487, h29963, hc12, hc34, hlam, hphi, ht23, p30029_1]
                                      · have p30029_0 := h30029c.1
                                        have p30029_1 := h30029c.2.1
                                        have p30029_2 := h30029c.2.2.1
                                        have p30029_3 := h30029c.2.2.2
                                        linarith only [h29963, hlam, p30029_0]
                                      · have p30029_0 := h30029c.1
                                        have p30029_1 := h30029c.2.1
                                        have p30029_2 := h30029c.2.2.1
                                        have p30029_3 := h30029c.2.2.2
                                        linarith only [h29964, hlam, p30029_1]
                                      · have p30029_0 := h30029c.1
                                        have p30029_1 := h30029c.2.1
                                        have p30029_2 := h30029c.2.2.1
                                        have p30029_3 := h30029c.2.2.2
                                        linarith only [hlam, p30029_0]
                                    · rcases h2bigk with h30063c | h30063c | h30063c | h30063c | h30063c | h30063c | h30063c | h30063c | h30063c | h30063c | h30063c | h30063c | h30063c | h30063c | h30063c | h30063c | h30063c | h30063c | h30063c | h30063c | h30063c | h30063c | h30063c | h30063c | h30063c
                                      · have p30063_0 := h30063c.1
                                        have p30063_1 := h30063c.2.1
                                        have p30063_2 := h30063c.2.2.1
                                        have p30063_3 := h30063c.2.2.2
                                        linarith only [hlam, p30063_0]
                                      · have p30063_0 := h30063c.1
                                        have p30063_1 := h30063c.2.1
                                        have p30063_2 := h30063c.2.2.1
                                        have p30063_3 := h30063c.2.2.2
                                        linarith only [h29487, h4, hc12, hc34, hlam, hphi, ht23, p30063_1]
                                      · have p30063_0 := h30063c.1
                                        have p30063_1 := h30063c.2.1
                                        have p30063_2 := h30063c.2.2.1
                                        have p30063_3 := h30063c.2.2.2
                                        linarith only [h4, hlam, p30063_0]
                                      · have p30063_0 := h30063c.1
                                        have p30063_1 := h30063c.2.1
                                        have p30063_2 := h30063c.2.2.1
                                        have p30063_3 := h30063c.2.2.2
                                        linarith only [h19744, hlam, p30063_0]
                                      · have p30063_0 := h30063c.1
                                        have p30063_1 := h30063c.2.1
                                        have p30063_2 := h30063c.2.2.1
                                        have p30063_3 := h30063c.2.2.2
                                        linarith only [h22010, hlam, p30063_0]
                                      · have p30063_0 := h30063c.1
                                        have p30063_1 := h30063c.2.1
                                        have p30063_2 := h30063c.2.2.1
                                        have p30063_3 := h30063c.2.2.2
                                        linarith only [h0, hlam, p30063_1]
                                      · have p30063_0 := h30063c.1
                                        have p30063_1 := h30063c.2.1
                                        have p30063_2 := h30063c.2.2.1
                                        have p30063_3 := h30063c.2.2.2
                                        linarith only [hlam, p30063_0]
                                      · have p30063_0 := h30063c.1
                                        have p30063_1 := h30063c.2.1
                                        have p30063_2 := h30063c.2.2.1
                                        have p30063_3 := h30063c.2.2.2
                                        linarith only [h29477, hlam, p30063_0]
                                      · have p30063_0 := h30063c.1
                                        have p30063_1 := h30063c.2.1
                                        have p30063_2 := h30063c.2.2.1
                                        have p30063_3 := h30063c.2.2.2
                                        linarith only [h29479, hlam, p30063_0]
                                      · have p30063_0 := h30063c.1
                                        have p30063_1 := h30063c.2.1
                                        have p30063_2 := h30063c.2.2.1
                                        have p30063_3 := h30063c.2.2.2
                                        linarith only [h29481, hlam, p30063_0]
                                      · have p30063_0 := h30063c.1
                                        have p30063_1 := h30063c.2.1
                                        have p30063_2 := h30063c.2.2.1
                                        have p30063_3 := h30063c.2.2.2
                                        linarith only [h29487, hc02, hc34, hlam, hphi, ht23, p30063_1]
                                      · have p30063_0 := h30063c.1
                                        have p30063_1 := h30063c.2.1
                                        have p30063_2 := h30063c.2.2.1
                                        have p30063_3 := h30063c.2.2.2
                                        linarith only [h29487, hc12, hc34, hlam, hphi, ht23, p30063_1]
                                      · have p30063_0 := h30063c.1
                                        have p30063_1 := h30063c.2.1
                                        have p30063_2 := h30063c.2.2.1
                                        have p30063_3 := h30063c.2.2.2
                                        linarith only [hlam, p30063_0]
                                      · have p30063_0 := h30063c.1
                                        have p30063_1 := h30063c.2.1
                                        have p30063_2 := h30063c.2.2.1
                                        have p30063_3 := h30063c.2.2.2
                                        linarith only [h29487, hlam, p30063_1]
                                      · have p30063_0 := h30063c.1
                                        have p30063_1 := h30063c.2.1
                                        have p30063_2 := h30063c.2.2.1
                                        have p30063_3 := h30063c.2.2.2
                                        linarith only [h0, h22010, h29487, hc12, hc34, hlam, hphi, ht23, p30063_1]
                                      · have p30063_0 := h30063c.1
                                        have p30063_1 := h30063c.2.1
                                        have p30063_2 := h30063c.2.2.1
                                        have p30063_3 := h30063c.2.2.2
                                        rcases p30063_3 (m.d 0 2) (by simp) with h30079 | h30079
                                        · linarith only [h30079, hlam, p30063_0]
                                        · rcases p30063_3 (m.d 1 2) (by simp) with h30081 | h30081
                                          · linarith only [h29479, h30081, hlam]
                                          · rcases p30063_3 (m.d 2 3) (by simp) with h30083 | h30083
                                            · linarith only [h29487, h30083, hlam]
                                            · linarith only [h30083, h4, hlam]
                                      · have p30063_0 := h30063c.1
                                        have p30063_1 := h30063c.2.1
                                        have p30063_2 := h30063c.2.2.1
                                        have p30063_3 := h30063c.2.2.2
                                        rcases p30063_3 (m.d 0 2) (by simp) with h30086 | h30086
                                        · linarith only [h19744, h30086, hlam]
                                        · linarith only [h0, h30086, hlam]
                                      · have p30063_0 := h30063c.1
                                        have p30063_1 := h30063c.2.1
                                        have p30063_2 := h30063c.2.2.1
                                        have p30063_3 := h30063c.2.2.2
                                        linarith only [h0, h29487, h4, hc12, hc34, hlam, hphi, ht23, p30063_1]
                                      · have p30063_0 := h30063c.1
                                        have p30063_1 := h30063c.2.1
                                        have p30063_2 := h30063c.2.2.1
                                        have p30063_3 := h30063c.2.2.2
                                        linarith only [hlam, p30063_0]
                                      · have p30063_0 := h30063c.1
                                        have p30063_1 := h30063c.2.1
                                        have p30063_2 := h30063c.2.2.1
                                        have p30063_3 := h30063c.2.2.2
                                        linarith only [h0, h22010, h29487, hc12, hc34, hlam, hphi, ht23, p30063_1]
                                      · have p30063_0 := h30063c.1
                                        have p30063_1 := h30063c.2.1
                                        have p30063_2 := h30063c.2.2.1
                                        have p30063_3 := h30063c.2.2.2
                                        linarith only [h0, h29487, h29963, hc12, hc34, hlam, hphi, ht23, p30063_1]
                                      · have p30063_0 := h30063c.1
                                        have p30063_1 := h30063c.2.1
                                        have p30063_2 := h30063c.2.2.1
                                        have p30063_3 := h30063c.2.2.2
                                        linarith only [h29487, h29963, hc12, hc34, hlam, hphi, ht23, p30063_1]
                                      · have p30063_0 := h30063c.1
                                        have p30063_1 := h30063c.2.1
                                        have p30063_2 := h30063c.2.2.1
                                        have p30063_3 := h30063c.2.2.2
                                        linarith only [h29963, hlam, p30063_0]
                                      · have p30063_0 := h30063c.1
                                        have p30063_1 := h30063c.2.1
                                        have p30063_2 := h30063c.2.2.1
                                        have p30063_3 := h30063c.2.2.2
                                        linarith only [h29964, hlam, p30063_1]
                                      · have p30063_0 := h30063c.1
                                        have p30063_1 := h30063c.2.1
                                        have p30063_2 := h30063c.2.2.1
                                        have p30063_3 := h30063c.2.2.2
                                        linarith only [hlam, p30063_0]
                                    · rcases h2bigk with h30097c | h30097c | h30097c | h30097c | h30097c | h30097c | h30097c | h30097c | h30097c | h30097c | h30097c | h30097c | h30097c | h30097c | h30097c | h30097c | h30097c | h30097c | h30097c | h30097c | h30097c | h30097c | h30097c | h30097c | h30097c
                                      · have p30097_0 := h30097c.1
                                        have p30097_1 := h30097c.2.1
                                        have p30097_2 := h30097c.2.2.1
                                        have p30097_3 := h30097c.2.2.2
                                        linarith only [hlam, p30097_0]
                                      · have p30097_0 := h30097c.1
                                        have p30097_1 := h30097c.2.1
                                        have p30097_2 := h30097c.2.2.1
                                        have p30097_3 := h30097c.2.2.2
                                        linarith only [h29487, h4, hc12, hc34, hlam, hphi, ht23, p30097_1]
                                      · have p30097_0 := h30097c.1
                                        have p30097_1 := h30097c.2.1
                                        have p30097_2 := h30097c.2.2.1
                                        have p30097_3 := h30097c.2.2.2
                                        linarith only [h4, hlam, p30097_0]
                                      · have p30097_0 := h30097c.1
                                        have p30097_1 := h30097c.2.1
                                        have p30097_2 := h30097c.2.2.1
                                        have p30097_3 := h30097c.2.2.2
                                        linarith only [h19744, hlam, p30097_0]
                                      · have p30097_0 := h30097c.1
                                        have p30097_1 := h30097c.2.1
                                        have p30097_2 := h30097c.2.2.1
                                        have p30097_3 := h30097c.2.2.2
                                        linarith only [h22010, hlam, p30097_0]
                                      · have p30097_0 := h30097c.1
                                        have p30097_1 := h30097c.2.1
                                        have p30097_2 := h30097c.2.2.1
                                        have p30097_3 := h30097c.2.2.2
                                        linarith only [h0, hlam, p30097_1]
                                      · have p30097_0 := h30097c.1
                                        have p30097_1 := h30097c.2.1
                                        have p30097_2 := h30097c.2.2.1
                                        have p30097_3 := h30097c.2.2.2
                                        linarith only [hlam, p30097_0]
                                      · have p30097_0 := h30097c.1
                                        have p30097_1 := h30097c.2.1
                                        have p30097_2 := h30097c.2.2.1
                                        have p30097_3 := h30097c.2.2.2
                                        linarith only [h29477, hlam, p30097_0]
                                      · have p30097_0 := h30097c.1
                                        have p30097_1 := h30097c.2.1
                                        have p30097_2 := h30097c.2.2.1
                                        have p30097_3 := h30097c.2.2.2
                                        linarith only [h29479, hlam, p30097_0]
                                      · have p30097_0 := h30097c.1
                                        have p30097_1 := h30097c.2.1
                                        have p30097_2 := h30097c.2.2.1
                                        have p30097_3 := h30097c.2.2.2
                                        linarith only [h29481, hlam, p30097_0]
                                      · have p30097_0 := h30097c.1
                                        have p30097_1 := h30097c.2.1
                                        have p30097_2 := h30097c.2.2.1
                                        have p30097_3 := h30097c.2.2.2
                                        linarith only [h29487, hc02, hc34, hlam, hphi, ht23, p30097_1]
                                      · have p30097_0 := h30097c.1
                                        have p30097_1 := h30097c.2.1
                                        have p30097_2 := h30097c.2.2.1
                                        have p30097_3 := h30097c.2.2.2
                                        linarith only [h29487, hc12, hc34, hlam, hphi, ht23, p30097_1]
                                      · have p30097_0 := h30097c.1
                                        have p30097_1 := h30097c.2.1
                                        have p30097_2 := h30097c.2.2.1
                                        have p30097_3 := h30097c.2.2.2
                                        linarith only [hlam, p30097_0]
                                      · have p30097_0 := h30097c.1
                                        have p30097_1 := h30097c.2.1
                                        have p30097_2 := h30097c.2.2.1
                                        have p30097_3 := h30097c.2.2.2
                                        linarith only [h29487, hlam, p30097_1]
                                      · have p30097_0 := h30097c.1
                                        have p30097_1 := h30097c.2.1
                                        have p30097_2 := h30097c.2.2.1
                                        have p30097_3 := h30097c.2.2.2
                                        linarith only [h0, h22010, h29487, hc12, hc34, hlam, hphi, ht23, p30097_1]
                                      · have p30097_0 := h30097c.1
                                        have p30097_1 := h30097c.2.1
                                        have p30097_2 := h30097c.2.2.1
                                        have p30097_3 := h30097c.2.2.2
                                        rcases p30097_3 (m.d 0 2) (by simp) with h30113 | h30113
                                        · linarith only [h30113, hlam, p30097_0]
                                        · rcases p30097_3 (m.d 1 2) (by simp) with h30115 | h30115
                                          · linarith only [h29479, h30115, hlam]
                                          · rcases p30097_3 (m.d 2 3) (by simp) with h30117 | h30117
                                            · linarith only [h29487, h30117, hlam]
                                            · linarith only [h30117, h4, hlam]
                                      · have p30097_0 := h30097c.1
                                        have p30097_1 := h30097c.2.1
                                        have p30097_2 := h30097c.2.2.1
                                        have p30097_3 := h30097c.2.2.2
                                        rcases p30097_3 (m.d 0 2) (by simp) with h30120 | h30120
                                        · linarith only [h19744, h30120, hlam]
                                        · linarith only [h0, h30120, hlam]
                                      · have p30097_0 := h30097c.1
                                        have p30097_1 := h30097c.2.1
                                        have p30097_2 := h30097c.2.2.1
                                        have p30097_3 := h30097c.2.2.2
                                        linarith only [h0, h29487, h4, hc12, hc34, hlam, hphi, ht23, p30097_1]
                                      · have p30097_0 := h30097c.1
                                        have p30097_1 := h30097c.2.1
                                        have p30097_2 := h30097c.2.2.1
                                        have p30097_3 := h30097c.2.2.2
                                        linarith only [hlam, p30097_0]
                                      · have p30097_0 := h30097c.1
                                        have p30097_1 := h30097c.2.1
                                        have p30097_2 := h30097c.2.2.1
                                        have p30097_3 := h30097c.2.2.2
                                        linarith only [h0, h22010, h29487, hc12, hc34, hlam, hphi, ht23, p30097_1]
                                      · have p30097_0 := h30097c.1
                                        have p30097_1 := h30097c.2.1
                                        have p30097_2 := h30097c.2.2.1
                                        have p30097_3 := h30097c.2.2.2
                                        linarith only [h0, h29487, h29963, hc12, hc34, hlam, hphi, ht23, p30097_1]
                                      · have p30097_0 := h30097c.1
                                        have p30097_1 := h30097c.2.1
                                        have p30097_2 := h30097c.2.2.1
                                        have p30097_3 := h30097c.2.2.2
                                        linarith only [h29487, h29963, hc12, hc34, hlam, hphi, ht23, p30097_1]
                                      · have p30097_0 := h30097c.1
                                        have p30097_1 := h30097c.2.1
                                        have p30097_2 := h30097c.2.2.1
                                        have p30097_3 := h30097c.2.2.2
                                        linarith only [h29963, hlam, p30097_0]
                                      · have p30097_0 := h30097c.1
                                        have p30097_1 := h30097c.2.1
                                        have p30097_2 := h30097c.2.2.1
                                        have p30097_3 := h30097c.2.2.2
                                        linarith only [h29964, hlam, p30097_1]
                                      · have p30097_0 := h30097c.1
                                        have p30097_1 := h30097c.2.1
                                        have p30097_2 := h30097c.2.2.1
                                        have p30097_3 := h30097c.2.2.2
                                        linarith only [hlam, p30097_0]
                          · linarith only [h29984, hlam, p29966_0]
                        · have p29966_0 := h29966c.1
                          have p29966_1 := h29966c.2.1
                          have p29966_2 := h29966c.2.2.1
                          have p29966_3 := h29966c.2.2.2
                          rcases p29966_3 (m.d 0 1) (by simp) with h30132 | h30132
                          · rcases p29966_3 (m.d 1 2) (by simp) with h30133 | h30133
                            · linarith only [h0, h30133, hlam]
                            · rcases p29966_3 (m.d 1 3) (by simp) with h30135 | h30135
                              · linarith only [h1, h30135, hlam]
                              · linarith only [h29485, h30135, hlam]
                          · linarith only [h30132, hlam, p29966_0]
                        · have p29966_0 := h29966c.1
                          have p29966_1 := h29966c.2.1
                          have p29966_2 := h29966c.2.2.1
                          have p29966_3 := h29966c.2.2.2
                          linarith only [h0, hlam, p29966_0]
                        · have p29966_0 := h29966c.1
                          have p29966_1 := h29966c.2.1
                          have p29966_2 := h29966c.2.2.1
                          have p29966_3 := h29966c.2.2.2
                          linarith only [hlam, p29966_0]
                        · have p29966_0 := h29966c.1
                          have p29966_1 := h29966c.2.1
                          have p29966_2 := h29966c.2.2.1
                          have p29966_3 := h29966c.2.2.2
                          linarith only [h29477, hlam, p29966_1]
                        · have p29966_0 := h29966c.1
                          have p29966_1 := h29966c.2.1
                          have p29966_2 := h29966c.2.2.1
                          have p29966_3 := h29966c.2.2.2
                          linarith only [h29479, hlam, p29966_1]
                        · have p29966_0 := h29966c.1
                          have p29966_1 := h29966c.2.1
                          have p29966_2 := h29966c.2.2.1
                          have p29966_3 := h29966c.2.2.2
                          linarith only [h29481, hlam, p29966_1]
                        · have p29966_0 := h29966c.1
                          have p29966_1 := h29966c.2.1
                          have p29966_2 := h29966c.2.2.1
                          have p29966_3 := h29966c.2.2.2
                          linarith only [h1, hlam, p29966_0]
                        · have p29966_0 := h29966c.1
                          have p29966_1 := h29966c.2.1
                          have p29966_2 := h29966c.2.2.1
                          have p29966_3 := h29966c.2.2.2
                          linarith only [h1, h29487, h4, hc12, hc34, hlam, hphi, ht23, p29966_1]
                        · have p29966_0 := h29966c.1
                          have p29966_1 := h29966c.2.1
                          have p29966_2 := h29966c.2.2.1
                          have p29966_3 := h29966c.2.2.2
                          linarith only [hlam, p29966_0]
                        · have p29966_0 := h29966c.1
                          have p29966_1 := h29966c.2.1
                          have p29966_2 := h29966c.2.2.1
                          have p29966_3 := h29966c.2.2.2
                          linarith only [h29483, hlam, p29966_0]
                        · have p29966_0 := h29966c.1
                          have p29966_1 := h29966c.2.1
                          have p29966_2 := h29966c.2.2.1
                          have p29966_3 := h29966c.2.2.2
                          linarith only [h1, h29481, h29487, h4, hc12, hc34, hlam, hphi, ht23, p29966_1]
                        · have p29966_0 := h29966c.1
                          have p29966_1 := h29966c.2.1
                          have p29966_2 := h29966c.2.2.1
                          have p29966_3 := h29966c.2.2.2
                          linarith only [h2, hlam, p29966_0]
                        · have p29966_0 := h29966c.1
                          have p29966_1 := h29966c.2.1
                          have p29966_2 := h29966c.2.2.1
                          have p29966_3 := h29966c.2.2.2
                          rcases p29966_3 (m.d 0 1) (by simp) with h30150 | h30150
                          · rcases p29966_3 (m.d 1 2) (by simp) with h30151 | h30151
                            · linarith only [h29479, h30151, hlam]
                            · rcases p29966_3 (m.d 1 3) (by simp) with h30153 | h30153
                              · linarith only [h29483, h30153, hlam]
                              · linarith only [h29477, h30153, hlam]
                          · linarith only [h0, h30150, hlam]
                        · have p29966_0 := h29966c.1
                          have p29966_1 := h29966c.2.1
                          have p29966_2 := h29966c.2.2.1
                          have p29966_3 := h29966c.2.2.2
                          linarith only [h2, h29485, hc01, hc35, hlam, hphi, ht0b, ht5b, p29966_1]
                        · have p29966_0 := h29966c.1
                          have p29966_1 := h29966c.2.1
                          have p29966_2 := h29966c.2.2.1
                          have p29966_3 := h29966c.2.2.2
                          linarith only [hlam, p29966_0]
                        · have p29966_0 := h29966c.1
                          have p29966_1 := h29966c.2.1
                          have p29966_2 := h29966c.2.2.1
                          have p29966_3 := h29966c.2.2.2
                          rcases p29966_3 (m.d 0 1) (by simp) with h30159 | h30159
                          · rcases p29966_3 (m.d 1 2) (by simp) with h30160 | h30160
                            · linarith only [h29479, h30160, hlam]
                            · rcases p29966_3 (m.d 1 3) (by simp) with h30162 | h30162
                              · linarith only [h29483, h30162, hlam]
                              · linarith only [h29485, h30162, hlam]
                          · linarith only [h3, h30159, hlam]
                        · have p29966_0 := h29966c.1
                          have p29966_1 := h29966c.2.1
                          have p29966_2 := h29966c.2.2.1
                          have p29966_3 := h29966c.2.2.2
                          linarith only [h3, hlam, p29966_0]
                        · have p29966_0 := h29966c.1
                          have p29966_1 := h29966c.2.1
                          have p29966_2 := h29966c.2.2.1
                          have p29966_3 := h29966c.2.2.2
                          linarith only [h22010, h29487, h29963, h3, hc12, hc34, hlam, hphi, ht23, p29966_1]
                        · have p29966_0 := h29966c.1
                          have p29966_1 := h29966c.2.1
                          have p29966_2 := h29966c.2.2.1
                          have p29966_3 := h29966c.2.2.2
                          linarith only [h29485, hlam, p29966_0]
                        · have p29966_0 := h29966c.1
                          have p29966_1 := h29966c.2.1
                          have p29966_2 := h29966c.2.2.1
                          have p29966_3 := h29966c.2.2.2
                          linarith only [h29486, hlam, p29966_0]
                        · have p29966_0 := h29966c.1
                          have p29966_1 := h29966c.2.1
                          have p29966_2 := h29966c.2.2.1
                          have p29966_3 := h29966c.2.2.2
                          linarith only [hlam, p29966_0]
                      · linarith only [h0, h29487, h29965, h4, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h0, h19744, h29475, h29486, h29487, h29964, h3, h4, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h1, h29485, h29963, h4, hlam]
              · linarith only [h29483, h29485, h29486, hlam]
            · linarith only [h23337, h29475, h29485, hc13, hc34, hlam, hphi]
  · linarith only [h23337, h29475, h29476, hlam]

set_option maxHeartbeats 17120000 in
set_option maxHeartbeats 17120000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h23337 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h29475 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h30177 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h30178 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h19744 := hg19744
  have h22010 := hg22010
  linarith only [h0, h30178, h4, hlam]

set_option maxHeartbeats 17120000 in
set_option maxHeartbeats 17120000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h23337 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h29475 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h30177 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h30178 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h30180 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h19744 := hg19744
  have h22010 := hg22010
  linarith only [h0, h19744, h30180, hlam]

set_option maxHeartbeats 17120000 in
set_option maxHeartbeats 17120000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h23337 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h29475 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h30177 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h30178 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h30180 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h30182 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h19744 := hg19744
  have h22010 := hg22010
  linarith only [h0, h22010, h30182, hlam]

set_option maxHeartbeats 17120000 in
set_option maxHeartbeats 17120000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h23337 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h29475 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h30177 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h30178 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h30180 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h30182 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h30184 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h19744 := hg19744
  have h22010 := hg22010
  linarith only [h1, h23337, h30184, hlam]

end R2N4
