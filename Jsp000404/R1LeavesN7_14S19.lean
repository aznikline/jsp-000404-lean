import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_14S17
import Jsp000404.R1LeavesN7_14S18

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 14754000 in
set_option maxHeartbeats 14754000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x0_x0_x0_x0_x0_x0_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h4610 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h4611 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h4612 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4613 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4614 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4615 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4616 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4989 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h5097 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 1 2 3 (by decide) (by decide) with h5496 | h5496
  · rcases m.htr 1 2 4 (by decide) (by decide) with h5497 | h5497
    · rcases m.htr 1 2 5 (by decide) (by decide) with h5498 | h5498
      · rcases m.htr 1 3 4 (by decide) (by decide) with h5499 | h5499
        · linarith only [h4610, h4616, h5499, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h5501 | h5501
          · linarith only [h4610, h4989, h5501, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5503 | h5503
            · linarith only [h0, h4611, h5097, h5503, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5505 | h5505
              · linarith only [h4613, h4616, h5505, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5507 | h5507
                · linarith only [h4610, h4989, h5496, h5507, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5509 | h5509
                  · linarith only [h4614, h4616, h5097, h5509, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5511 | h5511
                    · rcases h0bigk with h5512c | h5512c | h5512c | h5512c | h5512c | h5512c | h5512c | h5512c | h5512c | h5512c | h5512c | h5512c | h5512c | h5512c | h5512c | h5512c | h5512c | h5512c | h5512c | h5512c | h5512c | h5512c | h5512c | h5512c | h5512c
                      · have p5512_0 := h5512c.1
                        have p5512_1 := h5512c.2.1
                        have p5512_2 := h5512c.2.2.1
                        have p5512_3 := h5512c.2.2.2
                        linarith only [hlam, p5512_0]
                      · have p5512_0 := h5512c.1
                        have p5512_1 := h5512c.2.1
                        have p5512_2 := h5512c.2.2.1
                        have p5512_3 := h5512c.2.2.2
                        linarith only [h0, hlam, p5512_1]
                      · have p5512_0 := h5512c.1
                        have p5512_1 := h5512c.2.1
                        have p5512_2 := h5512c.2.2.1
                        have p5512_3 := h5512c.2.2.2
                        rcases p5512_3 (m.d 0 1) (by simp) with h5515 | h5515
                        · rcases p5512_3 (m.d 0 2) (by simp) with h5516 | h5516
                          · rcases p5512_3 (m.d 0 3) (by simp) with h5517 | h5517
                            · linarith only [h4610, h5517, hlam]
                            · rcases p5512_3 (m.d 0 4) (by simp) with h5519 | h5519
                              · linarith only [h4611, h5519, hlam]
                              · linarith only [h4616, h5519, hlam]
                          · linarith only [h4613, h5516, hlam]
                        · linarith only [h4610, h5515, hlam]
                      · have p5512_0 := h5512c.1
                        have p5512_1 := h5512c.2.1
                        have p5512_2 := h5512c.2.2.1
                        have p5512_3 := h5512c.2.2.2
                        rcases p5512_3 (m.d 0 1) (by simp) with h5524 | h5524
                        · rcases p5512_3 (m.d 0 2) (by simp) with h5525 | h5525
                          · rcases p5512_3 (m.d 0 3) (by simp) with h5526 | h5526
                            · linarith only [h4610, h5526, hlam]
                            · rcases p5512_3 (m.d 0 4) (by simp) with h5528 | h5528
                              · linarith only [h4611, h5528, hlam]
                              · rcases p5512_3 (m.d 0 5) (by simp) with h5530 | h5530
                                · linarith only [h4612, h5530, hlam]
                                · linarith only [h5097, h5530, hlam]
                          · linarith only [h4614, h5525, hlam]
                        · linarith only [h4611, h5524, hlam]
                      · have p5512_0 := h5512c.1
                        have p5512_1 := h5512c.2.1
                        have p5512_2 := h5512c.2.2.1
                        have p5512_3 := h5512c.2.2.2
                        rcases p5512_3 (m.d 0 1) (by simp) with h5535 | h5535
                        · rcases p5512_3 (m.d 0 2) (by simp) with h5536 | h5536
                          · rcases p5512_3 (m.d 0 3) (by simp) with h5537 | h5537
                            · linarith only [h4610, h5537, hlam]
                            · rcases p5512_3 (m.d 0 4) (by simp) with h5539 | h5539
                              · linarith only [h4611, h5539, hlam]
                              · rcases p5512_3 (m.d 0 5) (by simp) with h5541 | h5541
                                · linarith only [h4612, h5541, hlam]
                                · rcases h2bigk with h5543c | h5543c | h5543c | h5543c | h5543c | h5543c | h5543c | h5543c | h5543c | h5543c | h5543c | h5543c | h5543c | h5543c | h5543c | h5543c | h5543c | h5543c | h5543c | h5543c | h5543c | h5543c | h5543c | h5543c | h5543c
                                  · have p5543_0 := h5543c.1
                                    have p5543_1 := h5543c.2.1
                                    have p5543_2 := h5543c.2.2.1
                                    have p5543_3 := h5543c.2.2.2
                                    linarith only [hlam, p5543_0]
                                  · have p5543_0 := h5543c.1
                                    have p5543_1 := h5543c.2.1
                                    have p5543_2 := h5543c.2.2.1
                                    have p5543_3 := h5543c.2.2.2
                                    linarith only [h0, hlam, p5543_1]
                                  · have p5543_0 := h5543c.1
                                    have p5543_1 := h5543c.2.1
                                    have p5543_2 := h5543c.2.2.1
                                    have p5543_3 := h5543c.2.2.2
                                    rcases p5543_3 (m.d 0 2) (by simp) with h5546 | h5546
                                    · rcases p5543_3 (m.d 1 2) (by simp) with h5547 | h5547
                                      · rcases p5543_3 (m.d 2 3) (by simp) with h5548 | h5548
                                        · linarith only [h5548, hlam, p5543_0]
                                        · rcases p5543_3 (m.d 2 4) (by simp) with h5550 | h5550
                                          · linarith only [h4614, h5550, hlam]
                                          · linarith only [h5505, h5550, hlam]
                                      · linarith only [h5496, h5547, hlam]
                                    · linarith only [h5546, hlam, p5543_0]
                                  · have p5543_0 := h5543c.1
                                    have p5543_1 := h5543c.2.1
                                    have p5543_2 := h5543c.2.2.1
                                    have p5543_3 := h5543c.2.2.2
                                    rcases p5543_3 (m.d 0 2) (by simp) with h5555 | h5555
                                    · rcases p5543_3 (m.d 1 2) (by simp) with h5556 | h5556
                                      · rcases p5543_3 (m.d 2 3) (by simp) with h5557 | h5557
                                        · linarith only [h4613, h5557, hlam]
                                        · rcases p5543_3 (m.d 2 4) (by simp) with h5559 | h5559
                                          · linarith only [h5559, hlam, p5543_0]
                                          · rcases p5543_3 (m.d 2 5) (by simp) with h5561 | h5561
                                            · linarith only [h4615, h5561, hlam]
                                            · linarith only [h5509, h5561, hlam]
                                      · linarith only [h5497, h5556, hlam]
                                    · linarith only [h5555, hlam, p5543_0]
                                  · have p5543_0 := h5543c.1
                                    have p5543_1 := h5543c.2.1
                                    have p5543_2 := h5543c.2.2.1
                                    have p5543_3 := h5543c.2.2.2
                                    rcases p5543_3 (m.d 0 2) (by simp) with h5566 | h5566
                                    · rcases p5543_3 (m.d 1 2) (by simp) with h5567 | h5567
                                      · rcases p5543_3 (m.d 2 3) (by simp) with h5568 | h5568
                                        · linarith only [h4613, h5568, hlam]
                                        · rcases p5543_3 (m.d 2 4) (by simp) with h5570 | h5570
                                          · linarith only [h4614, h5570, hlam]
                                          · rcases p5543_3 (m.d 2 5) (by simp) with h5572 | h5572
                                            · linarith only [h5572, hlam, p5543_0]
                                            · rcases h3bigk with h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c
                                              · have p5574_0 := h5574c.1
                                                have p5574_1 := h5574c.2.1
                                                have p5574_2 := h5574c.2.2.1
                                                have p5574_3 := h5574c.2.2.2
                                                linarith only [hlam, p5574_0]
                                              · have p5574_0 := h5574c.1
                                                have p5574_1 := h5574c.2.1
                                                have p5574_2 := h5574c.2.2.1
                                                have p5574_3 := h5574c.2.2.2
                                                linarith only [h0, h4616, h5097, h5496, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5512_1, p5574_1]
                                              · have p5574_0 := h5574c.1
                                                have p5574_1 := h5574c.2.1
                                                have p5574_2 := h5574c.2.2.1
                                                have p5574_3 := h5574c.2.2.2
                                                linarith only [h0, h4616, h5097, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5512_1, p5574_1]
                                              · have p5574_0 := h5574c.1
                                                have p5574_1 := h5574c.2.1
                                                have p5574_2 := h5574c.2.2.1
                                                have p5574_3 := h5574c.2.2.2
                                                linarith only [h4616, hlam, p5574_0]
                                              · have p5574_0 := h5574c.1
                                                have p5574_1 := h5574c.2.1
                                                have p5574_2 := h5574c.2.2.1
                                                have p5574_3 := h5574c.2.2.2
                                                linarith only [h4989, hlam, p5574_0]
                                              · have p5574_0 := h5574c.1
                                                have p5574_1 := h5574c.2.1
                                                have p5574_2 := h5574c.2.2.1
                                                have p5574_3 := h5574c.2.2.2
                                                linarith only [h4610, hlam, p5574_0]
                                              · have p5574_0 := h5574c.1
                                                have p5574_1 := h5574c.2.1
                                                have p5574_2 := h5574c.2.2.1
                                                have p5574_3 := h5574c.2.2.2
                                                linarith only [hlam, p5574_0]
                                              · have p5574_0 := h5574c.1
                                                have p5574_1 := h5574c.2.1
                                                have p5574_2 := h5574c.2.2.1
                                                have p5574_3 := h5574c.2.2.2
                                                linarith only [h0, h4610, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5574_1]
                                              · have p5574_0 := h5574c.1
                                                have p5574_1 := h5574c.2.1
                                                have p5574_2 := h5574c.2.2.1
                                                have p5574_3 := h5574c.2.2.2
                                                linarith only [h5499, hlam, p5574_0]
                                              · have p5574_0 := h5574c.1
                                                have p5574_1 := h5574c.2.1
                                                have p5574_2 := h5574c.2.2.1
                                                have p5574_3 := h5574c.2.2.2
                                                linarith only [h5501, hlam, p5574_0]
                                              · have p5574_0 := h5574c.1
                                                have p5574_1 := h5574c.2.1
                                                have p5574_2 := h5574c.2.2.1
                                                have p5574_3 := h5574c.2.2.2
                                                linarith only [h4613, hlam, p5574_0]
                                              · have p5574_0 := h5574c.1
                                                have p5574_1 := h5574c.2.1
                                                have p5574_2 := h5574c.2.2.1
                                                have p5574_3 := h5574c.2.2.2
                                                linarith only [h5496, hlam, p5574_0]
                                              · have p5574_0 := h5574c.1
                                                have p5574_1 := h5574c.2.1
                                                have p5574_2 := h5574c.2.2.1
                                                have p5574_3 := h5574c.2.2.2
                                                linarith only [hlam, p5574_0]
                                              · have p5574_0 := h5574c.1
                                                have p5574_1 := h5574c.2.1
                                                have p5574_2 := h5574c.2.2.1
                                                have p5574_3 := h5574c.2.2.2
                                                linarith only [h5505, hlam, p5574_0]
                                              · have p5574_0 := h5574c.1
                                                have p5574_1 := h5574c.2.1
                                                have p5574_2 := h5574c.2.2.1
                                                have p5574_3 := h5574c.2.2.2
                                                linarith only [h5507, hlam, p5574_0]
                                              · have p5574_0 := h5574c.1
                                                have p5574_1 := h5574c.2.1
                                                have p5574_2 := h5574c.2.2.1
                                                have p5574_3 := h5574c.2.2.2
                                                rcases p5574_3 (m.d 0 3) (by simp) with h5590 | h5590
                                                · linarith only [h5590, hlam, p5574_0]
                                                · rcases p5574_3 (m.d 1 3) (by simp) with h5592 | h5592
                                                  · linarith only [h5499, h5592, hlam]
                                                  · rcases p5574_3 (m.d 2 3) (by simp) with h5594 | h5594
                                                    · linarith only [h5505, h5594, hlam]
                                                    · rcases p5574_3 (m.d 3 4) (by simp) with h5596 | h5596
                                                      · rcases p5574_3 (m.d 3 5) (by simp) with h5597 | h5597
                                                        · linarith only [h5511, h5597, hlam]
                                                        · linarith only [h4989, h5597, hlam]
                                                      · linarith only [h5596, hlam, p5574_0]
                                              · have p5574_0 := h5574c.1
                                                have p5574_1 := h5574c.2.1
                                                have p5574_2 := h5574c.2.2.1
                                                have p5574_3 := h5574c.2.2.2
                                                rcases p5574_3 (m.d 0 3) (by simp) with h5601 | h5601
                                                · linarith only [h4616, h5601, hlam]
                                                · linarith only [h4610, h5601, hlam]
                                              · have p5574_0 := h5574c.1
                                                have p5574_1 := h5574c.2.1
                                                have p5574_2 := h5574c.2.2.1
                                                have p5574_3 := h5574c.2.2.2
                                                rcases p5574_3 (m.d 0 3) (by simp) with h5604 | h5604
                                                · linarith only [h4616, h5604, hlam]
                                                · linarith only [h4613, h5604, hlam]
                                              · have p5574_0 := h5574c.1
                                                have p5574_1 := h5574c.2.1
                                                have p5574_2 := h5574c.2.2.1
                                                have p5574_3 := h5574c.2.2.2
                                                linarith only [hlam, p5574_0]
                                              · have p5574_0 := h5574c.1
                                                have p5574_1 := h5574c.2.1
                                                have p5574_2 := h5574c.2.2.1
                                                have p5574_3 := h5574c.2.2.2
                                                linarith only [h4616, h5097, h5511, hc03, hc34, hlam, hphi, p5574_1]
                                              · have p5574_0 := h5574c.1
                                                have p5574_1 := h5574c.2.1
                                                have p5574_2 := h5574c.2.2.1
                                                have p5574_3 := h5574c.2.2.2
                                                rcases p5574_3 (m.d 0 3) (by simp) with h5609 | h5609
                                                · linarith only [h5609, hlam, p5574_0]
                                                · rcases p5574_3 (m.d 1 3) (by simp) with h5611 | h5611
                                                  · linarith only [h5501, h5611, hlam]
                                                  · rcases p5574_3 (m.d 2 3) (by simp) with h5613 | h5613
                                                    · linarith only [h5507, h5613, hlam]
                                                    · rcases p5574_3 (m.d 3 4) (by simp) with h5615 | h5615
                                                      · rcases p5574_3 (m.d 3 5) (by simp) with h5616 | h5616
                                                        · rcases h5bigk with h5617c | h5617c | h5617c | h5617c | h5617c | h5617c | h5617c | h5617c | h5617c | h5617c | h5617c | h5617c | h5617c | h5617c | h5617c | h5617c | h5617c | h5617c | h5617c | h5617c | h5617c | h5617c | h5617c | h5617c | h5617c
                                                          · have p5617_0 := h5617c.1
                                                            have p5617_1 := h5617c.2.1
                                                            have p5617_2 := h5617c.2.2.1
                                                            have p5617_3 := h5617c.2.2.2
                                                            linarith only [hlam, p5617_0]
                                                          · have p5617_0 := h5617c.1
                                                            have p5617_1 := h5617c.2.1
                                                            have p5617_2 := h5617c.2.2.1
                                                            have p5617_3 := h5617c.2.2.2
                                                            linarith only [h0, h5496, h5499, h5503, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5512_1, p5617_1]
                                                          · have p5617_0 := h5617c.1
                                                            have p5617_1 := h5617c.2.1
                                                            have p5617_2 := h5617c.2.2.1
                                                            have p5617_3 := h5617c.2.2.2
                                                            linarith only [h0, h5505, h5509, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5512_1, p5617_1]
                                                          · have p5617_0 := h5617c.1
                                                            have p5617_1 := h5617c.2.1
                                                            have p5617_2 := h5617c.2.2.1
                                                            have p5617_3 := h5617c.2.2.2
                                                            linarith only [h4989, hlam, p5617_1]
                                                          · have p5617_0 := h5617c.1
                                                            have p5617_1 := h5617c.2.1
                                                            have p5617_2 := h5617c.2.2.1
                                                            have p5617_3 := h5617c.2.2.2
                                                            linarith only [h5097, hlam, p5617_1]
                                                          · have p5617_0 := h5617c.1
                                                            have p5617_1 := h5617c.2.1
                                                            have p5617_2 := h5617c.2.2.1
                                                            have p5617_3 := h5617c.2.2.2
                                                            linarith only [h4612, hlam, p5617_0]
                                                          · have p5617_0 := h5617c.1
                                                            have p5617_1 := h5617c.2.1
                                                            have p5617_2 := h5617c.2.2.1
                                                            have p5617_3 := h5617c.2.2.2
                                                            linarith only [hlam, p5617_0]
                                                          · have p5617_0 := h5617c.1
                                                            have p5617_1 := h5617c.2.1
                                                            have p5617_2 := h5617c.2.2.1
                                                            have p5617_3 := h5617c.2.2.2
                                                            linarith only [h0, h4612, h5505, h5509, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5617_1]
                                                          · have p5617_0 := h5617c.1
                                                            have p5617_1 := h5617c.2.1
                                                            have p5617_2 := h5617c.2.2.1
                                                            have p5617_3 := h5617c.2.2.2
                                                            linarith only [h5501, hlam, p5617_1]
                                                          · have p5617_0 := h5617c.1
                                                            have p5617_1 := h5617c.2.1
                                                            have p5617_2 := h5617c.2.2.1
                                                            have p5617_3 := h5617c.2.2.2
                                                            linarith only [h5503, hlam, p5617_1]
                                                          · have p5617_0 := h5617c.1
                                                            have p5617_1 := h5617c.2.1
                                                            have p5617_2 := h5617c.2.2.1
                                                            have p5617_3 := h5617c.2.2.2
                                                            linarith only [h4615, hlam, p5617_1]
                                                          · have p5617_0 := h5617c.1
                                                            have p5617_1 := h5617c.2.1
                                                            have p5617_2 := h5617c.2.2.1
                                                            have p5617_3 := h5617c.2.2.2
                                                            linarith only [h5498, hlam, p5617_1]
                                                          · have p5617_0 := h5617c.1
                                                            have p5617_1 := h5617c.2.1
                                                            have p5617_2 := h5617c.2.2.1
                                                            have p5617_3 := h5617c.2.2.2
                                                            linarith only [hlam, p5617_0]
                                                          · have p5617_0 := h5617c.1
                                                            have p5617_1 := h5617c.2.1
                                                            have p5617_2 := h5617c.2.2.1
                                                            have p5617_3 := h5617c.2.2.2
                                                            linarith only [h5507, hlam, p5617_1]
                                                          · have p5617_0 := h5617c.1
                                                            have p5617_1 := h5617c.2.1
                                                            have p5617_2 := h5617c.2.2.1
                                                            have p5617_3 := h5617c.2.2.2
                                                            linarith only [h5509, hlam, p5617_1]
                                                          · have p5617_0 := h5617c.1
                                                            have p5617_1 := h5617c.2.1
                                                            have p5617_2 := h5617c.2.2.1
                                                            have p5617_3 := h5617c.2.2.2
                                                            rcases p5617_3 (m.d 0 5) (by simp) with h5633 | h5633
                                                            · linarith only [h4989, h5633, hlam]
                                                            · rcases p5617_3 (m.d 1 5) (by simp) with h5635 | h5635
                                                              · linarith only [h5501, h5635, hlam]
                                                              · rcases p5617_3 (m.d 2 5) (by simp) with h5637 | h5637
                                                                · linarith only [h5507, h5637, hlam]
                                                                · rcases p5617_3 (m.d 3 5) (by simp) with h5639 | h5639
                                                                  · rcases p5617_3 (m.d 4 5) (by simp) with h5640 | h5640
                                                                    · linarith only [h5511, h5640, hlam]
                                                                    · linarith only [h5097, h5640, hlam]
                                                                  · linarith only [h4989, h5639, hlam]
                                                          · have p5617_0 := h5617c.1
                                                            have p5617_1 := h5617c.2.1
                                                            have p5617_2 := h5617c.2.2.1
                                                            have p5617_3 := h5617c.2.2.2
                                                            rcases p5617_3 (m.d 0 5) (by simp) with h5644 | h5644
                                                            · linarith only [h4989, h5644, hlam]
                                                            · linarith only [h4612, h5644, hlam]
                                                          · have p5617_0 := h5617c.1
                                                            have p5617_1 := h5617c.2.1
                                                            have p5617_2 := h5617c.2.2.1
                                                            have p5617_3 := h5617c.2.2.2
                                                            rcases p5617_3 (m.d 0 5) (by simp) with h5647 | h5647
                                                            · linarith only [h4989, h5647, hlam]
                                                            · linarith only [h4615, h5647, hlam]
                                                          · have p5617_0 := h5617c.1
                                                            have p5617_1 := h5617c.2.1
                                                            have p5617_2 := h5617c.2.2.1
                                                            have p5617_3 := h5617c.2.2.2
                                                            linarith only [hlam, p5617_0]
                                                          · have p5617_0 := h5617c.1
                                                            have p5617_1 := h5617c.2.1
                                                            have p5617_2 := h5617c.2.2.1
                                                            have p5617_3 := h5617c.2.2.2
                                                            linarith only [h4610, h4616, h5097, h5496, hc23, hc35, hlam, hphi, p5617_1]
                                                          · have p5617_0 := h5617c.1
                                                            have p5617_1 := h5617c.2.1
                                                            have p5617_2 := h5617c.2.2.1
                                                            have p5617_3 := h5617c.2.2.2
                                                            linarith only [h4615, h5505, h5509, h5511, hc23, hc34, hlam, hphi, p5617_1]
                                                          · have p5617_0 := h5617c.1
                                                            have p5617_1 := h5617c.2.1
                                                            have p5617_2 := h5617c.2.2.1
                                                            have p5617_3 := h5617c.2.2.2
                                                            linarith only [h5498, h5505, h5509, h5511, hc23, hc34, hlam, hphi, p5617_1]
                                                          · have p5617_0 := h5617c.1
                                                            have p5617_1 := h5617c.2.1
                                                            have p5617_2 := h5617c.2.2.1
                                                            have p5617_3 := h5617c.2.2.2
                                                            linarith only [h5505, h5509, h5511, hc23, hc34, hlam, hphi, p5617_1]
                                                          · have p5617_0 := h5617c.1
                                                            have p5617_1 := h5617c.2.1
                                                            have p5617_2 := h5617c.2.2.1
                                                            have p5617_3 := h5617c.2.2.2
                                                            linarith only [h5511, hlam, p5617_0]
                                                          · have p5617_0 := h5617c.1
                                                            have p5617_1 := h5617c.2.1
                                                            have p5617_2 := h5617c.2.2.1
                                                            have p5617_3 := h5617c.2.2.2
                                                            linarith only [hlam, p5617_0]
                                                        · linarith only [h5616, hlam, p5574_0]
                                                      · linarith only [h4616, h5615, hlam]
                                              · have p5574_0 := h5574c.1
                                                have p5574_1 := h5574c.2.1
                                                have p5574_2 := h5574c.2.2.1
                                                have p5574_3 := h5574c.2.2.2
                                                rcases p5574_3 (m.d 0 3) (by simp) with h5659 | h5659
                                                · linarith only [h4989, h5659, hlam]
                                                · linarith only [h4610, h5659, hlam]
                                              · have p5574_0 := h5574c.1
                                                have p5574_1 := h5574c.2.1
                                                have p5574_2 := h5574c.2.2.1
                                                have p5574_3 := h5574c.2.2.2
                                                rcases p5574_3 (m.d 0 3) (by simp) with h5662 | h5662
                                                · linarith only [h4989, h5662, hlam]
                                                · linarith only [h4613, h5662, hlam]
                                              · have p5574_0 := h5574c.1
                                                have p5574_1 := h5574c.2.1
                                                have p5574_2 := h5574c.2.2.1
                                                have p5574_3 := h5574c.2.2.2
                                                linarith only [h5511, hlam, p5574_0]
                                              · have p5574_0 := h5574c.1
                                                have p5574_1 := h5574c.2.1
                                                have p5574_2 := h5574c.2.2.1
                                                have p5574_3 := h5574c.2.2.2
                                                linarith only [hlam, p5574_0]
                                      · linarith only [h5498, h5567, hlam]
                                    · linarith only [h5566, hlam, p5543_0]
                                  · have p5543_0 := h5543c.1
                                    have p5543_1 := h5543c.2.1
                                    have p5543_2 := h5543c.2.2.1
                                    have p5543_3 := h5543c.2.2.2
                                    linarith only [h0, h4610, h4616, h5097, h5496, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5512_1, p5543_1]
                                  · have p5543_0 := h5543c.1
                                    have p5543_1 := h5543c.2.1
                                    have p5543_2 := h5543c.2.2.1
                                    have p5543_3 := h5543c.2.2.2
                                    linarith only [hlam, p5543_0]
                                  · have p5543_0 := h5543c.1
                                    have p5543_1 := h5543c.2.1
                                    have p5543_2 := h5543c.2.2.1
                                    have p5543_3 := h5543c.2.2.2
                                    linarith only [h0, h4610, h4616, h5097, h5496, hlam, p5512_1, p5543_2]
                                  · have p5543_0 := h5543c.1
                                    have p5543_1 := h5543c.2.1
                                    have p5543_2 := h5543c.2.2.1
                                    have p5543_3 := h5543c.2.2.2
                                    linarith only [h0, h4612, h5498, h5509, hlam, p5512_1, p5543_2]
                                  · have p5543_0 := h5543c.1
                                    have p5543_1 := h5543c.2.1
                                    have p5543_2 := h5543c.2.2.1
                                    have p5543_3 := h5543c.2.2.2
                                    linarith only [h0, h4612, h5498, hlam, p5512_1, p5543_2]
                                  · have p5543_0 := h5543c.1
                                    have p5543_1 := h5543c.2.1
                                    have p5543_2 := h5543c.2.2.1
                                    have p5543_3 := h5543c.2.2.2
                                    linarith only [h4613, hlam, p5543_0]
                                  · have p5543_0 := h5543c.1
                                    have p5543_1 := h5543c.2.1
                                    have p5543_2 := h5543c.2.2.1
                                    have p5543_3 := h5543c.2.2.2
                                    linarith only [h5496, hlam, p5543_0]
                                  · have p5543_0 := h5543c.1
                                    have p5543_1 := h5543c.2.1
                                    have p5543_2 := h5543c.2.2.1
                                    have p5543_3 := h5543c.2.2.2
                                    linarith only [hlam, p5543_0]
                                  · have p5543_0 := h5543c.1
                                    have p5543_1 := h5543c.2.1
                                    have p5543_2 := h5543c.2.2.1
                                    have p5543_3 := h5543c.2.2.2
                                    linarith only [h5505, hlam, p5543_0]
                                  · have p5543_0 := h5543c.1
                                    have p5543_1 := h5543c.2.1
                                    have p5543_2 := h5543c.2.2.1
                                    have p5543_3 := h5543c.2.2.2
                                    linarith only [h5507, hlam, p5543_0]
                                  · have p5543_0 := h5543c.1
                                    have p5543_1 := h5543c.2.1
                                    have p5543_2 := h5543c.2.2.1
                                    have p5543_3 := h5543c.2.2.2
                                    linarith only [h4614, hlam, p5543_0]
                                  · have p5543_0 := h5543c.1
                                    have p5543_1 := h5543c.2.1
                                    have p5543_2 := h5543c.2.2.1
                                    have p5543_3 := h5543c.2.2.2
                                    linarith only [h5497, hlam, p5543_0]
                                  · have p5543_0 := h5543c.1
                                    have p5543_1 := h5543c.2.1
                                    have p5543_2 := h5543c.2.2.1
                                    have p5543_3 := h5543c.2.2.2
                                    linarith only [h4612, h5498, h5509, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5512_1, p5543_1, u0elo0]
                                  · have p5543_0 := h5543c.1
                                    have p5543_1 := h5543c.2.1
                                    have p5543_2 := h5543c.2.2.1
                                    have p5543_3 := h5543c.2.2.2
                                    linarith only [hlam, p5543_0]
                                  · have p5543_0 := h5543c.1
                                    have p5543_1 := h5543c.2.1
                                    have p5543_2 := h5543c.2.2.1
                                    have p5543_3 := h5543c.2.2.2
                                    linarith only [h5509, hlam, p5543_1]
                                  · have p5543_0 := h5543c.1
                                    have p5543_1 := h5543c.2.1
                                    have p5543_2 := h5543c.2.2.1
                                    have p5543_3 := h5543c.2.2.2
                                    linarith only [h4615, hlam, p5543_0]
                                  · have p5543_0 := h5543c.1
                                    have p5543_1 := h5543c.2.1
                                    have p5543_2 := h5543c.2.2.1
                                    have p5543_3 := h5543c.2.2.2
                                    linarith only [h5498, hlam, p5543_0]
                                  · have p5543_0 := h5543c.1
                                    have p5543_1 := h5543c.2.1
                                    have p5543_2 := h5543c.2.2.1
                                    have p5543_3 := h5543c.2.2.2
                                    linarith only [h0, h4612, h5498, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5512_1, p5543_1, u0elo1]
                                  · have p5543_0 := h5543c.1
                                    have p5543_1 := h5543c.2.1
                                    have p5543_2 := h5543c.2.2.1
                                    have p5543_3 := h5543c.2.2.2
                                    linarith only [h0, h4612, h5498, hc24, hlam, hphi, ht0b, ht45, ht5b, p5512_1, p5543_1, u0elo1]
                                  · have p5543_0 := h5543c.1
                                    have p5543_1 := h5543c.2.1
                                    have p5543_2 := h5543c.2.2.1
                                    have p5543_3 := h5543c.2.2.2
                                    linarith only [hlam, p5543_0]
                          · linarith only [h4615, h5536, hlam]
                        · linarith only [h4612, h5535, hlam]
                      · have p5512_0 := h5512c.1
                        have p5512_1 := h5512c.2.1
                        have p5512_2 := h5512c.2.2.1
                        have p5512_3 := h5512c.2.2.2
                        linarith only [h4610, h5496, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5512_1, u0elo1]
                      · have p5512_0 := h5512c.1
                        have p5512_1 := h5512c.2.1
                        have p5512_2 := h5512c.2.2.1
                        have p5512_3 := h5512c.2.2.2
                        linarith only [hlam, p5512_0]
                      · have p5512_0 := h5512c.1
                        have p5512_1 := h5512c.2.1
                        have p5512_2 := h5512c.2.2.1
                        have p5512_3 := h5512c.2.2.2
                        rcases p5512_3 (m.d 0 1) (by simp) with h5693 | h5693
                        · linarith only [h0, h5693, hlam]
                        · linarith only [h4610, h5693, hlam]
                      · have p5512_0 := h5512c.1
                        have p5512_1 := h5512c.2.1
                        have p5512_2 := h5512c.2.2.1
                        have p5512_3 := h5512c.2.2.2
                        rcases p5512_3 (m.d 0 1) (by simp) with h5696 | h5696
                        · linarith only [h0, h5696, hlam]
                        · linarith only [h4611, h5696, hlam]
                      · have p5512_0 := h5512c.1
                        have p5512_1 := h5512c.2.1
                        have p5512_2 := h5512c.2.2.1
                        have p5512_3 := h5512c.2.2.2
                        rcases p5512_3 (m.d 0 1) (by simp) with h5699 | h5699
                        · linarith only [h0, h5699, hlam]
                        · linarith only [h4612, h5699, hlam]
                      · have p5512_0 := h5512c.1
                        have p5512_1 := h5512c.2.1
                        have p5512_2 := h5512c.2.2.1
                        have p5512_3 := h5512c.2.2.2
                        linarith only [h4610, hlam, p5512_1]
                      · have p5512_0 := h5512c.1
                        have p5512_1 := h5512c.2.1
                        have p5512_2 := h5512c.2.2.1
                        have p5512_3 := h5512c.2.2.2
                        linarith only [h4613, hlam, p5512_1]
                      · have p5512_0 := h5512c.1
                        have p5512_1 := h5512c.2.1
                        have p5512_2 := h5512c.2.2.1
                        have p5512_3 := h5512c.2.2.2
                        linarith only [hlam, p5512_0]
                      · have p5512_0 := h5512c.1
                        have p5512_1 := h5512c.2.1
                        have p5512_2 := h5512c.2.2.1
                        have p5512_3 := h5512c.2.2.2
                        linarith only [h4616, hlam, p5512_1]
                      · have p5512_0 := h5512c.1
                        have p5512_1 := h5512c.2.1
                        have p5512_2 := h5512c.2.2.1
                        have p5512_3 := h5512c.2.2.2
                        linarith only [h4989, hlam, p5512_1]
                      · have p5512_0 := h5512c.1
                        have p5512_1 := h5512c.2.1
                        have p5512_2 := h5512c.2.2.1
                        have p5512_3 := h5512c.2.2.2
                        linarith only [h4611, hlam, p5512_0]
                      · have p5512_0 := h5512c.1
                        have p5512_1 := h5512c.2.1
                        have p5512_2 := h5512c.2.2.1
                        have p5512_3 := h5512c.2.2.2
                        linarith only [h4614, hlam, p5512_0]
                      · have p5512_0 := h5512c.1
                        have p5512_1 := h5512c.2.1
                        have p5512_2 := h5512c.2.2.1
                        have p5512_3 := h5512c.2.2.2
                        linarith only [h4610, h5097, h5496, h5511, hc23, hc34, hlam, hphi, p5512_1]
                      · have p5512_0 := h5512c.1
                        have p5512_1 := h5512c.2.1
                        have p5512_2 := h5512c.2.2.1
                        have p5512_3 := h5512c.2.2.2
                        linarith only [hlam, p5512_0]
                      · have p5512_0 := h5512c.1
                        have p5512_1 := h5512c.2.1
                        have p5512_2 := h5512c.2.2.1
                        have p5512_3 := h5512c.2.2.2
                        linarith only [h5097, hlam, p5512_0]
                      · have p5512_0 := h5512c.1
                        have p5512_1 := h5512c.2.1
                        have p5512_2 := h5512c.2.2.1
                        have p5512_3 := h5512c.2.2.2
                        linarith only [h4612, hlam, p5512_0]
                      · have p5512_0 := h5512c.1
                        have p5512_1 := h5512c.2.1
                        have p5512_2 := h5512c.2.2.1
                        have p5512_3 := h5512c.2.2.2
                        linarith only [h4615, hlam, p5512_1]
                      · have p5512_0 := h5512c.1
                        have p5512_1 := h5512c.2.1
                        have p5512_2 := h5512c.2.2.1
                        have p5512_3 := h5512c.2.2.2
                        linarith only [h4610, h5097, h5496, h5511, hc23, hc34, hlam, hphi, p5512_1]
                      · have p5512_0 := h5512c.1
                        have p5512_1 := h5512c.2.1
                        have p5512_2 := h5512c.2.2.1
                        have p5512_3 := h5512c.2.2.2
                        linarith only [h4611, h5097, h5496, h5499, h5511, hc23, hc34, hlam, hphi, p5512_1]
                      · have p5512_0 := h5512c.1
                        have p5512_1 := h5512c.2.1
                        have p5512_2 := h5512c.2.2.1
                        have p5512_3 := h5512c.2.2.2
                        linarith only [hlam, p5512_0]
                    · rcases h0bigk with h5717c | h5717c | h5717c | h5717c | h5717c | h5717c | h5717c | h5717c | h5717c | h5717c | h5717c | h5717c | h5717c | h5717c | h5717c | h5717c | h5717c | h5717c | h5717c | h5717c | h5717c | h5717c | h5717c | h5717c | h5717c
                      · have p5717_0 := h5717c.1
                        have p5717_1 := h5717c.2.1
                        have p5717_2 := h5717c.2.2.1
                        have p5717_3 := h5717c.2.2.2
                        linarith only [hlam, p5717_0]
                      · have p5717_0 := h5717c.1
                        have p5717_1 := h5717c.2.1
                        have p5717_2 := h5717c.2.2.1
                        have p5717_3 := h5717c.2.2.2
                        linarith only [h0, hlam, p5717_1]
                      · have p5717_0 := h5717c.1
                        have p5717_1 := h5717c.2.1
                        have p5717_2 := h5717c.2.2.1
                        have p5717_3 := h5717c.2.2.2
                        rcases p5717_3 (m.d 0 1) (by simp) with h5720 | h5720
                        · rcases p5717_3 (m.d 0 2) (by simp) with h5721 | h5721
                          · rcases p5717_3 (m.d 0 3) (by simp) with h5722 | h5722
                            · linarith only [h4610, h5722, hlam]
                            · rcases p5717_3 (m.d 0 4) (by simp) with h5724 | h5724
                              · linarith only [h4611, h5724, hlam]
                              · linarith only [h4616, h5724, hlam]
                          · linarith only [h4613, h5721, hlam]
                        · linarith only [h4610, h5720, hlam]
                      · have p5717_0 := h5717c.1
                        have p5717_1 := h5717c.2.1
                        have p5717_2 := h5717c.2.2.1
                        have p5717_3 := h5717c.2.2.2
                        rcases p5717_3 (m.d 0 1) (by simp) with h5729 | h5729
                        · rcases p5717_3 (m.d 0 2) (by simp) with h5730 | h5730
                          · rcases p5717_3 (m.d 0 3) (by simp) with h5731 | h5731
                            · linarith only [h4610, h5731, hlam]
                            · rcases p5717_3 (m.d 0 4) (by simp) with h5733 | h5733
                              · linarith only [h4611, h5733, hlam]
                              · rcases p5717_3 (m.d 0 5) (by simp) with h5735 | h5735
                                · linarith only [h4612, h5735, hlam]
                                · linarith only [h5097, h5735, hlam]
                          · linarith only [h4614, h5730, hlam]
                        · linarith only [h4611, h5729, hlam]
                      · have p5717_0 := h5717c.1
                        have p5717_1 := h5717c.2.1
                        have p5717_2 := h5717c.2.2.1
                        have p5717_3 := h5717c.2.2.2
                        rcases p5717_3 (m.d 0 1) (by simp) with h5740 | h5740
                        · rcases p5717_3 (m.d 0 2) (by simp) with h5741 | h5741
                          · rcases p5717_3 (m.d 0 3) (by simp) with h5742 | h5742
                            · linarith only [h4610, h5742, hlam]
                            · rcases p5717_3 (m.d 0 4) (by simp) with h5744 | h5744
                              · linarith only [h4611, h5744, hlam]
                              · rcases p5717_3 (m.d 0 5) (by simp) with h5746 | h5746
                                · linarith only [h4612, h5746, hlam]
                                · rcases h2bigk with h5748c | h5748c | h5748c | h5748c | h5748c | h5748c | h5748c | h5748c | h5748c | h5748c | h5748c | h5748c | h5748c | h5748c | h5748c | h5748c | h5748c | h5748c | h5748c | h5748c | h5748c | h5748c | h5748c | h5748c | h5748c
                                  · have p5748_0 := h5748c.1
                                    have p5748_1 := h5748c.2.1
                                    have p5748_2 := h5748c.2.2.1
                                    have p5748_3 := h5748c.2.2.2
                                    linarith only [hlam, p5748_0]
                                  · have p5748_0 := h5748c.1
                                    have p5748_1 := h5748c.2.1
                                    have p5748_2 := h5748c.2.2.1
                                    have p5748_3 := h5748c.2.2.2
                                    linarith only [h0, hlam, p5748_1]
                                  · have p5748_0 := h5748c.1
                                    have p5748_1 := h5748c.2.1
                                    have p5748_2 := h5748c.2.2.1
                                    have p5748_3 := h5748c.2.2.2
                                    rcases p5748_3 (m.d 0 2) (by simp) with h5751 | h5751
                                    · rcases p5748_3 (m.d 1 2) (by simp) with h5752 | h5752
                                      · rcases p5748_3 (m.d 2 3) (by simp) with h5753 | h5753
                                        · linarith only [h5753, hlam, p5748_0]
                                        · rcases p5748_3 (m.d 2 4) (by simp) with h5755 | h5755
                                          · linarith only [h4614, h5755, hlam]
                                          · linarith only [h5505, h5755, hlam]
                                      · linarith only [h5496, h5752, hlam]
                                    · linarith only [h5751, hlam, p5748_0]
                                  · have p5748_0 := h5748c.1
                                    have p5748_1 := h5748c.2.1
                                    have p5748_2 := h5748c.2.2.1
                                    have p5748_3 := h5748c.2.2.2
                                    rcases p5748_3 (m.d 0 2) (by simp) with h5760 | h5760
                                    · rcases p5748_3 (m.d 1 2) (by simp) with h5761 | h5761
                                      · rcases p5748_3 (m.d 2 3) (by simp) with h5762 | h5762
                                        · linarith only [h4613, h5762, hlam]
                                        · rcases p5748_3 (m.d 2 4) (by simp) with h5764 | h5764
                                          · linarith only [h5764, hlam, p5748_0]
                                          · rcases p5748_3 (m.d 2 5) (by simp) with h5766 | h5766
                                            · linarith only [h4615, h5766, hlam]
                                            · linarith only [h5509, h5766, hlam]
                                      · linarith only [h5497, h5761, hlam]
                                    · linarith only [h5760, hlam, p5748_0]
                                  · have p5748_0 := h5748c.1
                                    have p5748_1 := h5748c.2.1
                                    have p5748_2 := h5748c.2.2.1
                                    have p5748_3 := h5748c.2.2.2
                                    rcases p5748_3 (m.d 0 2) (by simp) with h5771 | h5771
                                    · rcases p5748_3 (m.d 1 2) (by simp) with h5772 | h5772
                                      · rcases p5748_3 (m.d 2 3) (by simp) with h5773 | h5773
                                        · linarith only [h4613, h5773, hlam]
                                        · rcases p5748_3 (m.d 2 4) (by simp) with h5775 | h5775
                                          · linarith only [h4614, h5775, hlam]
                                          · rcases p5748_3 (m.d 2 5) (by simp) with h5777 | h5777
                                            · linarith only [h5777, hlam, p5748_0]
                                            · rcases h3bigk with h5779c | h5779c | h5779c | h5779c | h5779c | h5779c | h5779c | h5779c | h5779c | h5779c | h5779c | h5779c | h5779c | h5779c | h5779c | h5779c | h5779c | h5779c | h5779c | h5779c | h5779c | h5779c | h5779c | h5779c | h5779c
                                              · have p5779_0 := h5779c.1
                                                have p5779_1 := h5779c.2.1
                                                have p5779_2 := h5779c.2.2.1
                                                have p5779_3 := h5779c.2.2.2
                                                linarith only [hlam, p5779_0]
                                              · have p5779_0 := h5779c.1
                                                have p5779_1 := h5779c.2.1
                                                have p5779_2 := h5779c.2.2.1
                                                have p5779_3 := h5779c.2.2.2
                                                linarith only [h4616, h5496, h5511, hc23, hc45, hlam, hphi, ht34, p5779_1]
                                              · have p5779_0 := h5779c.1
                                                have p5779_1 := h5779c.2.1
                                                have p5779_2 := h5779c.2.2.1
                                                have p5779_3 := h5779c.2.2.2
                                                linarith only [h4616, h5511, hc23, hc45, hlam, hphi, ht34, p5779_1]
                                              · have p5779_0 := h5779c.1
                                                have p5779_1 := h5779c.2.1
                                                have p5779_2 := h5779c.2.2.1
                                                have p5779_3 := h5779c.2.2.2
                                                linarith only [h4616, hlam, p5779_0]
                                              · have p5779_0 := h5779c.1
                                                have p5779_1 := h5779c.2.1
                                                have p5779_2 := h5779c.2.2.1
                                                have p5779_3 := h5779c.2.2.2
                                                linarith only [h4989, hlam, p5779_0]
                                              · have p5779_0 := h5779c.1
                                                have p5779_1 := h5779c.2.1
                                                have p5779_2 := h5779c.2.2.1
                                                have p5779_3 := h5779c.2.2.2
                                                linarith only [h4610, hlam, p5779_0]
                                              · have p5779_0 := h5779c.1
                                                have p5779_1 := h5779c.2.1
                                                have p5779_2 := h5779c.2.2.1
                                                have p5779_3 := h5779c.2.2.2
                                                linarith only [hlam, p5779_0]
                                              · have p5779_0 := h5779c.1
                                                have p5779_1 := h5779c.2.1
                                                have p5779_2 := h5779c.2.2.1
                                                have p5779_3 := h5779c.2.2.2
                                                linarith only [h4612, h5499, h5503, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5717_1, p5779_1, u0elo0]
                                              · have p5779_0 := h5779c.1
                                                have p5779_1 := h5779c.2.1
                                                have p5779_2 := h5779c.2.2.1
                                                have p5779_3 := h5779c.2.2.2
                                                linarith only [h5499, hlam, p5779_0]
                                              · have p5779_0 := h5779c.1
                                                have p5779_1 := h5779c.2.1
                                                have p5779_2 := h5779c.2.2.1
                                                have p5779_3 := h5779c.2.2.2
                                                linarith only [h5501, hlam, p5779_0]
                                              · have p5779_0 := h5779c.1
                                                have p5779_1 := h5779c.2.1
                                                have p5779_2 := h5779c.2.2.1
                                                have p5779_3 := h5779c.2.2.2
                                                linarith only [h4613, hlam, p5779_0]
                                              · have p5779_0 := h5779c.1
                                                have p5779_1 := h5779c.2.1
                                                have p5779_2 := h5779c.2.2.1
                                                have p5779_3 := h5779c.2.2.2
                                                linarith only [h5496, hlam, p5779_0]
                                              · have p5779_0 := h5779c.1
                                                have p5779_1 := h5779c.2.1
                                                have p5779_2 := h5779c.2.2.1
                                                have p5779_3 := h5779c.2.2.2
                                                linarith only [hlam, p5779_0]
                                              · have p5779_0 := h5779c.1
                                                have p5779_1 := h5779c.2.1
                                                have p5779_2 := h5779c.2.2.1
                                                have p5779_3 := h5779c.2.2.2
                                                linarith only [h5505, hlam, p5779_0]
                                              · have p5779_0 := h5779c.1
                                                have p5779_1 := h5779c.2.1
                                                have p5779_2 := h5779c.2.2.1
                                                have p5779_3 := h5779c.2.2.2
                                                linarith only [h5507, hlam, p5779_0]
                                              · have p5779_0 := h5779c.1
                                                have p5779_1 := h5779c.2.1
                                                have p5779_2 := h5779c.2.2.1
                                                have p5779_3 := h5779c.2.2.2
                                                linarith only [h5511, hc03, hc45, hlam, hphi, ht34, p5779_1]
                                              · have p5779_0 := h5779c.1
                                                have p5779_1 := h5779c.2.1
                                                have p5779_2 := h5779c.2.2.1
                                                have p5779_3 := h5779c.2.2.2
                                                linarith only [h5496, h5511, hc23, hc45, hlam, hphi, ht34, p5779_1]
                                              · have p5779_0 := h5779c.1
                                                have p5779_1 := h5779c.2.1
                                                have p5779_2 := h5779c.2.2.1
                                                have p5779_3 := h5779c.2.2.2
                                                linarith only [h5511, hc23, hc45, hlam, hphi, ht34, p5779_1]
                                              · have p5779_0 := h5779c.1
                                                have p5779_1 := h5779c.2.1
                                                have p5779_2 := h5779c.2.2.1
                                                have p5779_3 := h5779c.2.2.2
                                                linarith only [hlam, p5779_0]
                                              · have p5779_0 := h5779c.1
                                                have p5779_1 := h5779c.2.1
                                                have p5779_2 := h5779c.2.2.1
                                                have p5779_3 := h5779c.2.2.2
                                                linarith only [h5511, hlam, p5779_1]
                                              · have p5779_0 := h5779c.1
                                                have p5779_1 := h5779c.2.1
                                                have p5779_2 := h5779c.2.2.1
                                                have p5779_3 := h5779c.2.2.2
                                                rcases p5779_3 (m.d 0 3) (by simp) with h5800 | h5800
                                                · linarith only [h5800, hlam, p5779_0]
                                                · rcases p5779_3 (m.d 1 3) (by simp) with h5802 | h5802
                                                  · linarith only [h5501, h5802, hlam]
                                                  · rcases p5779_3 (m.d 2 3) (by simp) with h5804 | h5804
                                                    · linarith only [h5507, h5804, hlam]
                                                    · rcases p5779_3 (m.d 3 4) (by simp) with h5806 | h5806
                                                      · linarith only [h5511, h5806, hlam]
                                                      · linarith only [h4616, h5806, hlam]
                                              · have p5779_0 := h5779c.1
                                                have p5779_1 := h5779c.2.1
                                                have p5779_2 := h5779c.2.2.1
                                                have p5779_3 := h5779c.2.2.2
                                                rcases p5779_3 (m.d 0 3) (by simp) with h5809 | h5809
                                                · linarith only [h4989, h5809, hlam]
                                                · linarith only [h4610, h5809, hlam]
                                              · have p5779_0 := h5779c.1
                                                have p5779_1 := h5779c.2.1
                                                have p5779_2 := h5779c.2.2.1
                                                have p5779_3 := h5779c.2.2.2
                                                rcases p5779_3 (m.d 0 3) (by simp) with h5812 | h5812
                                                · linarith only [h4989, h5812, hlam]
                                                · linarith only [h4613, h5812, hlam]
                                              · have p5779_0 := h5779c.1
                                                have p5779_1 := h5779c.2.1
                                                have p5779_2 := h5779c.2.2.1
                                                have p5779_3 := h5779c.2.2.2
                                                linarith only [h4610, h4616, h5496, h5511, hc23, hc45, hlam, hphi, ht34, p5779_1]
                                              · have p5779_0 := h5779c.1
                                                have p5779_1 := h5779c.2.1
                                                have p5779_2 := h5779c.2.2.1
                                                have p5779_3 := h5779c.2.2.2
                                                linarith only [hlam, p5779_0]
                                      · linarith only [h5498, h5772, hlam]
                                    · linarith only [h5771, hlam, p5748_0]
                                  · have p5748_0 := h5748c.1
                                    have p5748_1 := h5748c.2.1
                                    have p5748_2 := h5748c.2.2.1
                                    have p5748_3 := h5748c.2.2.2
                                    linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p5717_1, p5748_1]
                                  · have p5748_0 := h5748c.1
                                    have p5748_1 := h5748c.2.1
                                    have p5748_2 := h5748c.2.2.1
                                    have p5748_3 := h5748c.2.2.2
                                    linarith only [hlam, p5748_0]
                                  · have p5748_0 := h5748c.1
                                    have p5748_1 := h5748c.2.1
                                    have p5748_2 := h5748c.2.2.1
                                    have p5748_3 := h5748c.2.2.2
                                    linarith only [h0, h4610, h4616, h5097, h5496, hlam, p5717_1, p5748_2]
                                  · have p5748_0 := h5748c.1
                                    have p5748_1 := h5748c.2.1
                                    have p5748_2 := h5748c.2.2.1
                                    have p5748_3 := h5748c.2.2.2
                                    linarith only [h0, h4614, h5097, hlam, p5717_1, p5748_2]
                                  · have p5748_0 := h5748c.1
                                    have p5748_1 := h5748c.2.1
                                    have p5748_2 := h5748c.2.2.1
                                    have p5748_3 := h5748c.2.2.2
                                    linarith only [h0, h4615, hlam, p5717_1, p5748_2]
                                  · have p5748_0 := h5748c.1
                                    have p5748_1 := h5748c.2.1
                                    have p5748_2 := h5748c.2.2.1
                                    have p5748_3 := h5748c.2.2.2
                                    linarith only [h4613, hlam, p5748_0]
                                  · have p5748_0 := h5748c.1
                                    have p5748_1 := h5748c.2.1
                                    have p5748_2 := h5748c.2.2.1
                                    have p5748_3 := h5748c.2.2.2
                                    linarith only [h5496, hlam, p5748_0]
                                  · have p5748_0 := h5748c.1
                                    have p5748_1 := h5748c.2.1
                                    have p5748_2 := h5748c.2.2.1
                                    have p5748_3 := h5748c.2.2.2
                                    linarith only [hlam, p5748_0]
                                  · have p5748_0 := h5748c.1
                                    have p5748_1 := h5748c.2.1
                                    have p5748_2 := h5748c.2.2.1
                                    have p5748_3 := h5748c.2.2.2
                                    linarith only [h5505, hlam, p5748_0]
                                  · have p5748_0 := h5748c.1
                                    have p5748_1 := h5748c.2.1
                                    have p5748_2 := h5748c.2.2.1
                                    have p5748_3 := h5748c.2.2.2
                                    linarith only [h5507, hlam, p5748_0]
                                  · have p5748_0 := h5748c.1
                                    have p5748_1 := h5748c.2.1
                                    have p5748_2 := h5748c.2.2.1
                                    have p5748_3 := h5748c.2.2.2
                                    linarith only [h4614, hlam, p5748_0]
                                  · have p5748_0 := h5748c.1
                                    have p5748_1 := h5748c.2.1
                                    have p5748_2 := h5748c.2.2.1
                                    have p5748_3 := h5748c.2.2.2
                                    linarith only [h5497, hlam, p5748_0]
                                  · have p5748_0 := h5748c.1
                                    have p5748_1 := h5748c.2.1
                                    have p5748_2 := h5748c.2.2.1
                                    have p5748_3 := h5748c.2.2.2
                                    linarith only [h4614, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5748_1, u0elo1]
                                  · have p5748_0 := h5748c.1
                                    have p5748_1 := h5748c.2.1
                                    have p5748_2 := h5748c.2.2.1
                                    have p5748_3 := h5748c.2.2.2
                                    linarith only [hlam, p5748_0]
                                  · have p5748_0 := h5748c.1
                                    have p5748_1 := h5748c.2.1
                                    have p5748_2 := h5748c.2.2.1
                                    have p5748_3 := h5748c.2.2.2
                                    linarith only [h5509, hlam, p5748_1]
                                  · have p5748_0 := h5748c.1
                                    have p5748_1 := h5748c.2.1
                                    have p5748_2 := h5748c.2.2.1
                                    have p5748_3 := h5748c.2.2.2
                                    linarith only [h4615, hlam, p5748_0]
                                  · have p5748_0 := h5748c.1
                                    have p5748_1 := h5748c.2.1
                                    have p5748_2 := h5748c.2.2.1
                                    have p5748_3 := h5748c.2.2.2
                                    linarith only [h5498, hlam, p5748_0]
                                  · have p5748_0 := h5748c.1
                                    have p5748_1 := h5748c.2.1
                                    have p5748_2 := h5748c.2.2.1
                                    have p5748_3 := h5748c.2.2.2
                                    linarith only [h4612, h5498, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5748_1, u0elo0]
                                  · have p5748_0 := h5748c.1
                                    have p5748_1 := h5748c.2.1
                                    have p5748_2 := h5748c.2.2.1
                                    have p5748_3 := h5748c.2.2.2
                                    linarith only [h0, h4612, h5498, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p5717_1, p5748_1]
                                  · have p5748_0 := h5748c.1
                                    have p5748_1 := h5748c.2.1
                                    have p5748_2 := h5748c.2.2.1
                                    have p5748_3 := h5748c.2.2.2
                                    linarith only [hlam, p5748_0]
                          · linarith only [h4615, h5741, hlam]
                        · linarith only [h4612, h5740, hlam]
                      · have p5717_0 := h5717c.1
                        have p5717_1 := h5717c.2.1
                        have p5717_2 := h5717c.2.2.1
                        have p5717_3 := h5717c.2.2.2
                        linarith only [h4610, h5496, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5717_1, u0elo1]
                      · have p5717_0 := h5717c.1
                        have p5717_1 := h5717c.2.1
                        have p5717_2 := h5717c.2.2.1
                        have p5717_3 := h5717c.2.2.2
                        linarith only [hlam, p5717_0]
                      · have p5717_0 := h5717c.1
                        have p5717_1 := h5717c.2.1
                        have p5717_2 := h5717c.2.2.1
                        have p5717_3 := h5717c.2.2.2
                        rcases p5717_3 (m.d 0 1) (by simp) with h5843 | h5843
                        · linarith only [h0, h5843, hlam]
                        · linarith only [h4610, h5843, hlam]
                      · have p5717_0 := h5717c.1
                        have p5717_1 := h5717c.2.1
                        have p5717_2 := h5717c.2.2.1
                        have p5717_3 := h5717c.2.2.2
                        rcases p5717_3 (m.d 0 1) (by simp) with h5846 | h5846
                        · linarith only [h0, h5846, hlam]
                        · linarith only [h4611, h5846, hlam]
                      · have p5717_0 := h5717c.1
                        have p5717_1 := h5717c.2.1
                        have p5717_2 := h5717c.2.2.1
                        have p5717_3 := h5717c.2.2.2
                        rcases p5717_3 (m.d 0 1) (by simp) with h5849 | h5849
                        · linarith only [h0, h5849, hlam]
                        · linarith only [h4612, h5849, hlam]
                      · have p5717_0 := h5717c.1
                        have p5717_1 := h5717c.2.1
                        have p5717_2 := h5717c.2.2.1
                        have p5717_3 := h5717c.2.2.2
                        linarith only [h4610, hlam, p5717_1]
                      · have p5717_0 := h5717c.1
                        have p5717_1 := h5717c.2.1
                        have p5717_2 := h5717c.2.2.1
                        have p5717_3 := h5717c.2.2.2
                        linarith only [h4613, hlam, p5717_1]
                      · have p5717_0 := h5717c.1
                        have p5717_1 := h5717c.2.1
                        have p5717_2 := h5717c.2.2.1
                        have p5717_3 := h5717c.2.2.2
                        linarith only [hlam, p5717_0]
                      · have p5717_0 := h5717c.1
                        have p5717_1 := h5717c.2.1
                        have p5717_2 := h5717c.2.2.1
                        have p5717_3 := h5717c.2.2.2
                        linarith only [h4616, hlam, p5717_1]
                      · have p5717_0 := h5717c.1
                        have p5717_1 := h5717c.2.1
                        have p5717_2 := h5717c.2.2.1
                        have p5717_3 := h5717c.2.2.2
                        linarith only [h4989, hlam, p5717_1]
                      · have p5717_0 := h5717c.1
                        have p5717_1 := h5717c.2.1
                        have p5717_2 := h5717c.2.2.1
                        have p5717_3 := h5717c.2.2.2
                        linarith only [h4611, hlam, p5717_0]
                      · have p5717_0 := h5717c.1
                        have p5717_1 := h5717c.2.1
                        have p5717_2 := h5717c.2.2.1
                        have p5717_3 := h5717c.2.2.2
                        linarith only [h4614, hlam, p5717_0]
                      · have p5717_0 := h5717c.1
                        have p5717_1 := h5717c.2.1
                        have p5717_2 := h5717c.2.2.1
                        have p5717_3 := h5717c.2.2.2
                        linarith only [h4610, h5097, h5496, hc23, hc45, hlam, hphi, ht34, p5717_1]
                      · have p5717_0 := h5717c.1
                        have p5717_1 := h5717c.2.1
                        have p5717_2 := h5717c.2.2.1
                        have p5717_3 := h5717c.2.2.2
                        linarith only [hlam, p5717_0]
                      · have p5717_0 := h5717c.1
                        have p5717_1 := h5717c.2.1
                        have p5717_2 := h5717c.2.2.1
                        have p5717_3 := h5717c.2.2.2
                        linarith only [h5097, hlam, p5717_0]
                      · have p5717_0 := h5717c.1
                        have p5717_1 := h5717c.2.1
                        have p5717_2 := h5717c.2.2.1
                        have p5717_3 := h5717c.2.2.2
                        linarith only [h4612, hlam, p5717_0]
                      · have p5717_0 := h5717c.1
                        have p5717_1 := h5717c.2.1
                        have p5717_2 := h5717c.2.2.1
                        have p5717_3 := h5717c.2.2.2
                        linarith only [h4615, hlam, p5717_1]
                      · have p5717_0 := h5717c.1
                        have p5717_1 := h5717c.2.1
                        have p5717_2 := h5717c.2.2.1
                        have p5717_3 := h5717c.2.2.2
                        rcases p5717_3 (m.d 0 1) (by simp) with h5864 | h5864
                        · rcases p5717_3 (m.d 0 2) (by simp) with h5865 | h5865
                          · rcases p5717_3 (m.d 0 3) (by simp) with h5866 | h5866
                            · linarith only [h4989, h5866, hlam]
                            · rcases p5717_3 (m.d 0 4) (by simp) with h5868 | h5868
                              · linarith only [h5097, h5868, hlam]
                              · linarith only [h4616, h5868, hlam]
                          · linarith only [h4613, h5865, hlam]
                        · linarith only [h4610, h5864, hlam]
                      · have p5717_0 := h5717c.1
                        have p5717_1 := h5717c.2.1
                        have p5717_2 := h5717c.2.2.1
                        have p5717_3 := h5717c.2.2.2
                        rcases p5717_3 (m.d 0 1) (by simp) with h5873 | h5873
                        · rcases p5717_3 (m.d 0 2) (by simp) with h5874 | h5874
                          · rcases p5717_3 (m.d 0 3) (by simp) with h5875 | h5875
                            · linarith only [h4989, h5875, hlam]
                            · rcases p5717_3 (m.d 0 4) (by simp) with h5877 | h5877
                              · linarith only [h5097, h5877, hlam]
                              · rcases p5717_3 (m.d 0 5) (by simp) with h5879 | h5879
                                · rcases h2bigk with h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c | h5880c
                                  · have p5880_0 := h5880c.1
                                    have p5880_1 := h5880c.2.1
                                    have p5880_2 := h5880c.2.2.1
                                    have p5880_3 := h5880c.2.2.2
                                    linarith only [hlam, p5880_0]
                                  · have p5880_0 := h5880c.1
                                    have p5880_1 := h5880c.2.1
                                    have p5880_2 := h5880c.2.2.1
                                    have p5880_3 := h5880c.2.2.2
                                    linarith only [h0, hlam, p5880_1]
                                  · have p5880_0 := h5880c.1
                                    have p5880_1 := h5880c.2.1
                                    have p5880_2 := h5880c.2.2.1
                                    have p5880_3 := h5880c.2.2.2
                                    rcases p5880_3 (m.d 0 2) (by simp) with h5883 | h5883
                                    · rcases p5880_3 (m.d 1 2) (by simp) with h5884 | h5884
                                      · rcases p5880_3 (m.d 2 3) (by simp) with h5885 | h5885
                                        · linarith only [h5885, hlam, p5880_0]
                                        · rcases p5880_3 (m.d 2 4) (by simp) with h5887 | h5887
                                          · linarith only [h4614, h5887, hlam]
                                          · linarith only [h5505, h5887, hlam]
                                      · linarith only [h5496, h5884, hlam]
                                    · linarith only [h5883, hlam, p5880_0]
                                  · have p5880_0 := h5880c.1
                                    have p5880_1 := h5880c.2.1
                                    have p5880_2 := h5880c.2.2.1
                                    have p5880_3 := h5880c.2.2.2
                                    rcases p5880_3 (m.d 0 2) (by simp) with h5892 | h5892
                                    · rcases p5880_3 (m.d 1 2) (by simp) with h5893 | h5893
                                      · rcases p5880_3 (m.d 2 3) (by simp) with h5894 | h5894
                                        · linarith only [h4613, h5894, hlam]
                                        · rcases p5880_3 (m.d 2 4) (by simp) with h5896 | h5896
                                          · linarith only [h5896, hlam, p5880_0]
                                          · rcases p5880_3 (m.d 2 5) (by simp) with h5898 | h5898
                                            · linarith only [h4615, h5898, hlam]
                                            · linarith only [h5509, h5898, hlam]
                                      · linarith only [h5497, h5893, hlam]
                                    · linarith only [h5892, hlam, p5880_0]
                                  · have p5880_0 := h5880c.1
                                    have p5880_1 := h5880c.2.1
                                    have p5880_2 := h5880c.2.2.1
                                    have p5880_3 := h5880c.2.2.2
                                    rcases p5880_3 (m.d 0 2) (by simp) with h5903 | h5903
                                    · rcases p5880_3 (m.d 1 2) (by simp) with h5904 | h5904
                                      · rcases p5880_3 (m.d 2 3) (by simp) with h5905 | h5905
                                        · linarith only [h4613, h5905, hlam]
                                        · rcases p5880_3 (m.d 2 4) (by simp) with h5907 | h5907
                                          · linarith only [h4614, h5907, hlam]
                                          · rcases p5880_3 (m.d 2 5) (by simp) with h5909 | h5909
                                            · linarith only [h5909, hlam, p5880_0]
                                            · rcases h3bigk with h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c
                                              · have p5911_0 := h5911c.1
                                                have p5911_1 := h5911c.2.1
                                                have p5911_2 := h5911c.2.2.1
                                                have p5911_3 := h5911c.2.2.2
                                                linarith only [hlam, p5911_0]
                                              · have p5911_0 := h5911c.1
                                                have p5911_1 := h5911c.2.1
                                                have p5911_2 := h5911c.2.2.1
                                                have p5911_3 := h5911c.2.2.2
                                                linarith only [h4616, h5496, h5511, hc23, hc45, hlam, hphi, ht34, p5911_1]
                                              · have p5911_0 := h5911c.1
                                                have p5911_1 := h5911c.2.1
                                                have p5911_2 := h5911c.2.2.1
                                                have p5911_3 := h5911c.2.2.2
                                                linarith only [h4616, h5511, hc23, hc45, hlam, hphi, ht34, p5911_1]
                                              · have p5911_0 := h5911c.1
                                                have p5911_1 := h5911c.2.1
                                                have p5911_2 := h5911c.2.2.1
                                                have p5911_3 := h5911c.2.2.2
                                                linarith only [h4616, hlam, p5911_0]
                                              · have p5911_0 := h5911c.1
                                                have p5911_1 := h5911c.2.1
                                                have p5911_2 := h5911c.2.2.1
                                                have p5911_3 := h5911c.2.2.2
                                                linarith only [h4989, hlam, p5911_0]
                                              · have p5911_0 := h5911c.1
                                                have p5911_1 := h5911c.2.1
                                                have p5911_2 := h5911c.2.2.1
                                                have p5911_3 := h5911c.2.2.2
                                                linarith only [h4610, hlam, p5911_0]
                                              · have p5911_0 := h5911c.1
                                                have p5911_1 := h5911c.2.1
                                                have p5911_2 := h5911c.2.2.1
                                                have p5911_3 := h5911c.2.2.2
                                                linarith only [hlam, p5911_0]
                                              · have p5911_0 := h5911c.1
                                                have p5911_1 := h5911c.2.1
                                                have p5911_2 := h5911c.2.2.1
                                                have p5911_3 := h5911c.2.2.2
                                                linarith only [h4611, h4612, h5499, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5717_1, p5911_1, u0elo0]
                                              · have p5911_0 := h5911c.1
                                                have p5911_1 := h5911c.2.1
                                                have p5911_2 := h5911c.2.2.1
                                                have p5911_3 := h5911c.2.2.2
                                                linarith only [h5499, hlam, p5911_0]
                                              · have p5911_0 := h5911c.1
                                                have p5911_1 := h5911c.2.1
                                                have p5911_2 := h5911c.2.2.1
                                                have p5911_3 := h5911c.2.2.2
                                                linarith only [h5501, hlam, p5911_0]
                                              · have p5911_0 := h5911c.1
                                                have p5911_1 := h5911c.2.1
                                                have p5911_2 := h5911c.2.2.1
                                                have p5911_3 := h5911c.2.2.2
                                                linarith only [h4613, hlam, p5911_0]
                                              · have p5911_0 := h5911c.1
                                                have p5911_1 := h5911c.2.1
                                                have p5911_2 := h5911c.2.2.1
                                                have p5911_3 := h5911c.2.2.2
                                                linarith only [h5496, hlam, p5911_0]
                                              · have p5911_0 := h5911c.1
                                                have p5911_1 := h5911c.2.1
                                                have p5911_2 := h5911c.2.2.1
                                                have p5911_3 := h5911c.2.2.2
                                                linarith only [hlam, p5911_0]
                                              · have p5911_0 := h5911c.1
                                                have p5911_1 := h5911c.2.1
                                                have p5911_2 := h5911c.2.2.1
                                                have p5911_3 := h5911c.2.2.2
                                                linarith only [h5505, hlam, p5911_0]
                                              · have p5911_0 := h5911c.1
                                                have p5911_1 := h5911c.2.1
                                                have p5911_2 := h5911c.2.2.1
                                                have p5911_3 := h5911c.2.2.2
                                                linarith only [h5507, hlam, p5911_0]
                                              · have p5911_0 := h5911c.1
                                                have p5911_1 := h5911c.2.1
                                                have p5911_2 := h5911c.2.2.1
                                                have p5911_3 := h5911c.2.2.2
                                                linarith only [h5511, hc03, hc45, hlam, hphi, ht34, p5911_1]
                                              · have p5911_0 := h5911c.1
                                                have p5911_1 := h5911c.2.1
                                                have p5911_2 := h5911c.2.2.1
                                                have p5911_3 := h5911c.2.2.2
                                                linarith only [h5496, h5511, hc23, hc45, hlam, hphi, ht34, p5911_1]
                                              · have p5911_0 := h5911c.1
                                                have p5911_1 := h5911c.2.1
                                                have p5911_2 := h5911c.2.2.1
                                                have p5911_3 := h5911c.2.2.2
                                                linarith only [h5511, hc23, hc45, hlam, hphi, ht34, p5911_1]
                                              · have p5911_0 := h5911c.1
                                                have p5911_1 := h5911c.2.1
                                                have p5911_2 := h5911c.2.2.1
                                                have p5911_3 := h5911c.2.2.2
                                                linarith only [hlam, p5911_0]
                                              · have p5911_0 := h5911c.1
                                                have p5911_1 := h5911c.2.1
                                                have p5911_2 := h5911c.2.2.1
                                                have p5911_3 := h5911c.2.2.2
                                                linarith only [h5511, hlam, p5911_1]
                                              · have p5911_0 := h5911c.1
                                                have p5911_1 := h5911c.2.1
                                                have p5911_2 := h5911c.2.2.1
                                                have p5911_3 := h5911c.2.2.2
                                                rcases p5911_3 (m.d 0 3) (by simp) with h5932 | h5932
                                                · linarith only [h5932, hlam, p5911_0]
                                                · rcases p5911_3 (m.d 1 3) (by simp) with h5934 | h5934
                                                  · linarith only [h5501, h5934, hlam]
                                                  · rcases p5911_3 (m.d 2 3) (by simp) with h5936 | h5936
                                                    · linarith only [h5507, h5936, hlam]
                                                    · rcases p5911_3 (m.d 3 4) (by simp) with h5938 | h5938
                                                      · linarith only [h5511, h5938, hlam]
                                                      · linarith only [h4616, h5938, hlam]
                                              · have p5911_0 := h5911c.1
                                                have p5911_1 := h5911c.2.1
                                                have p5911_2 := h5911c.2.2.1
                                                have p5911_3 := h5911c.2.2.2
                                                rcases p5911_3 (m.d 0 3) (by simp) with h5941 | h5941
                                                · linarith only [h4989, h5941, hlam]
                                                · linarith only [h4610, h5941, hlam]
                                              · have p5911_0 := h5911c.1
                                                have p5911_1 := h5911c.2.1
                                                have p5911_2 := h5911c.2.2.1
                                                have p5911_3 := h5911c.2.2.2
                                                rcases p5911_3 (m.d 0 3) (by simp) with h5944 | h5944
                                                · linarith only [h4989, h5944, hlam]
                                                · linarith only [h4613, h5944, hlam]
                                              · have p5911_0 := h5911c.1
                                                have p5911_1 := h5911c.2.1
                                                have p5911_2 := h5911c.2.2.1
                                                have p5911_3 := h5911c.2.2.2
                                                linarith only [h4610, h4616, h5496, h5511, hc23, hc45, hlam, hphi, ht34, p5911_1]
                                              · have p5911_0 := h5911c.1
                                                have p5911_1 := h5911c.2.1
                                                have p5911_2 := h5911c.2.2.1
                                                have p5911_3 := h5911c.2.2.2
                                                linarith only [hlam, p5911_0]
                                      · linarith only [h5498, h5904, hlam]
                                    · linarith only [h5903, hlam, p5880_0]
                                  · have p5880_0 := h5880c.1
                                    have p5880_1 := h5880c.2.1
                                    have p5880_2 := h5880c.2.2.1
                                    have p5880_3 := h5880c.2.2.2
                                    linarith only [h0, h4612, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5717_1, p5880_1]
                                  · have p5880_0 := h5880c.1
                                    have p5880_1 := h5880c.2.1
                                    have p5880_2 := h5880c.2.2.1
                                    have p5880_3 := h5880c.2.2.2
                                    linarith only [hlam, p5880_0]
                                  · have p5880_0 := h5880c.1
                                    have p5880_1 := h5880c.2.1
                                    have p5880_2 := h5880c.2.2.1
                                    have p5880_3 := h5880c.2.2.2
                                    linarith only [h0, h4610, h4612, h4616, h5496, hlam, p5717_1, p5880_2]
                                  · have p5880_0 := h5880c.1
                                    have p5880_1 := h5880c.2.1
                                    have p5880_2 := h5880c.2.2.1
                                    have p5880_3 := h5880c.2.2.2
                                    linarith only [h0, h4612, h4614, hlam, p5717_1, p5880_2]
                                  · have p5880_0 := h5880c.1
                                    have p5880_1 := h5880c.2.1
                                    have p5880_2 := h5880c.2.2.1
                                    have p5880_3 := h5880c.2.2.2
                                    rcases p5880_3 (m.d 0 2) (by simp) with h5955 | h5955
                                    · linarith only [h0, h5955, hlam]
                                    · linarith only [h4615, h5955, hlam]
                                  · have p5880_0 := h5880c.1
                                    have p5880_1 := h5880c.2.1
                                    have p5880_2 := h5880c.2.2.1
                                    have p5880_3 := h5880c.2.2.2
                                    linarith only [h4613, hlam, p5880_0]
                                  · have p5880_0 := h5880c.1
                                    have p5880_1 := h5880c.2.1
                                    have p5880_2 := h5880c.2.2.1
                                    have p5880_3 := h5880c.2.2.2
                                    linarith only [h5496, hlam, p5880_0]
                                  · have p5880_0 := h5880c.1
                                    have p5880_1 := h5880c.2.1
                                    have p5880_2 := h5880c.2.2.1
                                    have p5880_3 := h5880c.2.2.2
                                    linarith only [hlam, p5880_0]
                                  · have p5880_0 := h5880c.1
                                    have p5880_1 := h5880c.2.1
                                    have p5880_2 := h5880c.2.2.1
                                    have p5880_3 := h5880c.2.2.2
                                    linarith only [h5505, hlam, p5880_0]
                                  · have p5880_0 := h5880c.1
                                    have p5880_1 := h5880c.2.1
                                    have p5880_2 := h5880c.2.2.1
                                    have p5880_3 := h5880c.2.2.2
                                    linarith only [h5507, hlam, p5880_0]
                                  · have p5880_0 := h5880c.1
                                    have p5880_1 := h5880c.2.1
                                    have p5880_2 := h5880c.2.2.1
                                    have p5880_3 := h5880c.2.2.2
                                    linarith only [h4614, hlam, p5880_0]
                                  · have p5880_0 := h5880c.1
                                    have p5880_1 := h5880c.2.1
                                    have p5880_2 := h5880c.2.2.1
                                    have p5880_3 := h5880c.2.2.2
                                    linarith only [h5497, hlam, p5880_0]
                                  · have p5880_0 := h5880c.1
                                    have p5880_1 := h5880c.2.1
                                    have p5880_2 := h5880c.2.2.1
                                    have p5880_3 := h5880c.2.2.2
                                    linarith only [h4614, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5880_1, u0elo1]
                                  · have p5880_0 := h5880c.1
                                    have p5880_1 := h5880c.2.1
                                    have p5880_2 := h5880c.2.2.1
                                    have p5880_3 := h5880c.2.2.2
                                    linarith only [hlam, p5880_0]
                                  · have p5880_0 := h5880c.1
                                    have p5880_1 := h5880c.2.1
                                    have p5880_2 := h5880c.2.2.1
                                    have p5880_3 := h5880c.2.2.2
                                    linarith only [h5509, hlam, p5880_1]
                                  · have p5880_0 := h5880c.1
                                    have p5880_1 := h5880c.2.1
                                    have p5880_2 := h5880c.2.2.1
                                    have p5880_3 := h5880c.2.2.2
                                    linarith only [h4615, hlam, p5880_0]
                                  · have p5880_0 := h5880c.1
                                    have p5880_1 := h5880c.2.1
                                    have p5880_2 := h5880c.2.2.1
                                    have p5880_3 := h5880c.2.2.2
                                    linarith only [h5498, hlam, p5880_0]
                                  · have p5880_0 := h5880c.1
                                    have p5880_1 := h5880c.2.1
                                    have p5880_2 := h5880c.2.2.1
                                    have p5880_3 := h5880c.2.2.2
                                    linarith only [h4612, h5498, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5880_1, u0elo0]
                                  · have p5880_0 := h5880c.1
                                    have p5880_1 := h5880c.2.1
                                    have p5880_2 := h5880c.2.2.1
                                    have p5880_3 := h5880c.2.2.2
                                    linarith only [h0, h4612, h5498, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p5880_1]
                                  · have p5880_0 := h5880c.1
                                    have p5880_1 := h5880c.2.1
                                    have p5880_2 := h5880c.2.2.1
                                    have p5880_3 := h5880c.2.2.2
                                    linarith only [hlam, p5880_0]
                                · linarith only [h5097, h5879, hlam]
                          · linarith only [h4614, h5874, hlam]
                        · linarith only [h4611, h5873, hlam]
                      · have p5717_0 := h5717c.1
                        have p5717_1 := h5717c.2.1
                        have p5717_2 := h5717c.2.2.1
                        have p5717_3 := h5717c.2.2.2
                        linarith only [hlam, p5717_0]
      · linarith only [h0, h4615, h5498, hlam]
    · linarith only [h0, h4614, h5497, hlam]
  · linarith only [h0, h4613, h5496, hlam]

set_option maxHeartbeats 14754000 in
set_option maxHeartbeats 14754000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x0_x0_x0_x0_x0_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h4610 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h4611 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h4612 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4613 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4614 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4615 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4616 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4989 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 4 5 (by decide) (by decide) with h5097 | h5097
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x0_x0_x0_x0_x0_x0_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 h4610 h4611 h4612 h4613 h4614 h4615 h4616 h4989 h5097
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x0_x0_x0_x0_x0_x0_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 h4610 h4611 h4612 h4613 h4614 h4615 h4616 h4989 h5097

set_option maxHeartbeats 14754000 in
set_option maxHeartbeats 14754000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h4610 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h4611 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h4612 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4613 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4614 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4615 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4616 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 5 (by decide) (by decide) with h4989 | h4989
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x0_x0_x0_x0_x0_x0_x1_x0 m hb0 hb2 hb3 hb5 hg0 h4610 h4611 h4612 h4613 h4614 h4615 h4616 h4989
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x0_x0_x0_x0_x0_x0_x1_x1 m hb0 hb2 hb3 hb5 hg0 h4610 h4611 h4612 h4613 h4614 h4615 h4616 h4989

set_option maxHeartbeats 14754000 in
set_option maxHeartbeats 14754000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h4610 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h4611 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h4612 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4613 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4614 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4615 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 4 (by decide) (by decide) with h4616 | h4616
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 h4610 h4611 h4612 h4613 h4614 h4615 h4616
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 h4610 h4611 h4612 h4613 h4614 h4615 h4616

set_option maxHeartbeats 14754000 in
set_option maxHeartbeats 14754000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h4610 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h4611 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h4612 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4613 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4614 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4615 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  linarith only [h0, h4612, h4615, hlam]

set_option maxHeartbeats 14754000 in
set_option maxHeartbeats 14754000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h4610 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h4611 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h4612 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4613 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4614 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 5 (by decide) (by decide) with h4615 | h4615
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 h4610 h4611 h4612 h4613 h4614 h4615
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 h4610 h4611 h4612 h4613 h4614 h4615

set_option maxHeartbeats 14754000 in
set_option maxHeartbeats 14754000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h4610 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h4611 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h4612 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4613 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4614 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  linarith only [h0, h4611, h4614, hlam]

set_option maxHeartbeats 14754000 in
set_option maxHeartbeats 14754000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h4610 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h4611 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h4612 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4613 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 4 (by decide) (by decide) with h4614 | h4614
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 h4610 h4611 h4612 h4613 h4614
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 h4610 h4611 h4612 h4613 h4614

set_option maxHeartbeats 14754000 in
set_option maxHeartbeats 14754000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h4610 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h4611 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h4612 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4613 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  linarith only [h0, h4610, h4613, hlam]

set_option maxHeartbeats 14754000 in
set_option maxHeartbeats 14754000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h4610 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h4611 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h4612 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h4613 | h4613
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 h4610 h4611 h4612 h4613
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 h4610 h4611 h4612 h4613

set_option maxHeartbeats 14754000 in
set_option maxHeartbeats 14754000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h4610 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h4611 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h4612 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h5983 | h5983
  · rcases m.htr 0 2 4 (by decide) (by decide) with h5984 | h5984
    · rcases m.htr 0 2 5 (by decide) (by decide) with h5985 | h5985
      · rcases m.htr 0 3 4 (by decide) (by decide) with h5986 | h5986
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5987 | h5987
          · linarith only [h4610, h4612, h5987, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5989 | h5989
            · linarith only [h4610, h4612, h5986, h5989, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5991 | h5991
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5992 | h5992
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5993 | h5993
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5994 | h5994
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5995 | h5995
                      · linarith only [h4610, h5987, h5995, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h5997 | h5997
                        · linarith only [h4610, h4611, h4612, h5989, h5994, h5997, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                        · linarith only [h4610, h4612, h5994, h5997, hc34, hc45, hlam, hphi]
                    · linarith only [h5986, h5987, h5994, hc13, hc35, hlam, hphi]
                  · linarith only [h0, h4610, h5985, h5986, h5993, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · linarith only [h0, h5984, h5992, hlam]
              · linarith only [h0, h5983, h5991, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h6004 | h6004
          · linarith only [h4611, h4612, h5986, h6004, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6006 | h6006
            · linarith only [h4611, h4612, h6006, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6008 | h6008
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6009 | h6009
                · rcases m.htr 1 2 5 (by decide) (by decide) with h6010 | h6010
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6011 | h6011
                    · linarith only [h4610, h5986, h6011, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h6013 | h6013
                      · linarith only [h4610, h4612, h6004, h6013, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h6015 | h6015
                        · linarith only [h4611, h5986, h6006, h6015, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6017 | h6017
                          · linarith only [h4610, h5986, h6008, h6017, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6019 | h6019
                            · linarith only [h4610, h6004, h6008, h6019, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6021 | h6021
                              · linarith only [h4610, h4612, h5984, h6008, h6015, h6021, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6023 | h6023
                                · linarith only [h4611, h4612, h6008, h6011, h6015, h6023, hc23, hc34, hlam, hphi]
                                · rcases h0bigk with h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c
                                  · have p6025_0 := h6025c.1
                                    have p6025_1 := h6025c.2.1
                                    have p6025_2 := h6025c.2.2.1
                                    have p6025_3 := h6025c.2.2.2
                                    linarith only [hlam, p6025_0]
                                  · have p6025_0 := h6025c.1
                                    have p6025_1 := h6025c.2.1
                                    have p6025_2 := h6025c.2.2.1
                                    have p6025_3 := h6025c.2.2.2
                                    linarith only [h0, hlam, p6025_1]
                                  · have p6025_0 := h6025c.1
                                    have p6025_1 := h6025c.2.1
                                    have p6025_2 := h6025c.2.2.1
                                    have p6025_3 := h6025c.2.2.2
                                    linarith only [h4612, h6013, hc03, hc35, hlam, hphi, p6025_1]
                                  · have p6025_0 := h6025c.1
                                    have p6025_1 := h6025c.2.1
                                    have p6025_2 := h6025c.2.2.1
                                    have p6025_3 := h6025c.2.2.2
                                    linarith only [h4612, h6013, h6023, hc04, hc45, hlam, hphi, p6025_1]
                                  · have p6025_0 := h6025c.1
                                    have p6025_1 := h6025c.2.1
                                    have p6025_2 := h6025c.2.2.1
                                    have p6025_3 := h6025c.2.2.2
                                    linarith only [h4612, hlam, p6025_1]
                                  · have p6025_0 := h6025c.1
                                    have p6025_1 := h6025c.2.1
                                    have p6025_2 := h6025c.2.2.1
                                    have p6025_3 := h6025c.2.2.2
                                    linarith only [h4610, h6008, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6025_1, u0elo1]
                                  · have p6025_0 := h6025c.1
                                    have p6025_1 := h6025c.2.1
                                    have p6025_2 := h6025c.2.2.1
                                    have p6025_3 := h6025c.2.2.2
                                    linarith only [hlam, p6025_0]
                                  · have p6025_0 := h6025c.1
                                    have p6025_1 := h6025c.2.1
                                    have p6025_2 := h6025c.2.2.1
                                    have p6025_3 := h6025c.2.2.2
                                    rcases p6025_3 (m.d 0 1) (by simp) with h6033 | h6033
                                    · linarith only [h0, h6033, hlam]
                                    · linarith only [h4610, h6033, hlam]
                                  · have p6025_0 := h6025c.1
                                    have p6025_1 := h6025c.2.1
                                    have p6025_2 := h6025c.2.2.1
                                    have p6025_3 := h6025c.2.2.2
                                    rcases p6025_3 (m.d 0 1) (by simp) with h6036 | h6036
                                    · linarith only [h0, h6036, hlam]
                                    · linarith only [h4611, h6036, hlam]
                                  · have p6025_0 := h6025c.1
                                    have p6025_1 := h6025c.2.1
                                    have p6025_2 := h6025c.2.2.1
                                    have p6025_3 := h6025c.2.2.2
                                    linarith only [h4611, h4612, h6008, h6011, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6025_1, u0elo1]
                                  · have p6025_0 := h6025c.1
                                    have p6025_1 := h6025c.2.1
                                    have p6025_2 := h6025c.2.2.1
                                    have p6025_3 := h6025c.2.2.2
                                    linarith only [h4610, hlam, p6025_1]
                                  · have p6025_0 := h6025c.1
                                    have p6025_1 := h6025c.2.1
                                    have p6025_2 := h6025c.2.2.1
                                    have p6025_3 := h6025c.2.2.2
                                    linarith only [h5983, hlam, p6025_1]
                                  · have p6025_0 := h6025c.1
                                    have p6025_1 := h6025c.2.1
                                    have p6025_2 := h6025c.2.2.1
                                    have p6025_3 := h6025c.2.2.2
                                    linarith only [hlam, p6025_0]
                                  · have p6025_0 := h6025c.1
                                    have p6025_1 := h6025c.2.1
                                    have p6025_2 := h6025c.2.2.1
                                    have p6025_3 := h6025c.2.2.2
                                    linarith only [h5986, hlam, p6025_1]
                                  · have p6025_0 := h6025c.1
                                    have p6025_1 := h6025c.2.1
                                    have p6025_2 := h6025c.2.2.1
                                    have p6025_3 := h6025c.2.2.2
                                    linarith only [h6004, hlam, p6025_1]
                                  · have p6025_0 := h6025c.1
                                    have p6025_1 := h6025c.2.1
                                    have p6025_2 := h6025c.2.2.1
                                    have p6025_3 := h6025c.2.2.2
                                    linarith only [h4611, hlam, p6025_0]
                                  · have p6025_0 := h6025c.1
                                    have p6025_1 := h6025c.2.1
                                    have p6025_2 := h6025c.2.2.1
                                    have p6025_3 := h6025c.2.2.2
                                    linarith only [h5984, hlam, p6025_0]
                                  · have p6025_0 := h6025c.1
                                    have p6025_1 := h6025c.2.1
                                    have p6025_2 := h6025c.2.2.1
                                    have p6025_3 := h6025c.2.2.2
                                    linarith only [h4610, h4611, h4612, h6008, h6013, h6023, hc23, hc45, hlam, hphi, ht34, p6025_1]
                                  · have p6025_0 := h6025c.1
                                    have p6025_1 := h6025c.2.1
                                    have p6025_2 := h6025c.2.2.1
                                    have p6025_3 := h6025c.2.2.2
                                    linarith only [hlam, p6025_0]
                                  · have p6025_0 := h6025c.1
                                    have p6025_1 := h6025c.2.1
                                    have p6025_2 := h6025c.2.2.1
                                    have p6025_3 := h6025c.2.2.2
                                    linarith only [h6006, hlam, p6025_0]
                                  · have p6025_0 := h6025c.1
                                    have p6025_1 := h6025c.2.1
                                    have p6025_2 := h6025c.2.2.1
                                    have p6025_3 := h6025c.2.2.2
                                    linarith only [h4610, h6008, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6025_1, u0elo4]
                                  · have p6025_0 := h6025c.1
                                    have p6025_1 := h6025c.2.1
                                    have p6025_2 := h6025c.2.2.1
                                    have p6025_3 := h6025c.2.2.2
                                    linarith only [h5985, hlam, p6025_1]
                                  · have p6025_0 := h6025c.1
                                    have p6025_1 := h6025c.2.1
                                    have p6025_2 := h6025c.2.2.1
                                    have p6025_3 := h6025c.2.2.2
                                    rcases p6025_3 (m.d 0 1) (by simp) with h6052 | h6052
                                    · linarith only [h4612, h6052, hlam]
                                    · linarith only [h4610, h6052, hlam]
                                  · have p6025_0 := h6025c.1
                                    have p6025_1 := h6025c.2.1
                                    have p6025_2 := h6025c.2.2.1
                                    have p6025_3 := h6025c.2.2.2
                                    rcases p6025_3 (m.d 0 1) (by simp) with h6055 | h6055
                                    · linarith only [h4612, h6055, hlam]
                                    · linarith only [h4611, h6055, hlam]
                                  · have p6025_0 := h6025c.1
                                    have p6025_1 := h6025c.2.1
                                    have p6025_2 := h6025c.2.2.1
                                    have p6025_3 := h6025c.2.2.2
                                    linarith only [hlam, p6025_0]
                  · linarith only [h0, h5985, h6010, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h5984, h6009, hlam]
              · linarith only [h0, h5983, h6008, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h6062 | h6062
        · rcases m.htr 0 3 5 (by decide) (by decide) with h6063 | h6063
          · linarith only [h4610, h4612, h6063, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6065 | h6065
            · linarith only [h0, h4610, h5985, h6062, h6065, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6067 | h6067
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6068 | h6068
                · rcases m.htr 1 2 5 (by decide) (by decide) with h6069 | h6069
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6070 | h6070
                    · linarith only [h0, h4610, h5985, h6069, h6070, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h4610, h5985, h6062, h6069, h6070, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6073 | h6073
                    · linarith only [h0, h4610, h6069, h6073, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h6062, h6063, h6073, hc13, hc35, hlam, hphi]
                · linarith only [h0, h5984, h6068, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h5983, h6067, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h6078 | h6078
          · linarith only [h4610, h4612, h6078, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6080 | h6080
            · linarith only [h0, h4611, h5985, h6080, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6082 | h6082
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6083 | h6083
                · rcases m.htr 1 2 5 (by decide) (by decide) with h6084 | h6084
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6085 | h6085
                    · linarith only [h0, h4610, h5985, h6062, h6084, h6085, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h6087 | h6087
                      · linarith only [h0, h4610, h5985, h6078, h6087, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h6089 | h6089
                        · linarith only [h0, h4611, h5985, h6080, h6084, h6089, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6091 | h6091
                          · linarith only [h5983, h5985, h6062, h6084, h6091, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6093 | h6093
                            · linarith only [h0, h4610, h4611, h5985, h6082, h6084, h6087, h6093, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6095 | h6095
                              · linarith only [h0, h4611, h5985, h6083, h6084, h6089, h6095, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6097 | h6097
                                · linarith only [h0, h4611, h5985, h6083, h6084, h6089, h6091, h6097, hc23, hc34, hlam, hphi]
                                · rcases h0bigk with h6099c | h6099c | h6099c | h6099c | h6099c | h6099c | h6099c | h6099c | h6099c | h6099c | h6099c | h6099c | h6099c | h6099c | h6099c | h6099c | h6099c | h6099c | h6099c | h6099c | h6099c | h6099c | h6099c | h6099c | h6099c
                                  · have p6099_0 := h6099c.1
                                    have p6099_1 := h6099c.2.1
                                    have p6099_2 := h6099c.2.2.1
                                    have p6099_3 := h6099c.2.2.2
                                    linarith only [hlam, p6099_0]
                                  · have p6099_0 := h6099c.1
                                    have p6099_1 := h6099c.2.1
                                    have p6099_2 := h6099c.2.2.1
                                    have p6099_3 := h6099c.2.2.2
                                    linarith only [h0, hlam, p6099_1]
                                  · have p6099_0 := h6099c.1
                                    have p6099_1 := h6099c.2.1
                                    have p6099_2 := h6099c.2.2.1
                                    have p6099_3 := h6099c.2.2.2
                                    linarith only [h0, h4610, h5985, h6082, h6084, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6099_1]
                                  · have p6099_0 := h6099c.1
                                    have p6099_1 := h6099c.2.1
                                    have p6099_2 := h6099c.2.2.1
                                    have p6099_3 := h6099c.2.2.2
                                    linarith only [h0, h4610, h5985, h6062, h6082, h6084, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6099_1]
                                  · have p6099_0 := h6099c.1
                                    have p6099_1 := h6099c.2.1
                                    have p6099_2 := h6099c.2.2.1
                                    have p6099_3 := h6099c.2.2.2
                                    linarith only [h4612, hlam, p6099_1]
                                  · have p6099_0 := h6099c.1
                                    have p6099_1 := h6099c.2.1
                                    have p6099_2 := h6099c.2.2.1
                                    have p6099_3 := h6099c.2.2.2
                                    linarith only [h5985, h6084, hc01, hc12, hlam, hphi, p6099_1]
                                  · have p6099_0 := h6099c.1
                                    have p6099_1 := h6099c.2.1
                                    have p6099_2 := h6099c.2.2.1
                                    have p6099_3 := h6099c.2.2.2
                                    linarith only [hlam, p6099_0]
                                  · have p6099_0 := h6099c.1
                                    have p6099_1 := h6099c.2.1
                                    have p6099_2 := h6099c.2.2.1
                                    have p6099_3 := h6099c.2.2.2
                                    linarith only [h4610, h5985, h6082, h6084, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6099_1]
                                  · have p6099_0 := h6099c.1
                                    have p6099_1 := h6099c.2.1
                                    have p6099_2 := h6099c.2.2.1
                                    have p6099_3 := h6099c.2.2.2
                                    linarith only [h4610, h5985, h6062, h6082, h6084, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6099_1]
                                  · have p6099_0 := h6099c.1
                                    have p6099_1 := h6099c.2.1
                                    have p6099_2 := h6099c.2.2.1
                                    have p6099_3 := h6099c.2.2.2
                                    linarith only [h5985, hlam, p6099_0]
                                  · have p6099_0 := h6099c.1
                                    have p6099_1 := h6099c.2.1
                                    have p6099_2 := h6099c.2.2.1
                                    have p6099_3 := h6099c.2.2.2
                                    linarith only [h4610, hlam, p6099_1]
                                  · have p6099_0 := h6099c.1
                                    have p6099_1 := h6099c.2.1
                                    have p6099_2 := h6099c.2.2.1
                                    have p6099_3 := h6099c.2.2.2
                                    linarith only [h5983, hlam, p6099_1]
                                  · have p6099_0 := h6099c.1
                                    have p6099_1 := h6099c.2.1
                                    have p6099_2 := h6099c.2.2.1
                                    have p6099_3 := h6099c.2.2.2
                                    linarith only [hlam, p6099_0]
                                  · have p6099_0 := h6099c.1
                                    have p6099_1 := h6099c.2.1
                                    have p6099_2 := h6099c.2.2.1
                                    have p6099_3 := h6099c.2.2.2
                                    linarith only [h6062, hlam, p6099_1]
                                  · have p6099_0 := h6099c.1
                                    have p6099_1 := h6099c.2.1
                                    have p6099_2 := h6099c.2.2.1
                                    have p6099_3 := h6099c.2.2.2
                                    linarith only [h6078, hlam, p6099_1]
                                  · have p6099_0 := h6099c.1
                                    have p6099_1 := h6099c.2.1
                                    have p6099_2 := h6099c.2.2.1
                                    have p6099_3 := h6099c.2.2.2
                                    linarith only [h4611, hlam, p6099_0]
                                  · have p6099_0 := h6099c.1
                                    have p6099_1 := h6099c.2.1
                                    have p6099_2 := h6099c.2.2.1
                                    have p6099_3 := h6099c.2.2.2
                                    linarith only [h5984, hlam, p6099_0]
                                  · have p6099_0 := h6099c.1
                                    have p6099_1 := h6099c.2.1
                                    have p6099_2 := h6099c.2.2.1
                                    have p6099_3 := h6099c.2.2.2
                                    linarith only [h0, h4610, h4611, h5985, h6082, h6084, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6099_1]
                                  · have p6099_0 := h6099c.1
                                    have p6099_1 := h6099c.2.1
                                    have p6099_2 := h6099c.2.2.1
                                    have p6099_3 := h6099c.2.2.2
                                    linarith only [hlam, p6099_0]
                                  · have p6099_0 := h6099c.1
                                    have p6099_1 := h6099c.2.1
                                    have p6099_2 := h6099c.2.2.1
                                    have p6099_3 := h6099c.2.2.2
                                    linarith only [h6080, hlam, p6099_0]
                                  · have p6099_0 := h6099c.1
                                    have p6099_1 := h6099c.2.1
                                    have p6099_2 := h6099c.2.2.1
                                    have p6099_3 := h6099c.2.2.2
                                    linarith only [h4610, h6082, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6099_1, u0elo4]
                                  · have p6099_0 := h6099c.1
                                    have p6099_1 := h6099c.2.1
                                    have p6099_2 := h6099c.2.2.1
                                    have p6099_3 := h6099c.2.2.2
                                    linarith only [h0, h4610, h5985, h6082, h6084, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6099_1]
                                  · have p6099_0 := h6099c.1
                                    have p6099_1 := h6099c.2.1
                                    have p6099_2 := h6099c.2.2.1
                                    have p6099_3 := h6099c.2.2.2
                                    rcases p6099_3 (m.d 0 1) (by simp) with h6122 | h6122
                                    · linarith only [h4612, h6122, hlam]
                                    · linarith only [h4610, h6122, hlam]
                                  · have p6099_0 := h6099c.1
                                    have p6099_1 := h6099c.2.1
                                    have p6099_2 := h6099c.2.2.1
                                    have p6099_3 := h6099c.2.2.2
                                    rcases p6099_3 (m.d 0 1) (by simp) with h6125 | h6125
                                    · linarith only [h4612, h6125, hlam]
                                    · linarith only [h4611, h6125, hlam]
                                  · have p6099_0 := h6099c.1
                                    have p6099_1 := h6099c.2.1
                                    have p6099_2 := h6099c.2.2.1
                                    have p6099_3 := h6099c.2.2.2
                                    linarith only [hlam, p6099_0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6129 | h6129
                    · linarith only [h0, h4610, h6084, h6129, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h6131 | h6131
                      · linarith only [h0, h4611, h6084, h6129, h6131, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h6133 | h6133
                        · linarith only [h0, h4611, h6084, h6133, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6135 | h6135
                          · linarith only [h4610, h6062, h6082, h6135, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6137 | h6137
                            · linarith only [h0, h4611, h6082, h6084, h6129, h6131, h6137, hlam]
                            · linarith only [h0, h4611, h6082, h6084, h6129, h6137, hc23, hc35, hlam, hphi]
                · linarith only [h0, h5984, h6083, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h5983, h6082, hlam]
    · linarith only [h0, h4611, h5984, hlam]
  · linarith only [h0, h4610, h5983, hlam]

set_option maxHeartbeats 14754000 in
set_option maxHeartbeats 14754000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h4610 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h4611 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h4612 | h4612
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 h4610 h4611 h4612
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 h4610 h4611 h4612

end R2N4
