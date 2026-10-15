import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_15S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 12504000 in
set_option maxHeartbeats 12504000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h0bigk := hb0.1
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s1 m hb0 hb1 hb3 hb4 h0 h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h5505 | h5505
    · rcases m.htr 0 1 5 (by decide) (by decide) with h5506 | h5506
      · rcases m.htr 0 2 3 (by decide) (by decide) with h5507 | h5507
        · linarith only [h0, h1, h5507, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h5509 | h5509
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5510 | h5510
            · rcases m.htr 0 3 4 (by decide) (by decide) with h5511 | h5511
              · rcases m.htr 0 3 5 (by decide) (by decide) with h5512 | h5512
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5513 | h5513
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5514 | h5514
                    · linarith only [h0, h1, h5507, h5514, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5516 | h5516
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5517 | h5517
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5518 | h5518
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5519 | h5519
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h5520 | h5520
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h5521 | h5521
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h5522 | h5522
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5523 | h5523
                                    · linarith only [h0, h1, h5514, h5516, h5523, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                    · linarith only [h0, h1, h5514, h5516, h5520, h5523, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · linarith only [h0, h1, h5514, h5522, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h0, h1, h5514, h5521, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h5528 | h5528
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h5529 | h5529
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5530 | h5530
                                    · linarith only [h0, h1, h5514, h5516, h5520, h5530, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5532 | h5532
                                      · linarith only [h0, h1, h5514, h5516, h5520, h5528, h5532, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                      · rcases h0bigk with h5534c | h5534c | h5534c | h5534c | h5534c | h5534c | h5534c | h5534c | h5534c | h5534c | h5534c | h5534c | h5534c | h5534c | h5534c | h5534c | h5534c | h5534c | h5534c | h5534c | h5534c | h5534c | h5534c | h5534c | h5534c
                                        · have p5534_0 := h5534c.1
                                          have p5534_1 := h5534c.2.1
                                          have p5534_2 := h5534c.2.2.1
                                          have p5534_3 := h5534c.2.2.2
                                          linarith only [hlam, p5534_0]
                                        · have p5534_0 := h5534c.1
                                          have p5534_1 := h5534c.2.1
                                          have p5534_2 := h5534c.2.2.1
                                          have p5534_3 := h5534c.2.2.2
                                          linarith only [h1, h5509, h5513, h5514, h5516, h5520, h5528, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5534_1]
                                        · have p5534_0 := h5534c.1
                                          have p5534_1 := h5534c.2.1
                                          have p5534_2 := h5534c.2.2.1
                                          have p5534_3 := h5534c.2.2.2
                                          linarith only [h1, hlam, p5534_0]
                                        · have p5534_0 := h5534c.1
                                          have p5534_1 := h5534c.2.1
                                          have p5534_2 := h5534c.2.2.1
                                          have p5534_3 := h5534c.2.2.2
                                          linarith only [h1, h5513, h5514, h5516, h5520, h5528, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5534_1]
                                        · have p5534_0 := h5534c.1
                                          have p5534_1 := h5534c.2.1
                                          have p5534_2 := h5534c.2.2.1
                                          have p5534_3 := h5534c.2.2.2
                                          linarith only [h1, h5514, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5534_1]
                                        · have p5534_0 := h5534c.1
                                          have p5534_1 := h5534c.2.1
                                          have p5534_2 := h5534c.2.2.1
                                          have p5534_3 := h5534c.2.2.2
                                          linarith only [h0, hlam, p5534_0]
                                        · have p5534_0 := h5534c.1
                                          have p5534_1 := h5534c.2.1
                                          have p5534_2 := h5534c.2.2.1
                                          have p5534_3 := h5534c.2.2.2
                                          linarith only [hlam, p5534_0]
                                        · have p5534_0 := h5534c.1
                                          have p5534_1 := h5534c.2.1
                                          have p5534_2 := h5534c.2.2.1
                                          have p5534_3 := h5534c.2.2.2
                                          linarith only [h5507, hlam, p5534_0]
                                        · have p5534_0 := h5534c.1
                                          have p5534_1 := h5534c.2.1
                                          have p5534_2 := h5534c.2.2.1
                                          have p5534_3 := h5534c.2.2.2
                                          linarith only [h5513, h5516, h5520, h5528, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p5534_1]
                                        · have p5534_0 := h5534c.1
                                          have p5534_1 := h5534c.2.1
                                          have p5534_2 := h5534c.2.2.1
                                          have p5534_3 := h5534c.2.2.2
                                          linarith only [h0, h1, h5506, h5514, h5516, h5520, h5528, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5534_1]
                                        · have p5534_0 := h5534c.1
                                          have p5534_1 := h5534c.2.1
                                          have p5534_2 := h5534c.2.2.1
                                          have p5534_3 := h5534c.2.2.2
                                          linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5534_1]
                                        · have p5534_0 := h5534c.1
                                          have p5534_1 := h5534c.2.1
                                          have p5534_2 := h5534c.2.2.1
                                          have p5534_3 := h5534c.2.2.2
                                          linarith only [h1, h5514, hc02, hc23, hlam, hphi, p5534_1]
                                        · have p5534_0 := h5534c.1
                                          have p5534_1 := h5534c.2.1
                                          have p5534_2 := h5534c.2.2.1
                                          have p5534_3 := h5534c.2.2.2
                                          linarith only [hlam, p5534_0]
                                        · have p5534_0 := h5534c.1
                                          have p5534_1 := h5534c.2.1
                                          have p5534_2 := h5534c.2.2.1
                                          have p5534_3 := h5534c.2.2.2
                                          linarith only [h1, h5513, h5514, h5516, h5520, h5528, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5534_1]
                                        · have p5534_0 := h5534c.1
                                          have p5534_1 := h5534c.2.1
                                          have p5534_2 := h5534c.2.2.1
                                          have p5534_3 := h5534c.2.2.2
                                          linarith only [h1, h5513, h5514, h5516, h5520, h5528, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5534_1]
                                        · have p5534_0 := h5534c.1
                                          have p5534_1 := h5534c.2.1
                                          have p5534_2 := h5534c.2.2.1
                                          have p5534_3 := h5534c.2.2.2
                                          linarith only [h5505, hlam, p5534_0]
                                        · have p5534_0 := h5534c.1
                                          have p5534_1 := h5534c.2.1
                                          have p5534_2 := h5534c.2.2.1
                                          have p5534_3 := h5534c.2.2.2
                                          linarith only [h5509, hlam, p5534_0]
                                        · have p5534_0 := h5534c.1
                                          have p5534_1 := h5534c.2.1
                                          have p5534_2 := h5534c.2.2.1
                                          have p5534_3 := h5534c.2.2.2
                                          linarith only [h5511, hlam, p5534_0]
                                        · have p5534_0 := h5534c.1
                                          have p5534_1 := h5534c.2.1
                                          have p5534_2 := h5534c.2.2.1
                                          have p5534_3 := h5534c.2.2.2
                                          linarith only [hlam, p5534_0]
                                        · have p5534_0 := h5534c.1
                                          have p5534_1 := h5534c.2.1
                                          have p5534_2 := h5534c.2.2.1
                                          have p5534_3 := h5534c.2.2.2
                                          linarith only [h0, h5509, h5513, h5516, h5520, h5528, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5534_1]
                                        · have p5534_0 := h5534c.1
                                          have p5534_1 := h5534c.2.1
                                          have p5534_2 := h5534c.2.2.1
                                          have p5534_3 := h5534c.2.2.2
                                          linarith only [h5506, hlam, p5534_0]
                                        · have p5534_0 := h5534c.1
                                          have p5534_1 := h5534c.2.1
                                          have p5534_2 := h5534c.2.2.1
                                          have p5534_3 := h5534c.2.2.2
                                          linarith only [h5510, hlam, p5534_1]
                                        · have p5534_0 := h5534c.1
                                          have p5534_1 := h5534c.2.1
                                          have p5534_2 := h5534c.2.2.1
                                          have p5534_3 := h5534c.2.2.2
                                          linarith only [h5512, hlam, p5534_0]
                                        · have p5534_0 := h5534c.1
                                          have p5534_1 := h5534c.2.1
                                          have p5534_2 := h5534c.2.2.1
                                          have p5534_3 := h5534c.2.2.2
                                          linarith only [h5513, hlam, p5534_1]
                                        · have p5534_0 := h5534c.1
                                          have p5534_1 := h5534c.2.1
                                          have p5534_2 := h5534c.2.2.1
                                          have p5534_3 := h5534c.2.2.2
                                          linarith only [hlam, p5534_0]
                                  · linarith only [h0, h1, h5514, h5516, h5528, h5529, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                                · linarith only [h0, h1, h5509, h5513, h5514, h5520, h5528, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h0, h1, h5516, h5519, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1, h5516, h5518, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h1, h5510, h5516, h5517, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h1, h5509, h5514, h5516, hc12, hc23, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5566 | h5566
                    · linarith only [h0, h1, h5507, h5566, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5568 | h5568
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5569 | h5569
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5570 | h5570
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5571 | h5571
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h5572 | h5572
                              · linarith only [h5505, h5513, h5572, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h5574 | h5574
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h5575 | h5575
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5576 | h5576
                                    · linarith only [h5505, h5513, h5568, h5576, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5578 | h5578
                                      · linarith only [h5505, h5513, h5568, h5574, h5578, hlam]
                                      · rcases h0bigk with h5580c | h5580c | h5580c | h5580c | h5580c | h5580c | h5580c | h5580c | h5580c | h5580c | h5580c | h5580c | h5580c | h5580c | h5580c | h5580c | h5580c | h5580c | h5580c | h5580c | h5580c | h5580c | h5580c | h5580c | h5580c
                                        · have p5580_0 := h5580c.1
                                          have p5580_1 := h5580c.2.1
                                          have p5580_2 := h5580c.2.2.1
                                          have p5580_3 := h5580c.2.2.2
                                          linarith only [hlam, p5580_0]
                                        · have p5580_0 := h5580c.1
                                          have p5580_1 := h5580c.2.1
                                          have p5580_2 := h5580c.2.2.1
                                          have p5580_3 := h5580c.2.2.2
                                          linarith only [h0, h1, h5566, h5569, h5574, h5576, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5580_1]
                                        · have p5580_0 := h5580c.1
                                          have p5580_1 := h5580c.2.1
                                          have p5580_2 := h5580c.2.2.1
                                          have p5580_3 := h5580c.2.2.2
                                          linarith only [h1, hlam, p5580_0]
                                        · have p5580_0 := h5580c.1
                                          have p5580_1 := h5580c.2.1
                                          have p5580_2 := h5580c.2.2.1
                                          have p5580_3 := h5580c.2.2.2
                                          linarith only [h1, h5505, h5566, h5568, h5574, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5580_1]
                                        · have p5580_0 := h5580c.1
                                          have p5580_1 := h5580c.2.1
                                          have p5580_2 := h5580c.2.2.1
                                          have p5580_3 := h5580c.2.2.2
                                          linarith only [h1, h5505, h5513, h5566, h5568, h5574, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5580_1]
                                        · have p5580_0 := h5580c.1
                                          have p5580_1 := h5580c.2.1
                                          have p5580_2 := h5580c.2.2.1
                                          have p5580_3 := h5580c.2.2.2
                                          linarith only [h0, hlam, p5580_0]
                                        · have p5580_0 := h5580c.1
                                          have p5580_1 := h5580c.2.1
                                          have p5580_2 := h5580c.2.2.1
                                          have p5580_3 := h5580c.2.2.2
                                          linarith only [hlam, p5580_0]
                                        · have p5580_0 := h5580c.1
                                          have p5580_1 := h5580c.2.1
                                          have p5580_2 := h5580c.2.2.1
                                          have p5580_3 := h5580c.2.2.2
                                          linarith only [h5507, hlam, p5580_0]
                                        · have p5580_0 := h5580c.1
                                          have p5580_1 := h5580c.2.1
                                          have p5580_2 := h5580c.2.2.1
                                          have p5580_3 := h5580c.2.2.2
                                          linarith only [h0, h1, h5505, h5566, h5568, h5574, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5580_1]
                                        · have p5580_0 := h5580c.1
                                          have p5580_1 := h5580c.2.1
                                          have p5580_2 := h5580c.2.2.1
                                          have p5580_3 := h5580c.2.2.2
                                          linarith only [h0, h1, h5505, h5513, h5566, h5568, h5574, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5580_1]
                                        · have p5580_0 := h5580c.1
                                          have p5580_1 := h5580c.2.1
                                          have p5580_2 := h5580c.2.2.1
                                          have p5580_3 := h5580c.2.2.2
                                          linarith only [h0, h5569, h5574, h5576, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p5580_1]
                                        · have p5580_0 := h5580c.1
                                          have p5580_1 := h5580c.2.1
                                          have p5580_2 := h5580c.2.2.1
                                          have p5580_3 := h5580c.2.2.2
                                          linarith only [h1, h5566, hc02, hc23, hlam, hphi, p5580_1]
                                        · have p5580_0 := h5580c.1
                                          have p5580_1 := h5580c.2.1
                                          have p5580_2 := h5580c.2.2.1
                                          have p5580_3 := h5580c.2.2.2
                                          linarith only [hlam, p5580_0]
                                        · have p5580_0 := h5580c.1
                                          have p5580_1 := h5580c.2.1
                                          have p5580_2 := h5580c.2.2.1
                                          have p5580_3 := h5580c.2.2.2
                                          rcases p5580_3 (m.d 0 1) (by simp) with h5594 | h5594
                                          · linarith only [h1, h5594, hlam]
                                          · linarith only [h5505, h5594, hlam]
                                        · have p5580_0 := h5580c.1
                                          have p5580_1 := h5580c.2.1
                                          have p5580_2 := h5580c.2.2.1
                                          have p5580_3 := h5580c.2.2.2
                                          rcases p5580_3 (m.d 0 1) (by simp) with h5597 | h5597
                                          · linarith only [h1, h5597, hlam]
                                          · linarith only [h5506, h5597, hlam]
                                        · have p5580_0 := h5580c.1
                                          have p5580_1 := h5580c.2.1
                                          have p5580_2 := h5580c.2.2.1
                                          have p5580_3 := h5580c.2.2.2
                                          linarith only [h5505, hlam, p5580_0]
                                        · have p5580_0 := h5580c.1
                                          have p5580_1 := h5580c.2.1
                                          have p5580_2 := h5580c.2.2.1
                                          have p5580_3 := h5580c.2.2.2
                                          linarith only [h5509, hlam, p5580_0]
                                        · have p5580_0 := h5580c.1
                                          have p5580_1 := h5580c.2.1
                                          have p5580_2 := h5580c.2.2.1
                                          have p5580_3 := h5580c.2.2.2
                                          linarith only [h5511, hlam, p5580_0]
                                        · have p5580_0 := h5580c.1
                                          have p5580_1 := h5580c.2.1
                                          have p5580_2 := h5580c.2.2.1
                                          have p5580_3 := h5580c.2.2.2
                                          linarith only [hlam, p5580_0]
                                        · have p5580_0 := h5580c.1
                                          have p5580_1 := h5580c.2.1
                                          have p5580_2 := h5580c.2.2.1
                                          have p5580_3 := h5580c.2.2.2
                                          linarith only [h5513, hlam, p5580_0]
                                        · have p5580_0 := h5580c.1
                                          have p5580_1 := h5580c.2.1
                                          have p5580_2 := h5580c.2.2.1
                                          have p5580_3 := h5580c.2.2.2
                                          linarith only [h5506, hlam, p5580_0]
                                        · have p5580_0 := h5580c.1
                                          have p5580_1 := h5580c.2.1
                                          have p5580_2 := h5580c.2.2.1
                                          have p5580_3 := h5580c.2.2.2
                                          linarith only [h5510, hlam, p5580_1]
                                        · have p5580_0 := h5580c.1
                                          have p5580_1 := h5580c.2.1
                                          have p5580_2 := h5580c.2.2.1
                                          have p5580_3 := h5580c.2.2.2
                                          linarith only [h5512, hlam, p5580_0]
                                        · have p5580_0 := h5580c.1
                                          have p5580_1 := h5580c.2.1
                                          have p5580_2 := h5580c.2.2.1
                                          have p5580_3 := h5580c.2.2.2
                                          linarith only [h1, h5505, h5506, h5566, h5568, h5574, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5580_1]
                                        · have p5580_0 := h5580c.1
                                          have p5580_1 := h5580c.2.1
                                          have p5580_2 := h5580c.2.2.1
                                          have p5580_3 := h5580c.2.2.2
                                          linarith only [hlam, p5580_0]
                                  · linarith only [h0, h1, h5566, h5575, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h0, h1, h5566, h5568, h5574, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h0, h1, h5510, h5512, h5568, h5571, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h1, h5511, h5513, h5570, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h0, h1, h5510, h5568, h5569, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h1, h5509, h5566, h5568, hc12, hc23, hlam, hphi]
                · linarith only [h0, h1, h5510, h5512, hlam]
              · linarith only [h0, h1, h5509, h5511, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h5618 | h5618
              · rcases m.htr 0 3 5 (by decide) (by decide) with h5619 | h5619
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5620 | h5620
                  · linarith only [h5509, h5510, h5620, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5622 | h5622
                    · linarith only [h0, h1, h5507, h5622, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5624 | h5624
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5625 | h5625
                        · linarith only [h0, h5510, h5625, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5627 | h5627
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5628 | h5628
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h5629 | h5629
                              · linarith only [h1, h5505, h5620, h5622, h5629, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h5631 | h5631
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h5632 | h5632
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5633 | h5633
                                    · linarith only [h1, h5506, h5510, h5620, h5622, h5624, h5625, h5633, hc02, hc23, hlam, hphi]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5635 | h5635
                                      · linarith only [h1, h5506, h5622, h5624, h5625, h5631, h5633, h5635, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                      · rcases h0bigk with h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c
                                        · have p5637_0 := h5637c.1
                                          have p5637_1 := h5637c.2.1
                                          have p5637_2 := h5637c.2.2.1
                                          have p5637_3 := h5637c.2.2.2
                                          linarith only [hlam, p5637_0]
                                        · have p5637_0 := h5637c.1
                                          have p5637_1 := h5637c.2.1
                                          have p5637_2 := h5637c.2.2.1
                                          have p5637_3 := h5637c.2.2.2
                                          linarith only [h0, h1, h5622, h5624, h5631, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5637_1]
                                        · have p5637_0 := h5637c.1
                                          have p5637_1 := h5637c.2.1
                                          have p5637_2 := h5637c.2.2.1
                                          have p5637_3 := h5637c.2.2.2
                                          linarith only [h1, hlam, p5637_0]
                                        · have p5637_0 := h5637c.1
                                          have p5637_1 := h5637c.2.1
                                          have p5637_2 := h5637c.2.2.1
                                          have p5637_3 := h5637c.2.2.2
                                          linarith only [h1, h5505, h5622, h5624, h5631, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5637_1]
                                        · have p5637_0 := h5637c.1
                                          have p5637_1 := h5637c.2.1
                                          have p5637_2 := h5637c.2.2.1
                                          have p5637_3 := h5637c.2.2.2
                                          linarith only [h0, h1, h5510, h5622, h5624, h5631, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5637_1]
                                        · have p5637_0 := h5637c.1
                                          have p5637_1 := h5637c.2.1
                                          have p5637_2 := h5637c.2.2.1
                                          have p5637_3 := h5637c.2.2.2
                                          linarith only [h0, hlam, p5637_0]
                                        · have p5637_0 := h5637c.1
                                          have p5637_1 := h5637c.2.1
                                          have p5637_2 := h5637c.2.2.1
                                          have p5637_3 := h5637c.2.2.2
                                          linarith only [hlam, p5637_0]
                                        · have p5637_0 := h5637c.1
                                          have p5637_1 := h5637c.2.1
                                          have p5637_2 := h5637c.2.2.1
                                          have p5637_3 := h5637c.2.2.2
                                          linarith only [h5507, hlam, p5637_0]
                                        · have p5637_0 := h5637c.1
                                          have p5637_1 := h5637c.2.1
                                          have p5637_2 := h5637c.2.2.1
                                          have p5637_3 := h5637c.2.2.2
                                          linarith only [h5505, h5510, h5624, h5631, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5637_1]
                                        · have p5637_0 := h5637c.1
                                          have p5637_1 := h5637c.2.1
                                          have p5637_2 := h5637c.2.2.1
                                          have p5637_3 := h5637c.2.2.2
                                          linarith only [h5510, hlam, p5637_0]
                                        · have p5637_0 := h5637c.1
                                          have p5637_1 := h5637c.2.1
                                          have p5637_2 := h5637c.2.2.1
                                          have p5637_3 := h5637c.2.2.2
                                          linarith only [h0, h5624, h5631, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p5637_1]
                                        · have p5637_0 := h5637c.1
                                          have p5637_1 := h5637c.2.1
                                          have p5637_2 := h5637c.2.2.1
                                          have p5637_3 := h5637c.2.2.2
                                          linarith only [h1, h5622, hc02, hc23, hlam, hphi, p5637_1]
                                        · have p5637_0 := h5637c.1
                                          have p5637_1 := h5637c.2.1
                                          have p5637_2 := h5637c.2.2.1
                                          have p5637_3 := h5637c.2.2.2
                                          linarith only [hlam, p5637_0]
                                        · have p5637_0 := h5637c.1
                                          have p5637_1 := h5637c.2.1
                                          have p5637_2 := h5637c.2.2.1
                                          have p5637_3 := h5637c.2.2.2
                                          rcases p5637_3 (m.d 0 1) (by simp) with h5651 | h5651
                                          · linarith only [h1, h5651, hlam]
                                          · linarith only [h5505, h5651, hlam]
                                        · have p5637_0 := h5637c.1
                                          have p5637_1 := h5637c.2.1
                                          have p5637_2 := h5637c.2.2.1
                                          have p5637_3 := h5637c.2.2.2
                                          linarith only [h0, h1, h5510, h5622, h5624, h5631, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5637_1]
                                        · have p5637_0 := h5637c.1
                                          have p5637_1 := h5637c.2.1
                                          have p5637_2 := h5637c.2.2.1
                                          have p5637_3 := h5637c.2.2.2
                                          linarith only [h5505, hlam, p5637_0]
                                        · have p5637_0 := h5637c.1
                                          have p5637_1 := h5637c.2.1
                                          have p5637_2 := h5637c.2.2.1
                                          have p5637_3 := h5637c.2.2.2
                                          linarith only [h5509, hlam, p5637_0]
                                        · have p5637_0 := h5637c.1
                                          have p5637_1 := h5637c.2.1
                                          have p5637_2 := h5637c.2.2.1
                                          have p5637_3 := h5637c.2.2.2
                                          linarith only [h5618, hlam, p5637_0]
                                        · have p5637_0 := h5637c.1
                                          have p5637_1 := h5637c.2.1
                                          have p5637_2 := h5637c.2.2.1
                                          have p5637_3 := h5637c.2.2.2
                                          linarith only [hlam, p5637_0]
                                        · have p5637_0 := h5637c.1
                                          have p5637_1 := h5637c.2.1
                                          have p5637_2 := h5637c.2.2.1
                                          have p5637_3 := h5637c.2.2.2
                                          linarith only [h5620, hlam, p5637_0]
                                        · have p5637_0 := h5637c.1
                                          have p5637_1 := h5637c.2.1
                                          have p5637_2 := h5637c.2.2.1
                                          have p5637_3 := h5637c.2.2.2
                                          linarith only [h5506, hlam, p5637_0]
                                        · have p5637_0 := h5637c.1
                                          have p5637_1 := h5637c.2.1
                                          have p5637_2 := h5637c.2.2.1
                                          have p5637_3 := h5637c.2.2.2
                                          linarith only [h0, h5624, h5631, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p5637_1]
                                        · have p5637_0 := h5637c.1
                                          have p5637_1 := h5637c.2.1
                                          have p5637_2 := h5637c.2.2.1
                                          have p5637_3 := h5637c.2.2.2
                                          linarith only [h5619, hlam, p5637_0]
                                        · have p5637_0 := h5637c.1
                                          have p5637_1 := h5637c.2.1
                                          have p5637_2 := h5637c.2.2.1
                                          have p5637_3 := h5637c.2.2.2
                                          linarith only [h1, h5505, h5506, h5622, h5624, h5631, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5637_1]
                                        · have p5637_0 := h5637c.1
                                          have p5637_1 := h5637c.2.1
                                          have p5637_2 := h5637c.2.2.1
                                          have p5637_3 := h5637c.2.2.2
                                          linarith only [hlam, p5637_0]
                                  · linarith only [h0, h1, h5622, h5624, h5631, h5632, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                                · linarith only [h1, h5506, h5622, h5624, h5625, h5631, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h1, h5506, h5624, h5625, h5628, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h1, h5506, h5624, h5625, h5627, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h1, h5509, h5622, h5624, hc12, hc23, hlam, hphi]
                · linarith only [h1, h5506, h5619, hlam]
              · linarith only [h1, h5506, h5509, h5510, h5618, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5672 | h5672
            · rcases m.htr 0 3 4 (by decide) (by decide) with h5673 | h5673
              · rcases m.htr 0 3 5 (by decide) (by decide) with h5674 | h5674
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5675 | h5675
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5676 | h5676
                    · linarith only [h0, h5507, h5676, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5678 | h5678
                      · linarith only [h0, h5509, h5672, h5678, hc01, hc25, hlam, hphi, ht0b, ht5b]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5680 | h5680
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5681 | h5681
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5682 | h5682
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h5683 | h5683
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h5684 | h5684
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h5685 | h5685
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5686 | h5686
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5687 | h5687
                                      · rcases h0bigk with h5688c | h5688c | h5688c | h5688c | h5688c | h5688c | h5688c | h5688c | h5688c | h5688c | h5688c | h5688c | h5688c | h5688c | h5688c | h5688c | h5688c | h5688c | h5688c | h5688c | h5688c | h5688c | h5688c | h5688c | h5688c
                                        · have p5688_0 := h5688c.1
                                          have p5688_1 := h5688c.2.1
                                          have p5688_2 := h5688c.2.2.1
                                          have p5688_3 := h5688c.2.2.2
                                          linarith only [hlam, p5688_0]
                                        · have p5688_0 := h5688c.1
                                          have p5688_1 := h5688c.2.1
                                          have p5688_2 := h5688c.2.2.1
                                          have p5688_3 := h5688c.2.2.2
                                          linarith only [h0, h1, h5676, h5680, h5685, h5687, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5688_1]
                                        · have p5688_0 := h5688c.1
                                          have p5688_1 := h5688c.2.1
                                          have p5688_2 := h5688c.2.2.1
                                          have p5688_3 := h5688c.2.2.2
                                          linarith only [h1, hlam, p5688_0]
                                        · have p5688_0 := h5688c.1
                                          have p5688_1 := h5688c.2.1
                                          have p5688_2 := h5688c.2.2.1
                                          have p5688_3 := h5688c.2.2.2
                                          linarith only [h0, h1, h5509, h5676, h5680, h5685, h5687, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5688_1]
                                        · have p5688_0 := h5688c.1
                                          have p5688_1 := h5688c.2.1
                                          have p5688_2 := h5688c.2.2.1
                                          have p5688_3 := h5688c.2.2.2
                                          linarith only [h1, h5676, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5688_1]
                                        · have p5688_0 := h5688c.1
                                          have p5688_1 := h5688c.2.1
                                          have p5688_2 := h5688c.2.2.1
                                          have p5688_3 := h5688c.2.2.2
                                          linarith only [h0, hlam, p5688_0]
                                        · have p5688_0 := h5688c.1
                                          have p5688_1 := h5688c.2.1
                                          have p5688_2 := h5688c.2.2.1
                                          have p5688_3 := h5688c.2.2.2
                                          linarith only [hlam, p5688_0]
                                        · have p5688_0 := h5688c.1
                                          have p5688_1 := h5688c.2.1
                                          have p5688_2 := h5688c.2.2.1
                                          have p5688_3 := h5688c.2.2.2
                                          linarith only [h5507, hlam, p5688_0]
                                        · have p5688_0 := h5688c.1
                                          have p5688_1 := h5688c.2.1
                                          have p5688_2 := h5688c.2.2.1
                                          have p5688_3 := h5688c.2.2.2
                                          linarith only [h5509, hlam, p5688_1]
                                        · have p5688_0 := h5688c.1
                                          have p5688_1 := h5688c.2.1
                                          have p5688_2 := h5688c.2.2.1
                                          have p5688_3 := h5688c.2.2.2
                                          linarith only [h5506, h5509, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p5688_1]
                                        · have p5688_0 := h5688c.1
                                          have p5688_1 := h5688c.2.1
                                          have p5688_2 := h5688c.2.2.1
                                          have p5688_3 := h5688c.2.2.2
                                          linarith only [h1, h5676, hc01, hc23, hlam, hphi, ht12, p5688_1]
                                        · have p5688_0 := h5688c.1
                                          have p5688_1 := h5688c.2.1
                                          have p5688_2 := h5688c.2.2.1
                                          have p5688_3 := h5688c.2.2.2
                                          linarith only [h1, h5676, hc02, hc23, hlam, hphi, p5688_1]
                                        · have p5688_0 := h5688c.1
                                          have p5688_1 := h5688c.2.1
                                          have p5688_2 := h5688c.2.2.1
                                          have p5688_3 := h5688c.2.2.2
                                          linarith only [hlam, p5688_0]
                                        · have p5688_0 := h5688c.1
                                          have p5688_1 := h5688c.2.1
                                          have p5688_2 := h5688c.2.2.1
                                          have p5688_3 := h5688c.2.2.2
                                          linarith only [h0, h1, h5509, h5676, h5680, h5685, h5687, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5688_1]
                                        · have p5688_0 := h5688c.1
                                          have p5688_1 := h5688c.2.1
                                          have p5688_2 := h5688c.2.2.1
                                          have p5688_3 := h5688c.2.2.2
                                          rcases p5688_3 (m.d 0 1) (by simp) with h5703 | h5703
                                          · linarith only [h1, h5703, hlam]
                                          · linarith only [h5506, h5703, hlam]
                                        · have p5688_0 := h5688c.1
                                          have p5688_1 := h5688c.2.1
                                          have p5688_2 := h5688c.2.2.1
                                          have p5688_3 := h5688c.2.2.2
                                          linarith only [h5505, hlam, p5688_0]
                                        · have p5688_0 := h5688c.1
                                          have p5688_1 := h5688c.2.1
                                          have p5688_2 := h5688c.2.2.1
                                          have p5688_3 := h5688c.2.2.2
                                          linarith only [h0, h5680, h5685, h5687, hc04, hc45, hlam, hphi, ht0b, ht5b, p5688_1]
                                        · have p5688_0 := h5688c.1
                                          have p5688_1 := h5688c.2.1
                                          have p5688_2 := h5688c.2.2.1
                                          have p5688_3 := h5688c.2.2.2
                                          linarith only [h5673, hlam, p5688_0]
                                        · have p5688_0 := h5688c.1
                                          have p5688_1 := h5688c.2.1
                                          have p5688_2 := h5688c.2.2.1
                                          have p5688_3 := h5688c.2.2.2
                                          linarith only [hlam, p5688_0]
                                        · have p5688_0 := h5688c.1
                                          have p5688_1 := h5688c.2.1
                                          have p5688_2 := h5688c.2.2.1
                                          have p5688_3 := h5688c.2.2.2
                                          linarith only [h1, h5505, h5506, h5676, h5680, h5685, h5687, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5688_1]
                                        · have p5688_0 := h5688c.1
                                          have p5688_1 := h5688c.2.1
                                          have p5688_2 := h5688c.2.2.1
                                          have p5688_3 := h5688c.2.2.2
                                          linarith only [h5506, hlam, p5688_0]
                                        · have p5688_0 := h5688c.1
                                          have p5688_1 := h5688c.2.1
                                          have p5688_2 := h5688c.2.2.1
                                          have p5688_3 := h5688c.2.2.2
                                          linarith only [h5672, hlam, p5688_1]
                                        · have p5688_0 := h5688c.1
                                          have p5688_1 := h5688c.2.1
                                          have p5688_2 := h5688c.2.2.1
                                          have p5688_3 := h5688c.2.2.2
                                          linarith only [h5674, hlam, p5688_0]
                                        · have p5688_0 := h5688c.1
                                          have p5688_1 := h5688c.2.1
                                          have p5688_2 := h5688c.2.2.1
                                          have p5688_3 := h5688c.2.2.2
                                          linarith only [h5675, hlam, p5688_1]
                                        · have p5688_0 := h5688c.1
                                          have p5688_1 := h5688c.2.1
                                          have p5688_2 := h5688c.2.2.1
                                          have p5688_3 := h5688c.2.2.2
                                          linarith only [hlam, p5688_0]
                                      · linarith only [h1, h5505, h5676, h5683, h5687, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · linarith only [h1, h5505, h5676, h5683, h5686, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · linarith only [h1, h5505, h5676, h5683, h5685, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                · linarith only [h1, h5505, h5676, h5678, h5680, h5684, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h1, h5505, h5675, h5678, h5680, h5683, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h0, h1, h5680, h5682, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h1, h5505, h5678, h5680, h5681, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h5509, h5672, h5680, hc12, hc24, hlam, hphi]
                  · linarith only [h5509, h5672, h5675, hlam]
                · linarith only [h0, h1, h5672, h5674, hlam]
              · linarith only [h1, h5505, h5673, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h5727 | h5727
              · rcases m.htr 0 3 5 (by decide) (by decide) with h5728 | h5728
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5729 | h5729
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5730 | h5730
                    · linarith only [h0, h5507, h5730, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5732 | h5732
                      · linarith only [h0, h5509, h5732, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5734 | h5734
                        · linarith only [h0, h5672, h5734, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5736 | h5736
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5737 | h5737
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h5738 | h5738
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h5739 | h5739
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h5740 | h5740
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5741 | h5741
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5742 | h5742
                                      · rcases h0bigk with h5743c | h5743c | h5743c | h5743c | h5743c | h5743c | h5743c | h5743c | h5743c | h5743c | h5743c | h5743c | h5743c | h5743c | h5743c | h5743c | h5743c | h5743c | h5743c | h5743c | h5743c | h5743c | h5743c | h5743c | h5743c
                                        · have p5743_0 := h5743c.1
                                          have p5743_1 := h5743c.2.1
                                          have p5743_2 := h5743c.2.2.1
                                          have p5743_3 := h5743c.2.2.2
                                          linarith only [hlam, p5743_0]
                                        · have p5743_0 := h5743c.1
                                          have p5743_1 := h5743c.2.1
                                          have p5743_2 := h5743c.2.2.1
                                          have p5743_3 := h5743c.2.2.2
                                          linarith only [h1, h5730, hc02, hc23, hlam, hphi, p5743_1]
                                        · have p5743_0 := h5743c.1
                                          have p5743_1 := h5743c.2.1
                                          have p5743_2 := h5743c.2.2.1
                                          have p5743_3 := h5743c.2.2.2
                                          linarith only [h1, hlam, p5743_0]
                                        · have p5743_0 := h5743c.1
                                          have p5743_1 := h5743c.2.1
                                          have p5743_2 := h5743c.2.2.1
                                          have p5743_3 := h5743c.2.2.2
                                          linarith only [h1, h5730, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5743_1]
                                        · have p5743_0 := h5743c.1
                                          have p5743_1 := h5743c.2.1
                                          have p5743_2 := h5743c.2.2.1
                                          have p5743_3 := h5743c.2.2.2
                                          linarith only [h0, h1, h5672, h5730, hc12, hc23, hlam, hphi, p5743_1]
                                        · have p5743_0 := h5743c.1
                                          have p5743_1 := h5743c.2.1
                                          have p5743_2 := h5743c.2.2.1
                                          have p5743_3 := h5743c.2.2.2
                                          linarith only [h0, hlam, p5743_0]
                                        · have p5743_0 := h5743c.1
                                          have p5743_1 := h5743c.2.1
                                          have p5743_2 := h5743c.2.2.1
                                          have p5743_3 := h5743c.2.2.2
                                          linarith only [hlam, p5743_0]
                                        · have p5743_0 := h5743c.1
                                          have p5743_1 := h5743c.2.1
                                          have p5743_2 := h5743c.2.2.1
                                          have p5743_3 := h5743c.2.2.2
                                          linarith only [h5507, hlam, p5743_0]
                                        · have p5743_0 := h5743c.1
                                          have p5743_1 := h5743c.2.1
                                          have p5743_2 := h5743c.2.2.1
                                          have p5743_3 := h5743c.2.2.2
                                          linarith only [h5509, hlam, p5743_1]
                                        · have p5743_0 := h5743c.1
                                          have p5743_1 := h5743c.2.1
                                          have p5743_2 := h5743c.2.2.1
                                          have p5743_3 := h5743c.2.2.2
                                          linarith only [h5672, hlam, p5743_0]
                                        · have p5743_0 := h5743c.1
                                          have p5743_1 := h5743c.2.1
                                          have p5743_2 := h5743c.2.2.1
                                          have p5743_3 := h5743c.2.2.2
                                          linarith only [h5505, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b, p5743_1]
                                        · have p5743_0 := h5743c.1
                                          have p5743_1 := h5743c.2.1
                                          have p5743_2 := h5743c.2.2.1
                                          have p5743_3 := h5743c.2.2.2
                                          linarith only [h0, h1, h5730, hc12, hc23, hlam, hphi, p5743_1]
                                        · have p5743_0 := h5743c.1
                                          have p5743_1 := h5743c.2.1
                                          have p5743_2 := h5743c.2.2.1
                                          have p5743_3 := h5743c.2.2.2
                                          linarith only [hlam, p5743_0]
                                        · have p5743_0 := h5743c.1
                                          have p5743_1 := h5743c.2.1
                                          have p5743_2 := h5743c.2.2.1
                                          have p5743_3 := h5743c.2.2.2
                                          linarith only [h1, h5505, h5730, h5736, h5742, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5743_1]
                                        · have p5743_0 := h5743c.1
                                          have p5743_1 := h5743c.2.1
                                          have p5743_2 := h5743c.2.2.1
                                          have p5743_3 := h5743c.2.2.2
                                          linarith only [h0, h1, h5672, h5730, hc12, hc23, hlam, hphi, p5743_1]
                                        · have p5743_0 := h5743c.1
                                          have p5743_1 := h5743c.2.1
                                          have p5743_2 := h5743c.2.2.1
                                          have p5743_3 := h5743c.2.2.2
                                          linarith only [h5505, hlam, p5743_0]
                                        · have p5743_0 := h5743c.1
                                          have p5743_1 := h5743c.2.1
                                          have p5743_2 := h5743c.2.2.1
                                          have p5743_3 := h5743c.2.2.2
                                          linarith only [h0, h1, h5505, h5730, hc12, hc23, hlam, hphi, p5743_1]
                                        · have p5743_0 := h5743c.1
                                          have p5743_1 := h5743c.2.1
                                          have p5743_2 := h5743c.2.2.1
                                          have p5743_3 := h5743c.2.2.2
                                          linarith only [h5727, hlam, p5743_0]
                                        · have p5743_0 := h5743c.1
                                          have p5743_1 := h5743c.2.1
                                          have p5743_2 := h5743c.2.2.1
                                          have p5743_3 := h5743c.2.2.2
                                          linarith only [hlam, p5743_0]
                                        · have p5743_0 := h5743c.1
                                          have p5743_1 := h5743c.2.1
                                          have p5743_2 := h5743c.2.2.1
                                          have p5743_3 := h5743c.2.2.2
                                          linarith only [h0, h5509, h5672, hc12, hc24, hlam, hphi, p5743_1]
                                        · have p5743_0 := h5743c.1
                                          have p5743_1 := h5743c.2.1
                                          have p5743_2 := h5743c.2.2.1
                                          have p5743_3 := h5743c.2.2.2
                                          linarith only [h5506, hlam, p5743_0]
                                        · have p5743_0 := h5743c.1
                                          have p5743_1 := h5743c.2.1
                                          have p5743_2 := h5743c.2.2.1
                                          have p5743_3 := h5743c.2.2.2
                                          linarith only [h0, h1, h5506, h5730, hc12, hc23, hlam, hphi, p5743_1]
                                        · have p5743_0 := h5743c.1
                                          have p5743_1 := h5743c.2.1
                                          have p5743_2 := h5743c.2.2.1
                                          have p5743_3 := h5743c.2.2.2
                                          linarith only [h5728, hlam, p5743_0]
                                        · have p5743_0 := h5743c.1
                                          have p5743_1 := h5743c.2.1
                                          have p5743_2 := h5743c.2.2.1
                                          have p5743_3 := h5743c.2.2.2
                                          linarith only [h5729, hlam, p5743_1]
                                        · have p5743_0 := h5743c.1
                                          have p5743_1 := h5743c.2.1
                                          have p5743_2 := h5743c.2.2.1
                                          have p5743_3 := h5743c.2.2.2
                                          linarith only [hlam, p5743_0]
                                      · linarith only [h1, h5505, h5730, h5738, h5742, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · linarith only [h1, h5505, h5730, h5738, h5741, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · linarith only [h1, h5505, h5730, h5738, h5740, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                · linarith only [h1, h5505, h5730, h5738, h5739, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h1, h5505, h5729, h5730, h5732, h5738, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h1, h5737, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h5505, h5732, h5736, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5776 | h5776
                    · linarith only [h0, h5507, h5776, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5778 | h5778
                      · linarith only [h0, h5509, h5778, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5780 | h5780
                        · linarith only [h0, h5672, h5780, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5782 | h5782
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5783 | h5783
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h5784 | h5784
                              · linarith only [h1, h5505, h5729, h5784, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h5786 | h5786
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h5787 | h5787
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5788 | h5788
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5789 | h5789
                                      · linarith only [h5505, h5729, h5782, h5789, hlam]
                                      · rcases h0bigk with h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c
                                        · have p5791_0 := h5791c.1
                                          have p5791_1 := h5791c.2.1
                                          have p5791_2 := h5791c.2.2.1
                                          have p5791_3 := h5791c.2.2.2
                                          linarith only [hlam, p5791_0]
                                        · have p5791_0 := h5791c.1
                                          have p5791_1 := h5791c.2.1
                                          have p5791_2 := h5791c.2.2.1
                                          have p5791_3 := h5791c.2.2.2
                                          linarith only [h1, h5776, hc02, hc23, hlam, hphi, p5791_1]
                                        · have p5791_0 := h5791c.1
                                          have p5791_1 := h5791c.2.1
                                          have p5791_2 := h5791c.2.2.1
                                          have p5791_3 := h5791c.2.2.2
                                          linarith only [h1, hlam, p5791_0]
                                        · have p5791_0 := h5791c.1
                                          have p5791_1 := h5791c.2.1
                                          have p5791_2 := h5791c.2.2.1
                                          have p5791_3 := h5791c.2.2.2
                                          linarith only [h1, h5776, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5791_1]
                                        · have p5791_0 := h5791c.1
                                          have p5791_1 := h5791c.2.1
                                          have p5791_2 := h5791c.2.2.1
                                          have p5791_3 := h5791c.2.2.2
                                          linarith only [h1, h5505, h5729, h5776, h5782, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5791_1]
                                        · have p5791_0 := h5791c.1
                                          have p5791_1 := h5791c.2.1
                                          have p5791_2 := h5791c.2.2.1
                                          have p5791_3 := h5791c.2.2.2
                                          linarith only [h0, hlam, p5791_0]
                                        · have p5791_0 := h5791c.1
                                          have p5791_1 := h5791c.2.1
                                          have p5791_2 := h5791c.2.2.1
                                          have p5791_3 := h5791c.2.2.2
                                          linarith only [hlam, p5791_0]
                                        · have p5791_0 := h5791c.1
                                          have p5791_1 := h5791c.2.1
                                          have p5791_2 := h5791c.2.2.1
                                          have p5791_3 := h5791c.2.2.2
                                          linarith only [h5507, hlam, p5791_0]
                                        · have p5791_0 := h5791c.1
                                          have p5791_1 := h5791c.2.1
                                          have p5791_2 := h5791c.2.2.1
                                          have p5791_3 := h5791c.2.2.2
                                          linarith only [h5509, hlam, p5791_1]
                                        · have p5791_0 := h5791c.1
                                          have p5791_1 := h5791c.2.1
                                          have p5791_2 := h5791c.2.2.1
                                          have p5791_3 := h5791c.2.2.2
                                          linarith only [h5672, hlam, p5791_0]
                                        · have p5791_0 := h5791c.1
                                          have p5791_1 := h5791c.2.1
                                          have p5791_2 := h5791c.2.2.1
                                          have p5791_3 := h5791c.2.2.2
                                          linarith only [h5506, hc03, hc15, hlam, hphi, ht0b, ht5b, p5791_1]
                                        · have p5791_0 := h5791c.1
                                          have p5791_1 := h5791c.2.1
                                          have p5791_2 := h5791c.2.2.1
                                          have p5791_3 := h5791c.2.2.2
                                          linarith only [h0, h1, h5776, hc12, hc23, hlam, hphi, p5791_1]
                                        · have p5791_0 := h5791c.1
                                          have p5791_1 := h5791c.2.1
                                          have p5791_2 := h5791c.2.2.1
                                          have p5791_3 := h5791c.2.2.2
                                          linarith only [hlam, p5791_0]
                                        · have p5791_0 := h5791c.1
                                          have p5791_1 := h5791c.2.1
                                          have p5791_2 := h5791c.2.2.1
                                          have p5791_3 := h5791c.2.2.2
                                          linarith only [h0, h1, h5509, h5776, hc12, hc23, hlam, hphi, p5791_1]
                                        · have p5791_0 := h5791c.1
                                          have p5791_1 := h5791c.2.1
                                          have p5791_2 := h5791c.2.2.1
                                          have p5791_3 := h5791c.2.2.2
                                          linarith only [h0, h1, h5509, h5729, h5776, hc12, hc23, hlam, hphi, p5791_1]
                                        · have p5791_0 := h5791c.1
                                          have p5791_1 := h5791c.2.1
                                          have p5791_2 := h5791c.2.2.1
                                          have p5791_3 := h5791c.2.2.2
                                          linarith only [h5505, hlam, p5791_0]
                                        · have p5791_0 := h5791c.1
                                          have p5791_1 := h5791c.2.1
                                          have p5791_2 := h5791c.2.2.1
                                          have p5791_3 := h5791c.2.2.2
                                          linarith only [h0, h5729, h5788, hc12, hc24, hlam, hphi, p5791_1]
                                        · have p5791_0 := h5791c.1
                                          have p5791_1 := h5791c.2.1
                                          have p5791_2 := h5791c.2.2.1
                                          have p5791_3 := h5791c.2.2.2
                                          linarith only [h5727, hlam, p5791_0]
                                        · have p5791_0 := h5791c.1
                                          have p5791_1 := h5791c.2.1
                                          have p5791_2 := h5791c.2.2.1
                                          have p5791_3 := h5791c.2.2.2
                                          linarith only [hlam, p5791_0]
                                        · have p5791_0 := h5791c.1
                                          have p5791_1 := h5791c.2.1
                                          have p5791_2 := h5791c.2.2.1
                                          have p5791_3 := h5791c.2.2.2
                                          linarith only [h5729, hlam, p5791_0]
                                        · have p5791_0 := h5791c.1
                                          have p5791_1 := h5791c.2.1
                                          have p5791_2 := h5791c.2.2.1
                                          have p5791_3 := h5791c.2.2.2
                                          linarith only [h5506, hlam, p5791_0]
                                        · have p5791_0 := h5791c.1
                                          have p5791_1 := h5791c.2.1
                                          have p5791_2 := h5791c.2.2.1
                                          have p5791_3 := h5791c.2.2.2
                                          linarith only [h0, h1, h5506, h5776, hc12, hc23, hlam, hphi, p5791_1]
                                        · have p5791_0 := h5791c.1
                                          have p5791_1 := h5791c.2.1
                                          have p5791_2 := h5791c.2.2.1
                                          have p5791_3 := h5791c.2.2.2
                                          linarith only [h5728, hlam, p5791_0]
                                        · have p5791_0 := h5791c.1
                                          have p5791_1 := h5791c.2.1
                                          have p5791_2 := h5791c.2.2.1
                                          have p5791_3 := h5791c.2.2.2
                                          linarith only [h1, h5506, h5776, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5791_1]
                                        · have p5791_0 := h5791c.1
                                          have p5791_1 := h5791c.2.1
                                          have p5791_2 := h5791c.2.2.1
                                          have p5791_3 := h5791c.2.2.2
                                          linarith only [hlam, p5791_0]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5817 | h5817
                                      · linarith only [h0, h5509, h5788, h5817, hc12, hc34, hlam, hphi, ht23]
                                      · rcases h0bigk with h5819c | h5819c | h5819c | h5819c | h5819c | h5819c | h5819c | h5819c | h5819c | h5819c | h5819c | h5819c | h5819c | h5819c | h5819c | h5819c | h5819c | h5819c | h5819c | h5819c | h5819c | h5819c | h5819c | h5819c | h5819c
                                        · have p5819_0 := h5819c.1
                                          have p5819_1 := h5819c.2.1
                                          have p5819_2 := h5819c.2.2.1
                                          have p5819_3 := h5819c.2.2.2
                                          linarith only [hlam, p5819_0]
                                        · have p5819_0 := h5819c.1
                                          have p5819_1 := h5819c.2.1
                                          have p5819_2 := h5819c.2.2.1
                                          have p5819_3 := h5819c.2.2.2
                                          linarith only [h0, h1, h5776, hc12, hc23, hlam, hphi, p5819_1]
                                        · have p5819_0 := h5819c.1
                                          have p5819_1 := h5819c.2.1
                                          have p5819_2 := h5819c.2.2.1
                                          have p5819_3 := h5819c.2.2.2
                                          linarith only [h1, hlam, p5819_0]
                                        · have p5819_0 := h5819c.1
                                          have p5819_1 := h5819c.2.1
                                          have p5819_2 := h5819c.2.2.1
                                          have p5819_3 := h5819c.2.2.2
                                          linarith only [h0, h1, h5509, h5776, hc12, hc23, hlam, hphi, p5819_1]
                                        · have p5819_0 := h5819c.1
                                          have p5819_1 := h5819c.2.1
                                          have p5819_2 := h5819c.2.2.1
                                          have p5819_3 := h5819c.2.2.2
                                          linarith only [h1, h5776, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5819_1]
                                        · have p5819_0 := h5819c.1
                                          have p5819_1 := h5819c.2.1
                                          have p5819_2 := h5819c.2.2.1
                                          have p5819_3 := h5819c.2.2.2
                                          linarith only [h0, hlam, p5819_0]
                                        · have p5819_0 := h5819c.1
                                          have p5819_1 := h5819c.2.1
                                          have p5819_2 := h5819c.2.2.1
                                          have p5819_3 := h5819c.2.2.2
                                          linarith only [hlam, p5819_0]
                                        · have p5819_0 := h5819c.1
                                          have p5819_1 := h5819c.2.1
                                          have p5819_2 := h5819c.2.2.1
                                          have p5819_3 := h5819c.2.2.2
                                          linarith only [h5507, hlam, p5819_0]
                                        · have p5819_0 := h5819c.1
                                          have p5819_1 := h5819c.2.1
                                          have p5819_2 := h5819c.2.2.1
                                          have p5819_3 := h5819c.2.2.2
                                          linarith only [h5509, hlam, p5819_1]
                                        · have p5819_0 := h5819c.1
                                          have p5819_1 := h5819c.2.1
                                          have p5819_2 := h5819c.2.2.1
                                          have p5819_3 := h5819c.2.2.2
                                          linarith only [h5672, hlam, p5819_0]
                                        · have p5819_0 := h5819c.1
                                          have p5819_1 := h5819c.2.1
                                          have p5819_2 := h5819c.2.2.1
                                          have p5819_3 := h5819c.2.2.2
                                          linarith only [h1, h5776, hc01, hc23, hlam, hphi, ht12, p5819_1]
                                        · have p5819_0 := h5819c.1
                                          have p5819_1 := h5819c.2.1
                                          have p5819_2 := h5819c.2.2.1
                                          have p5819_3 := h5819c.2.2.2
                                          linarith only [h0, h1, h5776, hc12, hc23, hlam, hphi, p5819_1]
                                        · have p5819_0 := h5819c.1
                                          have p5819_1 := h5819c.2.1
                                          have p5819_2 := h5819c.2.2.1
                                          have p5819_3 := h5819c.2.2.2
                                          linarith only [hlam, p5819_0]
                                        · have p5819_0 := h5819c.1
                                          have p5819_1 := h5819c.2.1
                                          have p5819_2 := h5819c.2.2.1
                                          have p5819_3 := h5819c.2.2.2
                                          linarith only [h0, h1, h5509, h5776, hc12, hc23, hlam, hphi, p5819_1]
                                        · have p5819_0 := h5819c.1
                                          have p5819_1 := h5819c.2.1
                                          have p5819_2 := h5819c.2.2.1
                                          have p5819_3 := h5819c.2.2.2
                                          linarith only [h1, h5506, h5776, h5778, h5784, hc12, hc23, hlam, hphi, p5819_1]
                                        · have p5819_0 := h5819c.1
                                          have p5819_1 := h5819c.2.1
                                          have p5819_2 := h5819c.2.2.1
                                          have p5819_3 := h5819c.2.2.2
                                          linarith only [h5505, hlam, p5819_0]
                                        · have p5819_0 := h5819c.1
                                          have p5819_1 := h5819c.2.1
                                          have p5819_2 := h5819c.2.2.1
                                          have p5819_3 := h5819c.2.2.2
                                          linarith only [h0, h1, h5505, h5776, hc12, hc23, hlam, hphi, p5819_1]
                                        · have p5819_0 := h5819c.1
                                          have p5819_1 := h5819c.2.1
                                          have p5819_2 := h5819c.2.2.1
                                          have p5819_3 := h5819c.2.2.2
                                          linarith only [h5727, hlam, p5819_0]
                                        · have p5819_0 := h5819c.1
                                          have p5819_1 := h5819c.2.1
                                          have p5819_2 := h5819c.2.2.1
                                          have p5819_3 := h5819c.2.2.2
                                          linarith only [hlam, p5819_0]
                                        · have p5819_0 := h5819c.1
                                          have p5819_1 := h5819c.2.1
                                          have p5819_2 := h5819c.2.2.1
                                          have p5819_3 := h5819c.2.2.2
                                          linarith only [h5729, hlam, p5819_0]
                                        · have p5819_0 := h5819c.1
                                          have p5819_1 := h5819c.2.1
                                          have p5819_2 := h5819c.2.2.1
                                          have p5819_3 := h5819c.2.2.2
                                          linarith only [h5506, hlam, p5819_0]
                                        · have p5819_0 := h5819c.1
                                          have p5819_1 := h5819c.2.1
                                          have p5819_2 := h5819c.2.2.1
                                          have p5819_3 := h5819c.2.2.2
                                          linarith only [h0, h1, h5506, h5776, hc12, hc23, hlam, hphi, p5819_1]
                                        · have p5819_0 := h5819c.1
                                          have p5819_1 := h5819c.2.1
                                          have p5819_2 := h5819c.2.2.1
                                          have p5819_3 := h5819c.2.2.2
                                          linarith only [h5728, hlam, p5819_0]
                                        · have p5819_0 := h5819c.1
                                          have p5819_1 := h5819c.2.1
                                          have p5819_2 := h5819c.2.2.1
                                          have p5819_3 := h5819c.2.2.2
                                          linarith only [h1, h5506, h5776, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5819_1]
                                        · have p5819_0 := h5819c.1
                                          have p5819_1 := h5819c.2.1
                                          have p5819_2 := h5819c.2.2.1
                                          have p5819_3 := h5819c.2.2.2
                                          linarith only [hlam, p5819_0]
                                  · linarith only [h0, h1, h5776, h5787, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h1, h5506, h5776, h5782, h5784, h5786, hlam]
                            · linarith only [h0, h1, h5783, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h5506, h5780, h5782, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h1, h5506, h5728, hlam]
              · linarith only [h1, h5505, h5727, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h5851 | h5851
        · linarith only [h0, h1, h5851, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h5853 | h5853
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5854 | h5854
            · linarith only [h0, h5506, h5854, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h5856 | h5856
              · rcases m.htr 0 3 5 (by decide) (by decide) with h5857 | h5857
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5858 | h5858
                  · linarith only [h0, h5506, h5853, h5858, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5860 | h5860
                    · linarith only [h0, h1, h5851, h5860, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5862 | h5862
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5863 | h5863
                        · linarith only [h0, h5506, h5854, h5863, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5865 | h5865
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5866 | h5866
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h5867 | h5867
                              · linarith only [h0, h5505, h5506, h5853, h5858, h5867, hlam]
                              · linarith only [h0, h5506, h5862, h5867, hc24, hc45, hlam, hphi]
                            · linarith only [h0, h1, h5857, h5862, h5866, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h0, h1, h5862, h5865, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h5851, h5853, h5862, hc12, hc23, hlam, hphi]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5873 | h5873
                  · linarith only [h0, h1, h5853, h5857, h5873, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5875 | h5875
                    · linarith only [h0, h1, h5851, h5875, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5877 | h5877
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5878 | h5878
                        · linarith only [h0, h5854, h5878, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5880 | h5880
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5881 | h5881
                            · linarith only [h0, h1, h5857, h5875, h5877, h5881, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h1, h5877, h5881, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1, h5877, h5880, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h5851, h5853, h5877, hc12, hc23, hlam, hphi]
              · linarith only [h0, h1, h5853, h5856, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5887 | h5887
            · linarith only [h5505, h5506, h5853, h5887, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h5889 | h5889
              · rcases m.htr 0 3 5 (by decide) (by decide) with h5890 | h5890
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5891 | h5891
                  · linarith only [h5505, h5506, h5891, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5893 | h5893
                    · linarith only [h0, h5851, h5893, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5895 | h5895
                      · linarith only [h0, h5853, h5895, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5897 | h5897
                        · linarith only [h0, h5506, h5887, h5897, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5899 | h5899
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5900 | h5900
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h5901 | h5901
                              · linarith only [h5505, h5506, h5853, h5891, h5900, h5901, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h5903 | h5903
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h5904 | h5904
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5905 | h5905
                                    · linarith only [h0, h5506, h5901, h5903, h5905, hc12, hc23, hlam, hphi]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5907 | h5907
                                      · linarith only [h5505, h5506, h5899, h5900, h5905, h5907, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                      · rcases h0bigk with h5909c | h5909c | h5909c | h5909c | h5909c | h5909c | h5909c | h5909c | h5909c | h5909c | h5909c | h5909c | h5909c | h5909c | h5909c | h5909c | h5909c | h5909c | h5909c | h5909c | h5909c | h5909c | h5909c | h5909c | h5909c
                                        · have p5909_0 := h5909c.1
                                          have p5909_1 := h5909c.2.1
                                          have p5909_2 := h5909c.2.2.1
                                          have p5909_3 := h5909c.2.2.2
                                          linarith only [hlam, p5909_0]
                                        · have p5909_0 := h5909c.1
                                          have p5909_1 := h5909c.2.1
                                          have p5909_2 := h5909c.2.2.1
                                          have p5909_3 := h5909c.2.2.2
                                          linarith only [h0, h5506, h5897, h5905, hc12, hc45, hlam, hphi, ht23, ht34, p5909_1]
                                        · have p5909_0 := h5909c.1
                                          have p5909_1 := h5909c.2.1
                                          have p5909_2 := h5909c.2.2.1
                                          have p5909_3 := h5909c.2.2.2
                                          linarith only [h1, hlam, p5909_0]
                                        · have p5909_0 := h5909c.1
                                          have p5909_1 := h5909c.2.1
                                          have p5909_2 := h5909c.2.2.1
                                          have p5909_3 := h5909c.2.2.2
                                          linarith only [h5506, h5897, h5905, hc04, hc45, hlam, hphi, p5909_1]
                                        · have p5909_0 := h5909c.1
                                          have p5909_1 := h5909c.2.1
                                          have p5909_2 := h5909c.2.2.1
                                          have p5909_3 := h5909c.2.2.2
                                          linarith only [h5506, hlam, p5909_1]
                                        · have p5909_0 := h5909c.1
                                          have p5909_1 := h5909c.2.1
                                          have p5909_2 := h5909c.2.2.1
                                          have p5909_3 := h5909c.2.2.2
                                          linarith only [h0, hlam, p5909_0]
                                        · have p5909_0 := h5909c.1
                                          have p5909_1 := h5909c.2.1
                                          have p5909_2 := h5909c.2.2.1
                                          have p5909_3 := h5909c.2.2.2
                                          linarith only [hlam, p5909_0]
                                        · have p5909_0 := h5909c.1
                                          have p5909_1 := h5909c.2.1
                                          have p5909_2 := h5909c.2.2.1
                                          have p5909_3 := h5909c.2.2.2
                                          linarith only [h5851, hlam, p5909_0]
                                        · have p5909_0 := h5909c.1
                                          have p5909_1 := h5909c.2.1
                                          have p5909_2 := h5909c.2.2.1
                                          have p5909_3 := h5909c.2.2.2
                                          linarith only [h5853, hlam, p5909_1]
                                        · have p5909_0 := h5909c.1
                                          have p5909_1 := h5909c.2.1
                                          have p5909_2 := h5909c.2.2.1
                                          have p5909_3 := h5909c.2.2.2
                                          linarith only [h5887, hlam, p5909_0]
                                        · have p5909_0 := h5909c.1
                                          have p5909_1 := h5909c.2.1
                                          have p5909_2 := h5909c.2.2.1
                                          have p5909_3 := h5909c.2.2.2
                                          linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5909_1]
                                        · have p5909_0 := h5909c.1
                                          have p5909_1 := h5909c.2.1
                                          have p5909_2 := h5909c.2.2.1
                                          have p5909_3 := h5909c.2.2.2
                                          linarith only [h0, h5851, hc12, hc23, hlam, hphi, p5909_1]
                                        · have p5909_0 := h5909c.1
                                          have p5909_1 := h5909c.2.1
                                          have p5909_2 := h5909c.2.2.1
                                          have p5909_3 := h5909c.2.2.2
                                          linarith only [hlam, p5909_0]
                                        · have p5909_0 := h5909c.1
                                          have p5909_1 := h5909c.2.1
                                          have p5909_2 := h5909c.2.2.1
                                          have p5909_3 := h5909c.2.2.2
                                          linarith only [h0, h5851, h5853, hc12, hc23, hlam, hphi, p5909_1]
                                        · have p5909_0 := h5909c.1
                                          have p5909_1 := h5909c.2.1
                                          have p5909_2 := h5909c.2.2.1
                                          have p5909_3 := h5909c.2.2.2
                                          linarith only [h0, h5506, h5851, hc12, hc23, hlam, hphi, p5909_1]
                                        · have p5909_0 := h5909c.1
                                          have p5909_1 := h5909c.2.1
                                          have p5909_2 := h5909c.2.2.1
                                          have p5909_3 := h5909c.2.2.2
                                          linarith only [h5505, hlam, p5909_0]
                                        · have p5909_0 := h5909c.1
                                          have p5909_1 := h5909c.2.1
                                          have p5909_2 := h5909c.2.2.1
                                          have p5909_3 := h5909c.2.2.2
                                          linarith only [h0, h1, h5505, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5909_1]
                                        · have p5909_0 := h5909c.1
                                          have p5909_1 := h5909c.2.1
                                          have p5909_2 := h5909c.2.2.1
                                          have p5909_3 := h5909c.2.2.2
                                          linarith only [h5889, hlam, p5909_0]
                                        · have p5909_0 := h5909c.1
                                          have p5909_1 := h5909c.2.1
                                          have p5909_2 := h5909c.2.2.1
                                          have p5909_3 := h5909c.2.2.2
                                          linarith only [hlam, p5909_0]
                                        · have p5909_0 := h5909c.1
                                          have p5909_1 := h5909c.2.1
                                          have p5909_2 := h5909c.2.2.1
                                          have p5909_3 := h5909c.2.2.2
                                          linarith only [h5891, hlam, p5909_0]
                                        · have p5909_0 := h5909c.1
                                          have p5909_1 := h5909c.2.1
                                          have p5909_2 := h5909c.2.2.1
                                          have p5909_3 := h5909c.2.2.2
                                          linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5909_1]
                                        · have p5909_0 := h5909c.1
                                          have p5909_1 := h5909c.2.1
                                          have p5909_2 := h5909c.2.2.1
                                          have p5909_3 := h5909c.2.2.2
                                          linarith only [h0, h5506, h5897, h5905, hc12, hc45, hlam, hphi, ht23, ht34, p5909_1]
                                        · have p5909_0 := h5909c.1
                                          have p5909_1 := h5909c.2.1
                                          have p5909_2 := h5909c.2.2.1
                                          have p5909_3 := h5909c.2.2.2
                                          linarith only [h5890, hlam, p5909_0]
                                        · have p5909_0 := h5909c.1
                                          have p5909_1 := h5909c.2.1
                                          have p5909_2 := h5909c.2.2.1
                                          have p5909_3 := h5909c.2.2.2
                                          linarith only [h5506, h5897, h5905, hc04, hc45, hlam, hphi, p5909_1]
                                        · have p5909_0 := h5909c.1
                                          have p5909_1 := h5909c.2.1
                                          have p5909_2 := h5909c.2.2.1
                                          have p5909_3 := h5909c.2.2.2
                                          linarith only [hlam, p5909_0]
                                  · linarith only [h1, h5890, h5893, h5904, hlam]
                                · linarith only [h1, h5505, h5893, h5895, h5903, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h1, h5890, h5900, hlam]
                          · linarith only [h1, h5505, h5895, h5899, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5939 | h5939
                  · linarith only [h1, h5505, h5890, h5939, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5941 | h5941
                    · linarith only [h0, h1, h5890, h5941, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5943 | h5943
                      · linarith only [h0, h5853, h5943, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5945 | h5945
                        · linarith only [h0, h5887, h5945, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5947 | h5947
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5948 | h5948
                            · linarith only [h0, h1, h5890, h5941, h5948, hc12, hc23, hlam, hphi]
                            · linarith only [h1, h5505, h5943, h5948, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h5505, h5943, h5947, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h5505, h5889, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h5953 | h5953
      · rcases m.htr 0 2 3 (by decide) (by decide) with h5954 | h5954
        · linarith only [h0, h1, h5954, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h5956 | h5956
          · linarith only [h0, h5505, h5956, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5958 | h5958
            · rcases m.htr 0 3 4 (by decide) (by decide) with h5959 | h5959
              · rcases m.htr 0 3 5 (by decide) (by decide) with h5960 | h5960
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5961 | h5961
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5962 | h5962
                    · linarith only [h0, h1, h5954, h5962, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5964 | h5964
                      · linarith only [h0, h5505, h5956, h5964, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5966 | h5966
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5967 | h5967
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5968 | h5968
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h5969 | h5969
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h5970 | h5970
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h5971 | h5971
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5972 | h5972
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5973 | h5973
                                      · rcases h0bigk with h5974c | h5974c | h5974c | h5974c | h5974c | h5974c | h5974c | h5974c | h5974c | h5974c | h5974c | h5974c | h5974c | h5974c | h5974c | h5974c | h5974c | h5974c | h5974c | h5974c | h5974c | h5974c | h5974c | h5974c | h5974c
                                        · have p5974_0 := h5974c.1
                                          have p5974_1 := h5974c.2.1
                                          have p5974_2 := h5974c.2.2.1
                                          have p5974_3 := h5974c.2.2.2
                                          linarith only [hlam, p5974_0]
                                        · have p5974_0 := h5974c.1
                                          have p5974_1 := h5974c.2.1
                                          have p5974_2 := h5974c.2.2.1
                                          have p5974_3 := h5974c.2.2.2
                                          linarith only [h5505, h5962, h5967, hc02, hc23, hlam, hphi, p5974_1]
                                        · have p5974_0 := h5974c.1
                                          have p5974_1 := h5974c.2.1
                                          have p5974_2 := h5974c.2.2.1
                                          have p5974_3 := h5974c.2.2.2
                                          linarith only [h1, hlam, p5974_0]
                                        · have p5974_0 := h5974c.1
                                          have p5974_1 := h5974c.2.1
                                          have p5974_2 := h5974c.2.2.1
                                          have p5974_3 := h5974c.2.2.2
                                          linarith only [h5505, hlam, p5974_1]
                                        · have p5974_0 := h5974c.1
                                          have p5974_1 := h5974c.2.1
                                          have p5974_2 := h5974c.2.2.1
                                          have p5974_3 := h5974c.2.2.2
                                          linarith only [h5505, h5962, h5967, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5974_1]
                                        · have p5974_0 := h5974c.1
                                          have p5974_1 := h5974c.2.1
                                          have p5974_2 := h5974c.2.2.1
                                          have p5974_3 := h5974c.2.2.2
                                          linarith only [h0, hlam, p5974_0]
                                        · have p5974_0 := h5974c.1
                                          have p5974_1 := h5974c.2.1
                                          have p5974_2 := h5974c.2.2.1
                                          have p5974_3 := h5974c.2.2.2
                                          linarith only [hlam, p5974_0]
                                        · have p5974_0 := h5974c.1
                                          have p5974_1 := h5974c.2.1
                                          have p5974_2 := h5974c.2.2.1
                                          have p5974_3 := h5974c.2.2.2
                                          linarith only [h5954, hlam, p5974_0]
                                        · have p5974_0 := h5974c.1
                                          have p5974_1 := h5974c.2.1
                                          have p5974_2 := h5974c.2.2.1
                                          have p5974_3 := h5974c.2.2.2
                                          linarith only [h5956, hlam, p5974_1]
                                        · have p5974_0 := h5974c.1
                                          have p5974_1 := h5974c.2.1
                                          have p5974_2 := h5974c.2.2.1
                                          have p5974_3 := h5974c.2.2.2
                                          linarith only [h0, h5505, h5953, h5962, h5967, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5974_1]
                                        · have p5974_0 := h5974c.1
                                          have p5974_1 := h5974c.2.1
                                          have p5974_2 := h5974c.2.2.1
                                          have p5974_3 := h5974c.2.2.2
                                          linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5974_1]
                                        · have p5974_0 := h5974c.1
                                          have p5974_1 := h5974c.2.1
                                          have p5974_2 := h5974c.2.2.1
                                          have p5974_3 := h5974c.2.2.2
                                          linarith only [h1, h5962, hc02, hc23, hlam, hphi, p5974_1]
                                        · have p5974_0 := h5974c.1
                                          have p5974_1 := h5974c.2.1
                                          have p5974_2 := h5974c.2.2.1
                                          have p5974_3 := h5974c.2.2.2
                                          linarith only [hlam, p5974_0]
                                        · have p5974_0 := h5974c.1
                                          have p5974_1 := h5974c.2.1
                                          have p5974_2 := h5974c.2.2.1
                                          have p5974_3 := h5974c.2.2.2
                                          linarith only [h0, h1, h5505, h5962, h5966, h5971, h5973, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5974_1]
                                        · have p5974_0 := h5974c.1
                                          have p5974_1 := h5974c.2.1
                                          have p5974_2 := h5974c.2.2.1
                                          have p5974_3 := h5974c.2.2.2
                                          rcases p5974_3 (m.d 0 1) (by simp) with h5989 | h5989
                                          · linarith only [h1, h5989, hlam]
                                          · linarith only [h5953, h5989, hlam]
                                        · have p5974_0 := h5974c.1
                                          have p5974_1 := h5974c.2.1
                                          have p5974_2 := h5974c.2.2.1
                                          have p5974_3 := h5974c.2.2.2
                                          linarith only [h0, h5966, h5971, h5973, hc04, hc45, hlam, hphi, ht0b, ht5b, p5974_1]
                                        · have p5974_0 := h5974c.1
                                          have p5974_1 := h5974c.2.1
                                          have p5974_2 := h5974c.2.2.1
                                          have p5974_3 := h5974c.2.2.2
                                          linarith only [h0, h5966, h5971, h5973, hc04, hc45, hlam, hphi, ht0b, ht5b, p5974_1]
                                        · have p5974_0 := h5974c.1
                                          have p5974_1 := h5974c.2.1
                                          have p5974_2 := h5974c.2.2.1
                                          have p5974_3 := h5974c.2.2.2
                                          linarith only [h5959, hlam, p5974_0]
                                        · have p5974_0 := h5974c.1
                                          have p5974_1 := h5974c.2.1
                                          have p5974_2 := h5974c.2.2.1
                                          have p5974_3 := h5974c.2.2.2
                                          linarith only [hlam, p5974_0]
                                        · have p5974_0 := h5974c.1
                                          have p5974_1 := h5974c.2.1
                                          have p5974_2 := h5974c.2.2.1
                                          have p5974_3 := h5974c.2.2.2
                                          rcases p5974_3 (m.d 0 1) (by simp) with h5996 | h5996
                                          · linarith only [h5505, h5996, hlam]
                                          · linarith only [h5953, h5996, hlam]
                                        · have p5974_0 := h5974c.1
                                          have p5974_1 := h5974c.2.1
                                          have p5974_2 := h5974c.2.2.1
                                          have p5974_3 := h5974c.2.2.2
                                          linarith only [h5953, hlam, p5974_0]
                                        · have p5974_0 := h5974c.1
                                          have p5974_1 := h5974c.2.1
                                          have p5974_2 := h5974c.2.2.1
                                          have p5974_3 := h5974c.2.2.2
                                          linarith only [h5958, hlam, p5974_1]
                                        · have p5974_0 := h5974c.1
                                          have p5974_1 := h5974c.2.1
                                          have p5974_2 := h5974c.2.2.1
                                          have p5974_3 := h5974c.2.2.2
                                          linarith only [h5960, hlam, p5974_0]
                                        · have p5974_0 := h5974c.1
                                          have p5974_1 := h5974c.2.1
                                          have p5974_2 := h5974c.2.2.1
                                          have p5974_3 := h5974c.2.2.2
                                          linarith only [h5961, hlam, p5974_1]
                                        · have p5974_0 := h5974c.1
                                          have p5974_1 := h5974c.2.1
                                          have p5974_2 := h5974c.2.2.1
                                          have p5974_3 := h5974c.2.2.2
                                          linarith only [hlam, p5974_0]
                                      · linarith only [h0, h5505, h5962, h5966, h5967, h5972, h5973, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · linarith only [h5505, h5953, h5956, h5967, h5969, h5972, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                  · linarith only [h0, h5505, h5962, h5967, h5971, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h0, h5505, h5962, h5966, h5967, h5970, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h0, h5505, h5966, h5969, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                            · linarith only [h0, h5505, h5966, h5967, h5968, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h1, h5959, h5967, hlam]
                        · linarith only [h0, h5505, h5958, h5964, h5966, hc12, hc24, hlam, hphi]
                  · linarith only [h5505, h5953, h5961, hlam]
                · linarith only [h0, h1, h5958, h5960, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h6014 | h6014
                · rcases m.htr 0 4 5 (by decide) (by decide) with h6015 | h6015
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h6016 | h6016
                    · linarith only [h0, h1, h5954, h6016, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h6018 | h6018
                      · linarith only [h0, h1, h5956, h5959, h6018, hc02, hc34, hlam, hphi, ht23]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h6020 | h6020
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h6021 | h6021
                          · linarith only [h0, h1, h5959, h6020, h6021, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h0, h1, h6020, h6021, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h0, h5505, h5958, h6018, h6020, hc12, hc24, hlam, hphi]
                  · linarith only [h0, h5505, h5958, h6015, hlam]
                · linarith only [h0, h1, h5958, h6014, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6027 | h6027
              · rcases m.htr 0 3 5 (by decide) (by decide) with h6028 | h6028
                · rcases m.htr 0 4 5 (by decide) (by decide) with h6029 | h6029
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h6030 | h6030
                    · linarith only [h0, h1, h5954, h6030, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h6032 | h6032
                      · linarith only [h0, h5956, h6032, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h6034 | h6034
                        · linarith only [h0, h5958, h6034, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h6036 | h6036
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h6037 | h6037
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h6038 | h6038
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h6039 | h6039
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h6040 | h6040
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6041 | h6041
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6042 | h6042
                                      · rcases h0bigk with h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c
                                        · have p6043_0 := h6043c.1
                                          have p6043_1 := h6043c.2.1
                                          have p6043_2 := h6043c.2.2.1
                                          have p6043_3 := h6043c.2.2.2
                                          linarith only [hlam, p6043_0]
                                        · have p6043_0 := h6043c.1
                                          have p6043_1 := h6043c.2.1
                                          have p6043_2 := h6043c.2.2.1
                                          have p6043_3 := h6043c.2.2.2
                                          linarith only [h5505, h6030, h6036, hc02, hc23, hlam, hphi, p6043_1]
                                        · have p6043_0 := h6043c.1
                                          have p6043_1 := h6043c.2.1
                                          have p6043_2 := h6043c.2.2.1
                                          have p6043_3 := h6043c.2.2.2
                                          linarith only [h1, hlam, p6043_0]
                                        · have p6043_0 := h6043c.1
                                          have p6043_1 := h6043c.2.1
                                          have p6043_2 := h6043c.2.2.1
                                          have p6043_3 := h6043c.2.2.2
                                          linarith only [h5505, hlam, p6043_1]
                                        · have p6043_0 := h6043c.1
                                          have p6043_1 := h6043c.2.1
                                          have p6043_2 := h6043c.2.2.1
                                          have p6043_3 := h6043c.2.2.2
                                          linarith only [h5505, h6030, h6036, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p6043_1]
                                        · have p6043_0 := h6043c.1
                                          have p6043_1 := h6043c.2.1
                                          have p6043_2 := h6043c.2.2.1
                                          have p6043_3 := h6043c.2.2.2
                                          linarith only [h0, hlam, p6043_0]
                                        · have p6043_0 := h6043c.1
                                          have p6043_1 := h6043c.2.1
                                          have p6043_2 := h6043c.2.2.1
                                          have p6043_3 := h6043c.2.2.2
                                          linarith only [hlam, p6043_0]
                                        · have p6043_0 := h6043c.1
                                          have p6043_1 := h6043c.2.1
                                          have p6043_2 := h6043c.2.2.1
                                          have p6043_3 := h6043c.2.2.2
                                          linarith only [h5954, hlam, p6043_0]
                                        · have p6043_0 := h6043c.1
                                          have p6043_1 := h6043c.2.1
                                          have p6043_2 := h6043c.2.2.1
                                          have p6043_3 := h6043c.2.2.2
                                          linarith only [h5956, hlam, p6043_1]
                                        · have p6043_0 := h6043c.1
                                          have p6043_1 := h6043c.2.1
                                          have p6043_2 := h6043c.2.2.1
                                          have p6043_3 := h6043c.2.2.2
                                          linarith only [h5958, hlam, p6043_0]
                                        · have p6043_0 := h6043c.1
                                          have p6043_1 := h6043c.2.1
                                          have p6043_2 := h6043c.2.2.1
                                          have p6043_3 := h6043c.2.2.2
                                          linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6043_1]
                                        · have p6043_0 := h6043c.1
                                          have p6043_1 := h6043c.2.1
                                          have p6043_2 := h6043c.2.2.1
                                          have p6043_3 := h6043c.2.2.2
                                          linarith only [h0, h1, h6030, hc12, hc23, hlam, hphi, p6043_1]
                                        · have p6043_0 := h6043c.1
                                          have p6043_1 := h6043c.2.1
                                          have p6043_2 := h6043c.2.2.1
                                          have p6043_3 := h6043c.2.2.2
                                          linarith only [hlam, p6043_0]
                                        · have p6043_0 := h6043c.1
                                          have p6043_1 := h6043c.2.1
                                          have p6043_2 := h6043c.2.2.1
                                          have p6043_3 := h6043c.2.2.2
                                          linarith only [h0, h1, h5505, h6030, hc12, hc23, hlam, hphi, p6043_1]
                                        · have p6043_0 := h6043c.1
                                          have p6043_1 := h6043c.2.1
                                          have p6043_2 := h6043c.2.2.1
                                          have p6043_3 := h6043c.2.2.2
                                          linarith only [h0, h1, h5958, h6030, hc12, hc23, hlam, hphi, p6043_1]
                                        · have p6043_0 := h6043c.1
                                          have p6043_1 := h6043c.2.1
                                          have p6043_2 := h6043c.2.2.1
                                          have p6043_3 := h6043c.2.2.2
                                          linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6043_1]
                                        · have p6043_0 := h6043c.1
                                          have p6043_1 := h6043c.2.1
                                          have p6043_2 := h6043c.2.2.1
                                          have p6043_3 := h6043c.2.2.2
                                          linarith only [h0, h5505, h6030, h6036, hc12, hc23, hlam, hphi, p6043_1]
                                        · have p6043_0 := h6043c.1
                                          have p6043_1 := h6043c.2.1
                                          have p6043_2 := h6043c.2.2.1
                                          have p6043_3 := h6043c.2.2.2
                                          linarith only [h6027, hlam, p6043_0]
                                        · have p6043_0 := h6043c.1
                                          have p6043_1 := h6043c.2.1
                                          have p6043_2 := h6043c.2.2.1
                                          have p6043_3 := h6043c.2.2.2
                                          linarith only [hlam, p6043_0]
                                        · have p6043_0 := h6043c.1
                                          have p6043_1 := h6043c.2.1
                                          have p6043_2 := h6043c.2.2.1
                                          have p6043_3 := h6043c.2.2.2
                                          linarith only [h0, h5505, h5958, h6030, h6036, hc12, hc23, hlam, hphi, p6043_1]
                                        · have p6043_0 := h6043c.1
                                          have p6043_1 := h6043c.2.1
                                          have p6043_2 := h6043c.2.2.1
                                          have p6043_3 := h6043c.2.2.2
                                          linarith only [h5953, hlam, p6043_0]
                                        · have p6043_0 := h6043c.1
                                          have p6043_1 := h6043c.2.1
                                          have p6043_2 := h6043c.2.2.1
                                          have p6043_3 := h6043c.2.2.2
                                          linarith only [h0, h1, h5953, h6030, hc12, hc23, hlam, hphi, p6043_1]
                                        · have p6043_0 := h6043c.1
                                          have p6043_1 := h6043c.2.1
                                          have p6043_2 := h6043c.2.2.1
                                          have p6043_3 := h6043c.2.2.2
                                          linarith only [h6028, hlam, p6043_0]
                                        · have p6043_0 := h6043c.1
                                          have p6043_1 := h6043c.2.1
                                          have p6043_2 := h6043c.2.2.1
                                          have p6043_3 := h6043c.2.2.2
                                          linarith only [h6029, hlam, p6043_1]
                                        · have p6043_0 := h6043c.1
                                          have p6043_1 := h6043c.2.1
                                          have p6043_2 := h6043c.2.2.1
                                          have p6043_3 := h6043c.2.2.2
                                          linarith only [hlam, p6043_0]
                                      · rcases h0bigk with h6069c | h6069c | h6069c | h6069c | h6069c | h6069c | h6069c | h6069c | h6069c | h6069c | h6069c | h6069c | h6069c | h6069c | h6069c | h6069c | h6069c | h6069c | h6069c | h6069c | h6069c | h6069c | h6069c | h6069c | h6069c
                                        · have p6069_0 := h6069c.1
                                          have p6069_1 := h6069c.2.1
                                          have p6069_2 := h6069c.2.2.1
                                          have p6069_3 := h6069c.2.2.2
                                          linarith only [hlam, p6069_0]
                                        · have p6069_0 := h6069c.1
                                          have p6069_1 := h6069c.2.1
                                          have p6069_2 := h6069c.2.2.1
                                          have p6069_3 := h6069c.2.2.2
                                          linarith only [h0, h5505, h6030, h6036, hc12, hc23, hlam, hphi, p6069_1]
                                        · have p6069_0 := h6069c.1
                                          have p6069_1 := h6069c.2.1
                                          have p6069_2 := h6069c.2.2.1
                                          have p6069_3 := h6069c.2.2.2
                                          linarith only [h1, hlam, p6069_0]
                                        · have p6069_0 := h6069c.1
                                          have p6069_1 := h6069c.2.1
                                          have p6069_2 := h6069c.2.2.1
                                          have p6069_3 := h6069c.2.2.2
                                          linarith only [h5505, hlam, p6069_1]
                                        · have p6069_0 := h6069c.1
                                          have p6069_1 := h6069c.2.1
                                          have p6069_2 := h6069c.2.2.1
                                          have p6069_3 := h6069c.2.2.2
                                          linarith only [h5505, h6030, h6036, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p6069_1]
                                        · have p6069_0 := h6069c.1
                                          have p6069_1 := h6069c.2.1
                                          have p6069_2 := h6069c.2.2.1
                                          have p6069_3 := h6069c.2.2.2
                                          linarith only [h0, hlam, p6069_0]
                                        · have p6069_0 := h6069c.1
                                          have p6069_1 := h6069c.2.1
                                          have p6069_2 := h6069c.2.2.1
                                          have p6069_3 := h6069c.2.2.2
                                          linarith only [hlam, p6069_0]
                                        · have p6069_0 := h6069c.1
                                          have p6069_1 := h6069c.2.1
                                          have p6069_2 := h6069c.2.2.1
                                          have p6069_3 := h6069c.2.2.2
                                          linarith only [h5954, hlam, p6069_0]
                                        · have p6069_0 := h6069c.1
                                          have p6069_1 := h6069c.2.1
                                          have p6069_2 := h6069c.2.2.1
                                          have p6069_3 := h6069c.2.2.2
                                          linarith only [h5956, hlam, p6069_1]
                                        · have p6069_0 := h6069c.1
                                          have p6069_1 := h6069c.2.1
                                          have p6069_2 := h6069c.2.2.1
                                          have p6069_3 := h6069c.2.2.2
                                          linarith only [h5958, hlam, p6069_0]
                                        · have p6069_0 := h6069c.1
                                          have p6069_1 := h6069c.2.1
                                          have p6069_2 := h6069c.2.2.1
                                          have p6069_3 := h6069c.2.2.2
                                          linarith only [h1, h6030, hc01, hc23, hlam, hphi, ht12, p6069_1]
                                        · have p6069_0 := h6069c.1
                                          have p6069_1 := h6069c.2.1
                                          have p6069_2 := h6069c.2.2.1
                                          have p6069_3 := h6069c.2.2.2
                                          linarith only [h0, h1, h6030, hc12, hc23, hlam, hphi, p6069_1]
                                        · have p6069_0 := h6069c.1
                                          have p6069_1 := h6069c.2.1
                                          have p6069_2 := h6069c.2.2.1
                                          have p6069_3 := h6069c.2.2.2
                                          linarith only [hlam, p6069_0]
                                        · have p6069_0 := h6069c.1
                                          have p6069_1 := h6069c.2.1
                                          have p6069_2 := h6069c.2.2.1
                                          have p6069_3 := h6069c.2.2.2
                                          linarith only [h1, h5505, h5953, h6030, h6038, h6042, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6069_1]
                                        · have p6069_0 := h6069c.1
                                          have p6069_1 := h6069c.2.1
                                          have p6069_2 := h6069c.2.2.1
                                          have p6069_3 := h6069c.2.2.2
                                          linarith only [h1, h5953, h6030, h6038, h6042, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6069_1]
                                        · have p6069_0 := h6069c.1
                                          have p6069_1 := h6069c.2.1
                                          have p6069_2 := h6069c.2.2.1
                                          have p6069_3 := h6069c.2.2.2
                                          linarith only [h5953, h6038, h6042, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p6069_1]
                                        · have p6069_0 := h6069c.1
                                          have p6069_1 := h6069c.2.1
                                          have p6069_2 := h6069c.2.2.1
                                          have p6069_3 := h6069c.2.2.2
                                          linarith only [h0, h5505, h6030, h6036, hc12, hc23, hlam, hphi, p6069_1]
                                        · have p6069_0 := h6069c.1
                                          have p6069_1 := h6069c.2.1
                                          have p6069_2 := h6069c.2.2.1
                                          have p6069_3 := h6069c.2.2.2
                                          linarith only [h6027, hlam, p6069_0]
                                        · have p6069_0 := h6069c.1
                                          have p6069_1 := h6069c.2.1
                                          have p6069_2 := h6069c.2.2.1
                                          have p6069_3 := h6069c.2.2.2
                                          linarith only [hlam, p6069_0]
                                        · have p6069_0 := h6069c.1
                                          have p6069_1 := h6069c.2.1
                                          have p6069_2 := h6069c.2.2.1
                                          have p6069_3 := h6069c.2.2.2
                                          linarith only [h5505, h5953, h6030, h6036, h6038, h6042, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6069_1]
                                        · have p6069_0 := h6069c.1
                                          have p6069_1 := h6069c.2.1
                                          have p6069_2 := h6069c.2.2.1
                                          have p6069_3 := h6069c.2.2.2
                                          linarith only [h5953, hlam, p6069_0]
                                        · have p6069_0 := h6069c.1
                                          have p6069_1 := h6069c.2.1
                                          have p6069_2 := h6069c.2.2.1
                                          have p6069_3 := h6069c.2.2.2
                                          linarith only [h0, h1, h5953, h6030, hc12, hc23, hlam, hphi, p6069_1]
                                        · have p6069_0 := h6069c.1
                                          have p6069_1 := h6069c.2.1
                                          have p6069_2 := h6069c.2.2.1
                                          have p6069_3 := h6069c.2.2.2
                                          linarith only [h6028, hlam, p6069_0]
                                        · have p6069_0 := h6069c.1
                                          have p6069_1 := h6069c.2.1
                                          have p6069_2 := h6069c.2.2.1
                                          have p6069_3 := h6069c.2.2.2
                                          linarith only [h6029, hlam, p6069_1]
                                        · have p6069_0 := h6069c.1
                                          have p6069_1 := h6069c.2.1
                                          have p6069_2 := h6069c.2.2.1
                                          have p6069_3 := h6069c.2.2.2
                                          linarith only [hlam, p6069_0]
                                    · linarith only [h0, h5505, h6032, h6041, hc12, hc45, hlam, hphi, ht23, ht34]
                                  · linarith only [h5505, h5953, h6030, h6034, h6036, h6040, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h5505, h5953, h6030, h6034, h6036, h6039, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h5505, h5953, h6034, h6038, hc12, hc45, hlam, hphi, ht23, ht34]
                            · linarith only [h5505, h5953, h6034, h6036, h6037, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h6027, h6036, hlam]
                  · linarith only [h5505, h5953, h6029, hlam]
                · linarith only [h1, h5953, h6028, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h6103 | h6103
                · rcases m.htr 0 4 5 (by decide) (by decide) with h6104 | h6104
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h6105 | h6105
                    · linarith only [h0, h1, h6027, h6105, hc23, hc34, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h6107 | h6107
                      · linarith only [h0, h5956, h6107, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h6109 | h6109
                        · linarith only [h0, h5958, h6109, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h6111 | h6111
                          · linarith only [h1, h5953, h6027, h6105, h6109, h6111, hc12, hc23, hlam, hphi]
                          · linarith only [h1, h5953, h6109, h6111, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h1, h5953, h6027, h6104, hlam]
                · linarith only [h1, h5953, h6103, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h6116 | h6116
        · linarith only [h0, h1, h6116, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h6118 | h6118
          · linarith only [h0, h5505, h6118, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h6120 | h6120
            · linarith only [h0, h5953, h6120, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6122 | h6122
              · rcases m.htr 0 3 5 (by decide) (by decide) with h6123 | h6123
                · rcases m.htr 0 4 5 (by decide) (by decide) with h6124 | h6124
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h6125 | h6125
                    · linarith only [h0, h1, h6116, h6125, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h6127 | h6127
                      · linarith only [h0, h5953, h6118, h6124, h6127, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h6129 | h6129
                        · linarith only [h0, h5953, h6120, h6129, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h6131 | h6131
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h6132 | h6132
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h6133 | h6133
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h6134 | h6134
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h6135 | h6135
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6136 | h6136
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6137 | h6137
                                      · rcases h0bigk with h6138c | h6138c | h6138c | h6138c | h6138c | h6138c | h6138c | h6138c | h6138c | h6138c | h6138c | h6138c | h6138c | h6138c | h6138c | h6138c | h6138c | h6138c | h6138c | h6138c | h6138c | h6138c | h6138c | h6138c | h6138c
                                        · have p6138_0 := h6138c.1
                                          have p6138_1 := h6138c.2.1
                                          have p6138_2 := h6138c.2.2.1
                                          have p6138_3 := h6138c.2.2.2
                                          linarith only [hlam, p6138_0]
                                        · have p6138_0 := h6138c.1
                                          have p6138_1 := h6138c.2.1
                                          have p6138_2 := h6138c.2.2.1
                                          have p6138_3 := h6138c.2.2.2
                                          linarith only [h5953, h6125, h6131, h6133, hc02, hc23, hlam, hphi, p6138_1]
                                        · have p6138_0 := h6138c.1
                                          have p6138_1 := h6138c.2.1
                                          have p6138_2 := h6138c.2.2.1
                                          have p6138_3 := h6138c.2.2.2
                                          linarith only [h1, hlam, p6138_0]
                                        · have p6138_0 := h6138c.1
                                          have p6138_1 := h6138c.2.1
                                          have p6138_2 := h6138c.2.2.1
                                          have p6138_3 := h6138c.2.2.2
                                          linarith only [h5505, hlam, p6138_1]
                                        · have p6138_0 := h6138c.1
                                          have p6138_1 := h6138c.2.1
                                          have p6138_2 := h6138c.2.2.1
                                          have p6138_3 := h6138c.2.2.2
                                          linarith only [h5953, hlam, p6138_1]
                                        · have p6138_0 := h6138c.1
                                          have p6138_1 := h6138c.2.1
                                          have p6138_2 := h6138c.2.2.1
                                          have p6138_3 := h6138c.2.2.2
                                          linarith only [h0, hlam, p6138_0]
                                        · have p6138_0 := h6138c.1
                                          have p6138_1 := h6138c.2.1
                                          have p6138_2 := h6138c.2.2.1
                                          have p6138_3 := h6138c.2.2.2
                                          linarith only [hlam, p6138_0]
                                        · have p6138_0 := h6138c.1
                                          have p6138_1 := h6138c.2.1
                                          have p6138_2 := h6138c.2.2.1
                                          have p6138_3 := h6138c.2.2.2
                                          linarith only [h6116, hlam, p6138_0]
                                        · have p6138_0 := h6138c.1
                                          have p6138_1 := h6138c.2.1
                                          have p6138_2 := h6138c.2.2.1
                                          have p6138_3 := h6138c.2.2.2
                                          linarith only [h6118, hlam, p6138_1]
                                        · have p6138_0 := h6138c.1
                                          have p6138_1 := h6138c.2.1
                                          have p6138_2 := h6138c.2.2.1
                                          have p6138_3 := h6138c.2.2.2
                                          linarith only [h6120, hlam, p6138_0]
                                        · have p6138_0 := h6138c.1
                                          have p6138_1 := h6138c.2.1
                                          have p6138_2 := h6138c.2.2.1
                                          have p6138_3 := h6138c.2.2.2
                                          linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6138_1]
                                        · have p6138_0 := h6138c.1
                                          have p6138_1 := h6138c.2.1
                                          have p6138_2 := h6138c.2.2.1
                                          have p6138_3 := h6138c.2.2.2
                                          linarith only [h0, h1, h6125, hc12, hc23, hlam, hphi, p6138_1]
                                        · have p6138_0 := h6138c.1
                                          have p6138_1 := h6138c.2.1
                                          have p6138_2 := h6138c.2.2.1
                                          have p6138_3 := h6138c.2.2.2
                                          linarith only [hlam, p6138_0]
                                        · have p6138_0 := h6138c.1
                                          have p6138_1 := h6138c.2.1
                                          have p6138_2 := h6138c.2.2.1
                                          have p6138_3 := h6138c.2.2.2
                                          linarith only [h0, h1, h5953, h6124, h6125, hc12, hc23, hlam, hphi, p6138_1]
                                        · have p6138_0 := h6138c.1
                                          have p6138_1 := h6138c.2.1
                                          have p6138_2 := h6138c.2.2.1
                                          have p6138_3 := h6138c.2.2.2
                                          linarith only [h0, h1, h5953, h6125, hc12, hc23, hlam, hphi, p6138_1]
                                        · have p6138_0 := h6138c.1
                                          have p6138_1 := h6138c.2.1
                                          have p6138_2 := h6138c.2.2.1
                                          have p6138_3 := h6138c.2.2.2
                                          linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6138_1]
                                        · have p6138_0 := h6138c.1
                                          have p6138_1 := h6138c.2.1
                                          have p6138_2 := h6138c.2.2.1
                                          have p6138_3 := h6138c.2.2.2
                                          linarith only [h0, h5505, h6127, hc12, hc24, hlam, hphi, p6138_1]
                                        · have p6138_0 := h6138c.1
                                          have p6138_1 := h6138c.2.1
                                          have p6138_2 := h6138c.2.2.1
                                          have p6138_3 := h6138c.2.2.2
                                          linarith only [h6122, hlam, p6138_0]
                                        · have p6138_0 := h6138c.1
                                          have p6138_1 := h6138c.2.1
                                          have p6138_2 := h6138c.2.2.1
                                          have p6138_3 := h6138c.2.2.2
                                          linarith only [hlam, p6138_0]
                                        · have p6138_0 := h6138c.1
                                          have p6138_1 := h6138c.2.1
                                          have p6138_2 := h6138c.2.2.1
                                          have p6138_3 := h6138c.2.2.2
                                          linarith only [h0, h1, h5953, h6122, h6125, hc12, hc23, hlam, hphi, p6138_1]
                                        · have p6138_0 := h6138c.1
                                          have p6138_1 := h6138c.2.1
                                          have p6138_2 := h6138c.2.2.1
                                          have p6138_3 := h6138c.2.2.2
                                          linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6138_1]
                                        · have p6138_0 := h6138c.1
                                          have p6138_1 := h6138c.2.1
                                          have p6138_2 := h6138c.2.2.1
                                          have p6138_3 := h6138c.2.2.2
                                          linarith only [h0, h5953, h6129, hc12, hc25, hlam, hphi, p6138_1]
                                        · have p6138_0 := h6138c.1
                                          have p6138_1 := h6138c.2.1
                                          have p6138_2 := h6138c.2.2.1
                                          have p6138_3 := h6138c.2.2.2
                                          linarith only [h6123, hlam, p6138_0]
                                        · have p6138_0 := h6138c.1
                                          have p6138_1 := h6138c.2.1
                                          have p6138_2 := h6138c.2.2.1
                                          have p6138_3 := h6138c.2.2.2
                                          linarith only [h6124, hlam, p6138_1]
                                        · have p6138_0 := h6138c.1
                                          have p6138_1 := h6138c.2.1
                                          have p6138_2 := h6138c.2.2.1
                                          have p6138_3 := h6138c.2.2.2
                                          linarith only [hlam, p6138_0]
                                      · rcases h0bigk with h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c
                                        · have p6164_0 := h6164c.1
                                          have p6164_1 := h6164c.2.1
                                          have p6164_2 := h6164c.2.2.1
                                          have p6164_3 := h6164c.2.2.2
                                          linarith only [hlam, p6164_0]
                                        · have p6164_0 := h6164c.1
                                          have p6164_1 := h6164c.2.1
                                          have p6164_2 := h6164c.2.2.1
                                          have p6164_3 := h6164c.2.2.2
                                          linarith only [h0, h1, h6125, hc12, hc23, hlam, hphi, p6164_1]
                                        · have p6164_0 := h6164c.1
                                          have p6164_1 := h6164c.2.1
                                          have p6164_2 := h6164c.2.2.1
                                          have p6164_3 := h6164c.2.2.2
                                          linarith only [h1, hlam, p6164_0]
                                        · have p6164_0 := h6164c.1
                                          have p6164_1 := h6164c.2.1
                                          have p6164_2 := h6164c.2.2.1
                                          have p6164_3 := h6164c.2.2.2
                                          linarith only [h5505, hlam, p6164_1]
                                        · have p6164_0 := h6164c.1
                                          have p6164_1 := h6164c.2.1
                                          have p6164_2 := h6164c.2.2.1
                                          have p6164_3 := h6164c.2.2.2
                                          linarith only [h5953, hlam, p6164_1]
                                        · have p6164_0 := h6164c.1
                                          have p6164_1 := h6164c.2.1
                                          have p6164_2 := h6164c.2.2.1
                                          have p6164_3 := h6164c.2.2.2
                                          linarith only [h0, hlam, p6164_0]
                                        · have p6164_0 := h6164c.1
                                          have p6164_1 := h6164c.2.1
                                          have p6164_2 := h6164c.2.2.1
                                          have p6164_3 := h6164c.2.2.2
                                          linarith only [hlam, p6164_0]
                                        · have p6164_0 := h6164c.1
                                          have p6164_1 := h6164c.2.1
                                          have p6164_2 := h6164c.2.2.1
                                          have p6164_3 := h6164c.2.2.2
                                          linarith only [h6116, hlam, p6164_0]
                                        · have p6164_0 := h6164c.1
                                          have p6164_1 := h6164c.2.1
                                          have p6164_2 := h6164c.2.2.1
                                          have p6164_3 := h6164c.2.2.2
                                          linarith only [h6118, hlam, p6164_1]
                                        · have p6164_0 := h6164c.1
                                          have p6164_1 := h6164c.2.1
                                          have p6164_2 := h6164c.2.2.1
                                          have p6164_3 := h6164c.2.2.2
                                          linarith only [h6120, hlam, p6164_0]
                                        · have p6164_0 := h6164c.1
                                          have p6164_1 := h6164c.2.1
                                          have p6164_2 := h6164c.2.2.1
                                          have p6164_3 := h6164c.2.2.2
                                          linarith only [h1, h6125, hc01, hc23, hlam, hphi, ht12, p6164_1]
                                        · have p6164_0 := h6164c.1
                                          have p6164_1 := h6164c.2.1
                                          have p6164_2 := h6164c.2.2.1
                                          have p6164_3 := h6164c.2.2.2
                                          linarith only [h0, h1, h6125, hc12, hc23, hlam, hphi, p6164_1]
                                        · have p6164_0 := h6164c.1
                                          have p6164_1 := h6164c.2.1
                                          have p6164_2 := h6164c.2.2.1
                                          have p6164_3 := h6164c.2.2.2
                                          linarith only [hlam, p6164_0]
                                        · have p6164_0 := h6164c.1
                                          have p6164_1 := h6164c.2.1
                                          have p6164_2 := h6164c.2.2.1
                                          have p6164_3 := h6164c.2.2.2
                                          linarith only [h1, h6124, h6125, h6137, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6164_1]
                                        · have p6164_0 := h6164c.1
                                          have p6164_1 := h6164c.2.1
                                          have p6164_2 := h6164c.2.2.1
                                          have p6164_3 := h6164c.2.2.2
                                          linarith only [h0, h1, h5953, h6125, hc12, hc23, hlam, hphi, p6164_1]
                                        · have p6164_0 := h6164c.1
                                          have p6164_1 := h6164c.2.1
                                          have p6164_2 := h6164c.2.2.1
                                          have p6164_3 := h6164c.2.2.2
                                          linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6164_1]
                                        · have p6164_0 := h6164c.1
                                          have p6164_1 := h6164c.2.1
                                          have p6164_2 := h6164c.2.2.1
                                          have p6164_3 := h6164c.2.2.2
                                          linarith only [h0, h5505, h6125, h6131, hc12, hc23, hlam, hphi, p6164_1]
                                        · have p6164_0 := h6164c.1
                                          have p6164_1 := h6164c.2.1
                                          have p6164_2 := h6164c.2.2.1
                                          have p6164_3 := h6164c.2.2.2
                                          linarith only [h6122, hlam, p6164_0]
                                        · have p6164_0 := h6164c.1
                                          have p6164_1 := h6164c.2.1
                                          have p6164_2 := h6164c.2.2.1
                                          have p6164_3 := h6164c.2.2.2
                                          linarith only [hlam, p6164_0]
                                        · have p6164_0 := h6164c.1
                                          have p6164_1 := h6164c.2.1
                                          have p6164_2 := h6164c.2.2.1
                                          have p6164_3 := h6164c.2.2.2
                                          linarith only [h0, h5505, h5953, h6125, h6131, hc12, hc23, hlam, hphi, p6164_1]
                                        · have p6164_0 := h6164c.1
                                          have p6164_1 := h6164c.2.1
                                          have p6164_2 := h6164c.2.2.1
                                          have p6164_3 := h6164c.2.2.2
                                          linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6164_1]
                                        · have p6164_0 := h6164c.1
                                          have p6164_1 := h6164c.2.1
                                          have p6164_2 := h6164c.2.2.1
                                          have p6164_3 := h6164c.2.2.2
                                          linarith only [h0, h5953, h6125, h6131, h6133, hc12, hc23, hlam, hphi, p6164_1]
                                        · have p6164_0 := h6164c.1
                                          have p6164_1 := h6164c.2.1
                                          have p6164_2 := h6164c.2.2.1
                                          have p6164_3 := h6164c.2.2.2
                                          linarith only [h6123, hlam, p6164_0]
                                        · have p6164_0 := h6164c.1
                                          have p6164_1 := h6164c.2.1
                                          have p6164_2 := h6164c.2.2.1
                                          have p6164_3 := h6164c.2.2.2
                                          linarith only [h6124, hlam, p6164_1]
                                        · have p6164_0 := h6164c.1
                                          have p6164_1 := h6164c.2.1
                                          have p6164_2 := h6164c.2.2.1
                                          have p6164_3 := h6164c.2.2.2
                                          linarith only [hlam, p6164_0]
                                    · linarith only [h6118, h6124, h6136, hlam]
                                  · linarith only [h0, h1, h6125, h6135, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h0, h1, h6125, h6134, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h0, h5505, h6124, h6133, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                            · linarith only [h1, h6123, h6132, hlam]
                          · linarith only [h1, h6122, h6131, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h6196 | h6196
                    · linarith only [h0, h5505, h6124, h6196, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h6198 | h6198
                      · linarith only [h0, h5505, h6124, h6198, hc24, hc45, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h6200 | h6200
                        · linarith only [h0, h6120, h6200, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h6202 | h6202
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h6203 | h6203
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h6204 | h6204
                              · linarith only [h0, h5505, h6124, h6196, h6202, h6204, hc12, hc23, hlam, hphi]
                              · linarith only [h0, h5505, h6204, hc12, hc45, hlam, hphi, ht23, ht34]
                            · linarith only [h0, h1, h6123, h6203, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                          · linarith only [h0, h1, h6202, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h6209 | h6209
                  · linarith only [h6122, h6123, h6209, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h6211 | h6211
                    · linarith only [h0, h1, h6123, h6211, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h6213 | h6213
                      · linarith only [h0, h5505, h6209, h6213, hc24, hc45, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h6215 | h6215
                        · linarith only [h0, h6120, h6215, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h6217 | h6217
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h6218 | h6218
                            · linarith only [h0, h5505, h6122, h6123, h6211, h6218, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h1, h6218, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h0, h1, h6122, h6217, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h6222 | h6222
                · rcases m.htr 0 4 5 (by decide) (by decide) with h6223 | h6223
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h6224 | h6224
                    · linarith only [h0, h6116, h6224, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h6226 | h6226
                      · linarith only [h0, h6118, h6226, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h6228 | h6228
                        · linarith only [h0, h6120, h6228, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h6230 | h6230
                          · linarith only [h0, h5953, h6122, h6222, h6224, h6230, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h6230, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h6122, h6222, h6223, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h6234 | h6234
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h6235 | h6235
                    · linarith only [h0, h1, h6222, h6235, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h6237 | h6237
                      · linarith only [h0, h6118, h6237, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h6239 | h6239
                        · linarith only [h0, h6120, h6239, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h6241 | h6241
                          · linarith only [h0, h1, h6122, h6235, h6241, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h6241, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h6244 | h6244
                    · linarith only [h0, h1, h6122, h6234, h6244, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h6246 | h6246
                      · linarith only [h0, h1, h6118, h6122, h6246, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h6248 | h6248
                        · linarith only [h0, h1, h6120, h6122, h6234, h6248, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h6250 | h6250
                          · linarith only [h0, h1, h6122, h6244, h6250, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h6250, hc12, hc34, hlam, hphi, ht23]

end R2N4
