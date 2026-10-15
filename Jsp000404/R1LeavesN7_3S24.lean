import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_3S14
import Jsp000404.R1LeavesN7_3S21
import Jsp000404.R1LeavesN7_3S23

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9670000 in
set_option maxHeartbeats 9670000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s10_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h8674 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8675 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 3 4 (by decide) (by decide) with h9441 | h9441
  · rcases m.htr 0 3 5 (by decide) (by decide) with h9442 | h9442
    · rcases m.htr 0 4 5 (by decide) (by decide) with h9443 | h9443
      · linarith only [h8674, h8675, h9443, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h9445 | h9445
        · linarith only [h0, h4, h9445, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h9447 | h9447
          · rcases m.htr 1 2 5 (by decide) (by decide) with h9448 | h9448
            · linarith only [h0, h8675, h9448, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9450 | h9450
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9451 | h9451
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9452 | h9452
                  · linarith only [h2, h9443, h9452, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9454 | h9454
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9455 | h9455
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9456 | h9456
                        · linarith only [h8674, h8675, h9443, h9455, h9456, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9458 | h9458
                          · linarith only [h0, h8675, h9447, h9454, h9456, h9458, hlam]
                          · rcases h1bigk with h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c
                            · have p9460_0 := h9460c.1
                              have p9460_1 := h9460c.2.1
                              have p9460_2 := h9460c.2.2.1
                              have p9460_3 := h9460c.2.2.2
                              linarith only [hlam, p9460_0]
                            · have p9460_0 := h9460c.1
                              have p9460_1 := h9460c.2.1
                              have p9460_2 := h9460c.2.2.1
                              have p9460_3 := h9460c.2.2.2
                              rcases p9460_3 (m.d 0 1) (by simp) with h9462 | h9462
                              · rcases p9460_3 (m.d 1 2) (by simp) with h9463 | h9463
                                · linarith only [h9463, hlam, p9460_0]
                                · rcases p9460_3 (m.d 1 3) (by simp) with h9465 | h9465
                                  · linarith only [h1, h9465, hlam]
                                  · linarith only [h9445, h9465, hlam]
                              · linarith only [h9462, hlam, p9460_0]
                            · have p9460_0 := h9460c.1
                              have p9460_1 := h9460c.2.1
                              have p9460_2 := h9460c.2.2.1
                              have p9460_3 := h9460c.2.2.2
                              rcases p9460_3 (m.d 0 1) (by simp) with h9469 | h9469
                              · rcases p9460_3 (m.d 1 2) (by simp) with h9470 | h9470
                                · linarith only [h0, h9470, hlam]
                                · rcases p9460_3 (m.d 1 3) (by simp) with h9472 | h9472
                                  · linarith only [h9472, hlam, p9460_0]
                                  · rcases p9460_3 (m.d 1 4) (by simp) with h9474 | h9474
                                    · linarith only [h2, h9474, hlam]
                                    · rcases p9460_3 (m.d 1 5) (by simp) with h9476 | h9476
                                      · linarith only [h3, h9476, hlam]
                                      · rcases h3bigk with h9478c | h9478c | h9478c | h9478c | h9478c | h9478c | h9478c | h9478c | h9478c | h9478c | h9478c | h9478c | h9478c | h9478c | h9478c | h9478c | h9478c | h9478c | h9478c | h9478c | h9478c | h9478c | h9478c | h9478c | h9478c
                                        · have p9478_0 := h9478c.1
                                          have p9478_1 := h9478c.2.1
                                          have p9478_2 := h9478c.2.2.1
                                          have p9478_3 := h9478c.2.2.2
                                          linarith only [hlam, p9478_0]
                                        · have p9478_0 := h9478c.1
                                          have p9478_1 := h9478c.2.1
                                          have p9478_2 := h9478c.2.2.1
                                          have p9478_3 := h9478c.2.2.2
                                          rcases p9478_3 (m.d 0 3) (by simp) with h9480 | h9480
                                          · rcases p9478_3 (m.d 1 3) (by simp) with h9481 | h9481
                                            · linarith only [h1, h9481, hlam]
                                            · rcases p9478_3 (m.d 2 3) (by simp) with h9483 | h9483
                                              · rcases p9478_3 (m.d 3 4) (by simp) with h9484 | h9484
                                                · linarith only [h9441, h9484, hlam]
                                                · rcases p9478_3 (m.d 3 5) (by simp) with h9486 | h9486
                                                  · linarith only [h9442, h9486, hlam]
                                                  · rcases h5bigk with h9488c | h9488c | h9488c | h9488c | h9488c | h9488c | h9488c | h9488c | h9488c | h9488c | h9488c | h9488c | h9488c | h9488c | h9488c | h9488c | h9488c | h9488c | h9488c | h9488c | h9488c | h9488c | h9488c | h9488c | h9488c
                                                    · have p9488_0 := h9488c.1
                                                      have p9488_1 := h9488c.2.1
                                                      have p9488_2 := h9488c.2.2.1
                                                      have p9488_3 := h9488c.2.2.2
                                                      linarith only [hlam, p9488_0]
                                                    · have p9488_0 := h9488c.1
                                                      have p9488_1 := h9488c.2.1
                                                      have p9488_2 := h9488c.2.2.1
                                                      have p9488_3 := h9488c.2.2.2
                                                      linarith only [h9447, h9448, hc05, hc24, hlam, hphi, ht0b, ht45, ht5b, p9488_1]
                                                    · have p9488_0 := h9488c.1
                                                      have p9488_1 := h9488c.2.1
                                                      have p9488_2 := h9488c.2.2.1
                                                      have p9488_3 := h9488c.2.2.2
                                                      linarith only [h8675, hlam, p9488_0]
                                                    · have p9488_0 := h9488c.1
                                                      have p9488_1 := h9488c.2.1
                                                      have p9488_2 := h9488c.2.2.1
                                                      have p9488_3 := h9488c.2.2.2
                                                      linarith only [h8675, h9456, h9458, hc34, hc45, hlam, hphi, p9488_1]
                                                    · have p9488_0 := h9488c.1
                                                      have p9488_1 := h9488c.2.1
                                                      have p9488_2 := h9488c.2.2.1
                                                      have p9488_3 := h9488c.2.2.2
                                                      linarith only [h9443, hlam, p9488_1]
                                                    · have p9488_0 := h9488c.1
                                                      have p9488_1 := h9488c.2.1
                                                      have p9488_2 := h9488c.2.2.1
                                                      have p9488_3 := h9488c.2.2.2
                                                      linarith only [h3, hlam, p9488_0]
                                                    · have p9488_0 := h9488c.1
                                                      have p9488_1 := h9488c.2.1
                                                      have p9488_2 := h9488c.2.2.1
                                                      have p9488_3 := h9488c.2.2.2
                                                      linarith only [hlam, p9488_0]
                                                    · have p9488_0 := h9488c.1
                                                      have p9488_1 := h9488c.2.1
                                                      have p9488_2 := h9488c.2.2.1
                                                      have p9488_3 := h9488c.2.2.2
                                                      linarith only [h9448, hlam, p9488_0]
                                                    · have p9488_0 := h9488c.1
                                                      have p9488_1 := h9488c.2.1
                                                      have p9488_2 := h9488c.2.2.1
                                                      have p9488_3 := h9488c.2.2.2
                                                      linarith only [h4, h9451, h9458, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9478_1, p9488_1]
                                                    · have p9488_0 := h9488c.1
                                                      have p9488_1 := h9488c.2.1
                                                      have p9488_2 := h9488c.2.2.1
                                                      have p9488_3 := h9488c.2.2.2
                                                      linarith only [h9452, hlam, p9488_1]
                                                    · have p9488_0 := h9488c.1
                                                      have p9488_1 := h9488c.2.1
                                                      have p9488_2 := h9488c.2.2.1
                                                      have p9488_3 := h9488c.2.2.2
                                                      linarith only [h3, h9448, h9456, hc12, hc45, hlam, hphi, ht23, ht34, p9488_1]
                                                    · have p9488_0 := h9488c.1
                                                      have p9488_1 := h9488c.2.1
                                                      have p9488_2 := h9488c.2.2.1
                                                      have p9488_3 := h9488c.2.2.2
                                                      linarith only [h9447, h9448, h9456, hc24, hc45, hlam, hphi, p9488_1]
                                                    · have p9488_0 := h9488c.1
                                                      have p9488_1 := h9488c.2.1
                                                      have p9488_2 := h9488c.2.2.1
                                                      have p9488_3 := h9488c.2.2.2
                                                      linarith only [hlam, p9488_0]
                                                    · have p9488_0 := h9488c.1
                                                      have p9488_1 := h9488c.2.1
                                                      have p9488_2 := h9488c.2.2.1
                                                      have p9488_3 := h9488c.2.2.2
                                                      linarith only [h9456, h9458, hc34, hc45, hlam, hphi, p9488_1]
                                                    · have p9488_0 := h9488c.1
                                                      have p9488_1 := h9488c.2.1
                                                      have p9488_2 := h9488c.2.2.1
                                                      have p9488_3 := h9488c.2.2.2
                                                      linarith only [h9456, hlam, p9488_1]
                                                    · have p9488_0 := h9488c.1
                                                      have p9488_1 := h9488c.2.1
                                                      have p9488_2 := h9488c.2.2.1
                                                      have p9488_3 := h9488c.2.2.2
                                                      linarith only [h9442, hlam, p9488_0]
                                                    · have p9488_0 := h9488c.1
                                                      have p9488_1 := h9488c.2.1
                                                      have p9488_2 := h9488c.2.2.1
                                                      have p9488_3 := h9488c.2.2.2
                                                      linarith only [h9451, hlam, p9488_0]
                                                    · have p9488_0 := h9488c.1
                                                      have p9488_1 := h9488c.2.1
                                                      have p9488_2 := h9488c.2.2.1
                                                      have p9488_3 := h9488c.2.2.2
                                                      linarith only [h9455, hlam, p9488_0]
                                                    · have p9488_0 := h9488c.1
                                                      have p9488_1 := h9488c.2.1
                                                      have p9488_2 := h9488c.2.2.1
                                                      have p9488_3 := h9488c.2.2.2
                                                      linarith only [hlam, p9488_0]
                                                    · have p9488_0 := h9488c.1
                                                      have p9488_1 := h9488c.2.1
                                                      have p9488_2 := h9488c.2.2.1
                                                      have p9488_3 := h9488c.2.2.2
                                                      linarith only [h9458, hlam, p9488_1]
                                                    · have p9488_0 := h9488c.1
                                                      have p9488_1 := h9488c.2.1
                                                      have p9488_2 := h9488c.2.2.1
                                                      have p9488_3 := h9488c.2.2.2
                                                      linarith only [h3, h9447, h9448, h9454, hc34, hc45, hlam, hphi, p9488_1]
                                                    · have p9488_0 := h9488c.1
                                                      have p9488_1 := h9488c.2.1
                                                      have p9488_2 := h9488c.2.2.1
                                                      have p9488_3 := h9488c.2.2.2
                                                      linarith only [h9447, h9448, h9454, hc34, hc45, hlam, hphi, p9488_1]
                                                    · have p9488_0 := h9488c.1
                                                      have p9488_1 := h9488c.2.1
                                                      have p9488_2 := h9488c.2.2.1
                                                      have p9488_3 := h9488c.2.2.2
                                                      linarith only [h0, h8675, h9447, h9454, hc34, hc45, hlam, hphi, p9488_1]
                                                    · have p9488_0 := h9488c.1
                                                      have p9488_1 := h9488c.2.1
                                                      have p9488_2 := h9488c.2.2.1
                                                      have p9488_3 := h9488c.2.2.2
                                                      linarith only [h9458, hc34, hc45, hlam, hphi, p9488_1]
                                                    · have p9488_0 := h9488c.1
                                                      have p9488_1 := h9488c.2.1
                                                      have p9488_2 := h9488c.2.2.1
                                                      have p9488_3 := h9488c.2.2.2
                                                      linarith only [hlam, p9488_0]
                                              · linarith only [h9445, h9483, hlam]
                                          · linarith only [h1, h9480, hlam]
                                        · have p9478_0 := h9478c.1
                                          have p9478_1 := h9478c.2.1
                                          have p9478_2 := h9478c.2.2.1
                                          have p9478_3 := h9478c.2.2.2
                                          linarith only [h4, hlam, p9478_1]
                                        · have p9478_0 := h9478c.1
                                          have p9478_1 := h9478c.2.1
                                          have p9478_2 := h9478c.2.2.1
                                          have p9478_3 := h9478c.2.2.2
                                          rcases p9478_3 (m.d 0 3) (by simp) with h9517 | h9517
                                          · rcases p9478_3 (m.d 1 3) (by simp) with h9518 | h9518
                                            · linarith only [h1, h9518, hlam]
                                            · linarith only [h9450, h9518, hlam]
                                          · linarith only [h9517, hlam, p9478_0]
                                        · have p9478_0 := h9478c.1
                                          have p9478_1 := h9478c.2.1
                                          have p9478_2 := h9478c.2.2.1
                                          have p9478_3 := h9478c.2.2.2
                                          rcases p9478_3 (m.d 0 3) (by simp) with h9522 | h9522
                                          · rcases p9478_3 (m.d 1 3) (by simp) with h9523 | h9523
                                            · linarith only [h1, h9523, hlam]
                                            · linarith only [h9451, h9523, hlam]
                                          · linarith only [h9522, hlam, p9478_0]
                                        · have p9478_0 := h9478c.1
                                          have p9478_1 := h9478c.2.1
                                          have p9478_2 := h9478c.2.2.1
                                          have p9478_3 := h9478c.2.2.2
                                          linarith only [h1, hlam, p9478_0]
                                        · have p9478_0 := h9478c.1
                                          have p9478_1 := h9478c.2.1
                                          have p9478_2 := h9478c.2.2.1
                                          have p9478_3 := h9478c.2.2.2
                                          linarith only [hlam, p9478_0]
                                        · have p9478_0 := h9478c.1
                                          have p9478_1 := h9478c.2.1
                                          have p9478_2 := h9478c.2.2.1
                                          have p9478_3 := h9478c.2.2.2
                                          linarith only [h9445, hlam, p9478_1]
                                        · have p9478_0 := h9478c.1
                                          have p9478_1 := h9478c.2.1
                                          have p9478_2 := h9478c.2.2.1
                                          have p9478_3 := h9478c.2.2.2
                                          linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9460_1, p9478_1]
                                        · have p9478_0 := h9478c.1
                                          have p9478_1 := h9478c.2.1
                                          have p9478_2 := h9478c.2.2.1
                                          have p9478_3 := h9478c.2.2.2
                                          linarith only [h9458, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9460_1, p9478_1]
                                        · have p9478_0 := h9478c.1
                                          have p9478_1 := h9478c.2.1
                                          have p9478_2 := h9478c.2.2.1
                                          have p9478_3 := h9478c.2.2.2
                                          rcases p9478_3 (m.d 0 3) (by simp) with h9532 | h9532
                                          · linarith only [h4, h9532, hlam]
                                          · rcases p9478_3 (m.d 1 3) (by simp) with h9534 | h9534
                                            · linarith only [h9445, h9534, hlam]
                                            · rcases p9478_3 (m.d 2 3) (by simp) with h9536 | h9536
                                              · rcases p9478_3 (m.d 3 4) (by simp) with h9537 | h9537
                                                · linarith only [h9454, h9537, hlam]
                                                · rcases p9478_3 (m.d 3 5) (by simp) with h9539 | h9539
                                                  · linarith only [h9455, h9539, hlam]
                                                  · rcases h5bigk with h9541c | h9541c | h9541c | h9541c | h9541c | h9541c | h9541c | h9541c | h9541c | h9541c | h9541c | h9541c | h9541c | h9541c | h9541c | h9541c | h9541c | h9541c | h9541c | h9541c | h9541c | h9541c | h9541c | h9541c | h9541c
                                                    · have p9541_0 := h9541c.1
                                                      have p9541_1 := h9541c.2.1
                                                      have p9541_2 := h9541c.2.2.1
                                                      have p9541_3 := h9541c.2.2.2
                                                      linarith only [hlam, p9541_0]
                                                    · have p9541_0 := h9541c.1
                                                      have p9541_1 := h9541c.2.1
                                                      have p9541_2 := h9541c.2.2.1
                                                      have p9541_3 := h9541c.2.2.2
                                                      linarith only [h9447, h9448, h9454, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p9541_1]
                                                    · have p9541_0 := h9541c.1
                                                      have p9541_1 := h9541c.2.1
                                                      have p9541_2 := h9541c.2.2.1
                                                      have p9541_3 := h9541c.2.2.2
                                                      linarith only [h8675, hlam, p9541_0]
                                                    · have p9541_0 := h9541c.1
                                                      have p9541_1 := h9541c.2.1
                                                      have p9541_2 := h9541c.2.2.1
                                                      have p9541_3 := h9541c.2.2.2
                                                      linarith only [h9442, h9458, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9478_1, p9541_1]
                                                    · have p9541_0 := h9541c.1
                                                      have p9541_1 := h9541c.2.1
                                                      have p9541_2 := h9541c.2.2.1
                                                      have p9541_3 := h9541c.2.2.2
                                                      linarith only [h9443, hlam, p9541_1]
                                                    · have p9541_0 := h9541c.1
                                                      have p9541_1 := h9541c.2.1
                                                      have p9541_2 := h9541c.2.2.1
                                                      have p9541_3 := h9541c.2.2.2
                                                      linarith only [h3, hlam, p9541_0]
                                                    · have p9541_0 := h9541c.1
                                                      have p9541_1 := h9541c.2.1
                                                      have p9541_2 := h9541c.2.2.1
                                                      have p9541_3 := h9541c.2.2.2
                                                      linarith only [hlam, p9541_0]
                                                    · have p9541_0 := h9541c.1
                                                      have p9541_1 := h9541c.2.1
                                                      have p9541_2 := h9541c.2.2.1
                                                      have p9541_3 := h9541c.2.2.2
                                                      linarith only [h9448, hlam, p9541_0]
                                                    · have p9541_0 := h9541c.1
                                                      have p9541_1 := h9541c.2.1
                                                      have p9541_2 := h9541c.2.2.1
                                                      have p9541_3 := h9541c.2.2.2
                                                      linarith only [h3, h9458, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9541_1]
                                                    · have p9541_0 := h9541c.1
                                                      have p9541_1 := h9541c.2.1
                                                      have p9541_2 := h9541c.2.2.1
                                                      have p9541_3 := h9541c.2.2.2
                                                      linarith only [h9452, hlam, p9541_1]
                                                    · have p9541_0 := h9541c.1
                                                      have p9541_1 := h9541c.2.1
                                                      have p9541_2 := h9541c.2.2.1
                                                      have p9541_3 := h9541c.2.2.2
                                                      linarith only [h0, h8675, h9447, h9454, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9541_1]
                                                    · have p9541_0 := h9541c.1
                                                      have p9541_1 := h9541c.2.1
                                                      have p9541_2 := h9541c.2.2.1
                                                      have p9541_3 := h9541c.2.2.2
                                                      linarith only [h9447, h9448, h9454, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9541_1]
                                                    · have p9541_0 := h9541c.1
                                                      have p9541_1 := h9541c.2.1
                                                      have p9541_2 := h9541c.2.2.1
                                                      have p9541_3 := h9541c.2.2.2
                                                      linarith only [hlam, p9541_0]
                                                    · have p9541_0 := h9541c.1
                                                      have p9541_1 := h9541c.2.1
                                                      have p9541_2 := h9541c.2.2.1
                                                      have p9541_3 := h9541c.2.2.2
                                                      linarith only [h9456, h9458, hc34, hc45, hlam, hphi, p9541_1]
                                                    · have p9541_0 := h9541c.1
                                                      have p9541_1 := h9541c.2.1
                                                      have p9541_2 := h9541c.2.2.1
                                                      have p9541_3 := h9541c.2.2.2
                                                      linarith only [h9456, hlam, p9541_1]
                                                    · have p9541_0 := h9541c.1
                                                      have p9541_1 := h9541c.2.1
                                                      have p9541_2 := h9541c.2.2.1
                                                      have p9541_3 := h9541c.2.2.2
                                                      linarith only [h9442, hlam, p9541_0]
                                                    · have p9541_0 := h9541c.1
                                                      have p9541_1 := h9541c.2.1
                                                      have p9541_2 := h9541c.2.2.1
                                                      have p9541_3 := h9541c.2.2.2
                                                      linarith only [h9451, hlam, p9541_0]
                                                    · have p9541_0 := h9541c.1
                                                      have p9541_1 := h9541c.2.1
                                                      have p9541_2 := h9541c.2.2.1
                                                      have p9541_3 := h9541c.2.2.2
                                                      linarith only [h9455, hlam, p9541_0]
                                                    · have p9541_0 := h9541c.1
                                                      have p9541_1 := h9541c.2.1
                                                      have p9541_2 := h9541c.2.2.1
                                                      have p9541_3 := h9541c.2.2.2
                                                      linarith only [hlam, p9541_0]
                                                    · have p9541_0 := h9541c.1
                                                      have p9541_1 := h9541c.2.1
                                                      have p9541_2 := h9541c.2.2.1
                                                      have p9541_3 := h9541c.2.2.2
                                                      linarith only [h9458, hlam, p9541_1]
                                                    · have p9541_0 := h9541c.1
                                                      have p9541_1 := h9541c.2.1
                                                      have p9541_2 := h9541c.2.2.1
                                                      have p9541_3 := h9541c.2.2.2
                                                      linarith only [h0, h8675, h9447, h9454, hc34, hc45, hlam, hphi, p9541_1]
                                                    · have p9541_0 := h9541c.1
                                                      have p9541_1 := h9541c.2.1
                                                      have p9541_2 := h9541c.2.2.1
                                                      have p9541_3 := h9541c.2.2.2
                                                      linarith only [h9447, h9448, h9454, hc34, hc45, hlam, hphi, p9541_1]
                                                    · have p9541_0 := h9541c.1
                                                      have p9541_1 := h9541c.2.1
                                                      have p9541_2 := h9541c.2.2.1
                                                      have p9541_3 := h9541c.2.2.2
                                                      linarith only [h0, h8675, h9447, h9454, hc34, hc45, hlam, hphi, p9541_1]
                                                    · have p9541_0 := h9541c.1
                                                      have p9541_1 := h9541c.2.1
                                                      have p9541_2 := h9541c.2.2.1
                                                      have p9541_3 := h9541c.2.2.2
                                                      linarith only [h9458, hc34, hc45, hlam, hphi, p9541_1]
                                                    · have p9541_0 := h9541c.1
                                                      have p9541_1 := h9541c.2.1
                                                      have p9541_2 := h9541c.2.2.1
                                                      have p9541_3 := h9541c.2.2.2
                                                      linarith only [hlam, p9541_0]
                                              · linarith only [h4, h9536, hlam]
                                        · have p9478_0 := h9478c.1
                                          have p9478_1 := h9478c.2.1
                                          have p9478_2 := h9478c.2.2.1
                                          have p9478_3 := h9478c.2.2.2
                                          rcases p9478_3 (m.d 0 3) (by simp) with h9568 | h9568
                                          · linarith only [h4, h9568, hlam]
                                          · linarith only [h1, h9568, hlam]
                                        · have p9478_0 := h9478c.1
                                          have p9478_1 := h9478c.2.1
                                          have p9478_2 := h9478c.2.2.1
                                          have p9478_3 := h9478c.2.2.2
                                          linarith only [hlam, p9478_0]
                                        · have p9478_0 := h9478c.1
                                          have p9478_1 := h9478c.2.1
                                          have p9478_2 := h9478c.2.2.1
                                          have p9478_3 := h9478c.2.2.2
                                          rcases p9478_3 (m.d 0 3) (by simp) with h9572 | h9572
                                          · linarith only [h4, h9572, hlam]
                                          · linarith only [h9441, h9572, hlam]
                                        · have p9478_0 := h9478c.1
                                          have p9478_1 := h9478c.2.1
                                          have p9478_2 := h9478c.2.2.1
                                          have p9478_3 := h9478c.2.2.2
                                          rcases p9478_3 (m.d 0 3) (by simp) with h9575 | h9575
                                          · linarith only [h4, h9575, hlam]
                                          · linarith only [h9442, h9575, hlam]
                                        · have p9478_0 := h9478c.1
                                          have p9478_1 := h9478c.2.1
                                          have p9478_2 := h9478c.2.2.1
                                          have p9478_3 := h9478c.2.2.2
                                          linarith only [h9441, hlam, p9478_0]
                                        · have p9478_0 := h9478c.1
                                          have p9478_1 := h9478c.2.1
                                          have p9478_2 := h9478c.2.2.1
                                          have p9478_3 := h9478c.2.2.2
                                          linarith only [h9450, hlam, p9478_0]
                                        · have p9478_0 := h9478c.1
                                          have p9478_1 := h9478c.2.1
                                          have p9478_2 := h9478c.2.2.1
                                          have p9478_3 := h9478c.2.2.2
                                          linarith only [h9454, hlam, p9478_0]
                                        · have p9478_0 := h9478c.1
                                          have p9478_1 := h9478c.2.1
                                          have p9478_2 := h9478c.2.2.1
                                          have p9478_3 := h9478c.2.2.2
                                          linarith only [hlam, p9478_0]
                                        · have p9478_0 := h9478c.1
                                          have p9478_1 := h9478c.2.1
                                          have p9478_2 := h9478c.2.2.1
                                          have p9478_3 := h9478c.2.2.2
                                          linarith only [h9458, hlam, p9478_1]
                                        · have p9478_0 := h9478c.1
                                          have p9478_1 := h9478c.2.1
                                          have p9478_2 := h9478c.2.2.1
                                          have p9478_3 := h9478c.2.2.2
                                          linarith only [h9442, hlam, p9478_0]
                                        · have p9478_0 := h9478c.1
                                          have p9478_1 := h9478c.2.1
                                          have p9478_2 := h9478c.2.2.1
                                          have p9478_3 := h9478c.2.2.2
                                          linarith only [h9451, hlam, p9478_0]
                                        · have p9478_0 := h9478c.1
                                          have p9478_1 := h9478c.2.1
                                          have p9478_2 := h9478c.2.2.1
                                          have p9478_3 := h9478c.2.2.2
                                          linarith only [h9455, hlam, p9478_0]
                                        · have p9478_0 := h9478c.1
                                          have p9478_1 := h9478c.2.1
                                          have p9478_2 := h9478c.2.2.1
                                          have p9478_3 := h9478c.2.2.2
                                          linarith only [h9451, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9460_1, p9478_1]
                                        · have p9478_0 := h9478c.1
                                          have p9478_1 := h9478c.2.1
                                          have p9478_2 := h9478c.2.2.1
                                          have p9478_3 := h9478c.2.2.2
                                          linarith only [hlam, p9478_0]
                              · linarith only [h9469, hlam, p9460_0]
                            · have p9460_0 := h9460c.1
                              have p9460_1 := h9460c.2.1
                              have p9460_2 := h9460c.2.2.1
                              have p9460_3 := h9460c.2.2.2
                              rcases p9460_3 (m.d 0 1) (by simp) with h9589 | h9589
                              · rcases p9460_3 (m.d 1 2) (by simp) with h9590 | h9590
                                · linarith only [h0, h9590, hlam]
                                · linarith only [h9447, h9590, hlam]
                              · linarith only [h9589, hlam, p9460_0]
                            · have p9460_0 := h9460c.1
                              have p9460_1 := h9460c.2.1
                              have p9460_2 := h9460c.2.2.1
                              have p9460_3 := h9460c.2.2.2
                              rcases p9460_3 (m.d 0 1) (by simp) with h9594 | h9594
                              · rcases p9460_3 (m.d 1 2) (by simp) with h9595 | h9595
                                · linarith only [h0, h9595, hlam]
                                · rcases p9460_3 (m.d 1 3) (by simp) with h9597 | h9597
                                  · linarith only [h1, h9597, hlam]
                                  · linarith only [h9451, h9597, hlam]
                              · linarith only [h9594, hlam, p9460_0]
                            · have p9460_0 := h9460c.1
                              have p9460_1 := h9460c.2.1
                              have p9460_2 := h9460c.2.2.1
                              have p9460_3 := h9460c.2.2.2
                              linarith only [h0, hlam, p9460_0]
                            · have p9460_0 := h9460c.1
                              have p9460_1 := h9460c.2.1
                              have p9460_2 := h9460c.2.2.1
                              have p9460_3 := h9460c.2.2.2
                              linarith only [hlam, p9460_0]
                            · have p9460_0 := h9460c.1
                              have p9460_1 := h9460c.2.1
                              have p9460_2 := h9460c.2.2.1
                              have p9460_3 := h9460c.2.2.2
                              linarith only [h9445, hlam, p9460_0]
                            · have p9460_0 := h9460c.1
                              have p9460_1 := h9460c.2.1
                              have p9460_2 := h9460c.2.2.1
                              have p9460_3 := h9460c.2.2.2
                              linarith only [h0, h8675, h9447, h9454, h9456, hc34, hc45, hlam, hphi, p9460_1]
                            · have p9460_0 := h9460c.1
                              have p9460_1 := h9460c.2.1
                              have p9460_2 := h9460c.2.2.1
                              have p9460_3 := h9460c.2.2.2
                              linarith only [h9448, hlam, p9460_0]
                            · have p9460_0 := h9460c.1
                              have p9460_1 := h9460c.2.1
                              have p9460_2 := h9460c.2.2.1
                              have p9460_3 := h9460c.2.2.2
                              linarith only [h1, hlam, p9460_0]
                            · have p9460_0 := h9460c.1
                              have p9460_1 := h9460c.2.1
                              have p9460_2 := h9460c.2.2.1
                              have p9460_3 := h9460c.2.2.2
                              linarith only [h1, h9447, h9454, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9460_1]
                            · have p9460_0 := h9460c.1
                              have p9460_1 := h9460c.2.1
                              have p9460_2 := h9460c.2.2.1
                              have p9460_3 := h9460c.2.2.2
                              linarith only [hlam, p9460_0]
                            · have p9460_0 := h9460c.1
                              have p9460_1 := h9460c.2.1
                              have p9460_2 := h9460c.2.2.1
                              have p9460_3 := h9460c.2.2.2
                              rcases p9460_3 (m.d 0 1) (by simp) with h9609 | h9609
                              · rcases p9460_3 (m.d 1 2) (by simp) with h9610 | h9610
                                · linarith only [h9445, h9610, hlam]
                                · linarith only [h9447, h9610, hlam]
                              · linarith only [h2, h9609, hlam]
                            · have p9460_0 := h9460c.1
                              have p9460_1 := h9460c.2.1
                              have p9460_2 := h9460c.2.2.1
                              have p9460_3 := h9460c.2.2.2
                              linarith only [h1, h9447, h9448, h9454, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9460_1]
                            · have p9460_0 := h9460c.1
                              have p9460_1 := h9460c.2.1
                              have p9460_2 := h9460c.2.2.1
                              have p9460_3 := h9460c.2.2.2
                              linarith only [h2, hlam, p9460_0]
                            · have p9460_0 := h9460c.1
                              have p9460_1 := h9460c.2.1
                              have p9460_2 := h9460c.2.2.1
                              have p9460_3 := h9460c.2.2.2
                              linarith only [h9447, hlam, p9460_1]
                            · have p9460_0 := h9460c.1
                              have p9460_1 := h9460c.2.1
                              have p9460_2 := h9460c.2.2.1
                              have p9460_3 := h9460c.2.2.2
                              linarith only [h9450, hlam, p9460_0]
                            · have p9460_0 := h9460c.1
                              have p9460_1 := h9460c.2.1
                              have p9460_2 := h9460c.2.2.1
                              have p9460_3 := h9460c.2.2.2
                              linarith only [hlam, p9460_0]
                            · have p9460_0 := h9460c.1
                              have p9460_1 := h9460c.2.1
                              have p9460_2 := h9460c.2.2.1
                              have p9460_3 := h9460c.2.2.2
                              linarith only [h9452, hlam, p9460_1]
                            · have p9460_0 := h9460c.1
                              have p9460_1 := h9460c.2.1
                              have p9460_2 := h9460c.2.2.1
                              have p9460_3 := h9460c.2.2.2
                              linarith only [h3, hlam, p9460_0]
                            · have p9460_0 := h9460c.1
                              have p9460_1 := h9460c.2.1
                              have p9460_2 := h9460c.2.2.1
                              have p9460_3 := h9460c.2.2.2
                              linarith only [h3, h9447, h9454, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9460_1]
                            · have p9460_0 := h9460c.1
                              have p9460_1 := h9460c.2.1
                              have p9460_2 := h9460c.2.2.1
                              have p9460_3 := h9460c.2.2.2
                              linarith only [h9451, hlam, p9460_0]
                            · have p9460_0 := h9460c.1
                              have p9460_1 := h9460c.2.1
                              have p9460_2 := h9460c.2.2.1
                              have p9460_3 := h9460c.2.2.2
                              rcases p9460_3 (m.d 0 1) (by simp) with h9623 | h9623
                              · rcases p9460_3 (m.d 1 2) (by simp) with h9624 | h9624
                                · linarith only [h9448, h9624, hlam]
                                · linarith only [h9447, h9624, hlam]
                              · linarith only [h2, h9623, hlam]
                            · have p9460_0 := h9460c.1
                              have p9460_1 := h9460c.2.1
                              have p9460_2 := h9460c.2.2.1
                              have p9460_3 := h9460c.2.2.2
                              linarith only [hlam, p9460_0]
                      · linarith only [h1, h4, h9451, h9455, hlam]
                    · linarith only [h4, h9441, h9454, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9631 | h9631
                  · linarith only [h2, h8674, h8675, h9443, h9631, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9633 | h9633
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9634 | h9634
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9635 | h9635
                        · linarith only [h9442, h9443, h9445, h9447, h9451, h9635, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9637 | h9637
                          · linarith only [h8675, h9442, h9445, h9447, h9451, h9633, h9635, h9637, hlam]
                          · rcases h1bigk with h9639c | h9639c | h9639c | h9639c | h9639c | h9639c | h9639c | h9639c | h9639c | h9639c | h9639c | h9639c | h9639c | h9639c | h9639c | h9639c | h9639c | h9639c | h9639c | h9639c | h9639c | h9639c | h9639c | h9639c | h9639c
                            · have p9639_0 := h9639c.1
                              have p9639_1 := h9639c.2.1
                              have p9639_2 := h9639c.2.2.1
                              have p9639_3 := h9639c.2.2.2
                              linarith only [hlam, p9639_0]
                            · have p9639_0 := h9639c.1
                              have p9639_1 := h9639c.2.1
                              have p9639_2 := h9639c.2.2.1
                              have p9639_3 := h9639c.2.2.2
                              rcases p9639_3 (m.d 0 1) (by simp) with h9641 | h9641
                              · rcases p9639_3 (m.d 1 2) (by simp) with h9642 | h9642
                                · linarith only [h9642, hlam, p9639_0]
                                · rcases p9639_3 (m.d 1 3) (by simp) with h9644 | h9644
                                  · linarith only [h1, h9644, hlam]
                                  · linarith only [h9445, h9644, hlam]
                              · linarith only [h9641, hlam, p9639_0]
                            · have p9639_0 := h9639c.1
                              have p9639_1 := h9639c.2.1
                              have p9639_2 := h9639c.2.2.1
                              have p9639_3 := h9639c.2.2.2
                              rcases p9639_3 (m.d 0 1) (by simp) with h9648 | h9648
                              · rcases p9639_3 (m.d 1 2) (by simp) with h9649 | h9649
                                · linarith only [h0, h9649, hlam]
                                · rcases p9639_3 (m.d 1 3) (by simp) with h9651 | h9651
                                  · linarith only [h9651, hlam, p9639_0]
                                  · rcases p9639_3 (m.d 1 4) (by simp) with h9653 | h9653
                                    · linarith only [h2, h9653, hlam]
                                    · rcases p9639_3 (m.d 1 5) (by simp) with h9655 | h9655
                                      · linarith only [h3, h9655, hlam]
                                      · linarith only [h9451, h9655, hlam]
                              · linarith only [h9648, hlam, p9639_0]
                            · have p9639_0 := h9639c.1
                              have p9639_1 := h9639c.2.1
                              have p9639_2 := h9639c.2.2.1
                              have p9639_3 := h9639c.2.2.2
                              rcases p9639_3 (m.d 0 1) (by simp) with h9659 | h9659
                              · rcases p9639_3 (m.d 1 2) (by simp) with h9660 | h9660
                                · linarith only [h0, h9660, hlam]
                                · linarith only [h9447, h9660, hlam]
                              · linarith only [h9659, hlam, p9639_0]
                            · have p9639_0 := h9639c.1
                              have p9639_1 := h9639c.2.1
                              have p9639_2 := h9639c.2.2.1
                              have p9639_3 := h9639c.2.2.2
                              rcases p9639_3 (m.d 0 1) (by simp) with h9664 | h9664
                              · rcases p9639_3 (m.d 1 2) (by simp) with h9665 | h9665
                                · linarith only [h0, h9665, hlam]
                                · rcases p9639_3 (m.d 1 3) (by simp) with h9667 | h9667
                                  · linarith only [h1, h9667, hlam]
                                  · rcases p9639_3 (m.d 1 4) (by simp) with h9669 | h9669
                                    · linarith only [h2, h9669, hlam]
                                    · rcases p9639_3 (m.d 1 5) (by simp) with h9671 | h9671
                                      · linarith only [h9671, hlam, p9639_0]
                                      · rcases h3bigk with h9673c | h9673c | h9673c | h9673c | h9673c | h9673c | h9673c | h9673c | h9673c | h9673c | h9673c | h9673c | h9673c | h9673c | h9673c | h9673c | h9673c | h9673c | h9673c | h9673c | h9673c | h9673c | h9673c | h9673c | h9673c
                                        · have p9673_0 := h9673c.1
                                          have p9673_1 := h9673c.2.1
                                          have p9673_2 := h9673c.2.2.1
                                          have p9673_3 := h9673c.2.2.2
                                          linarith only [hlam, p9673_0]
                                        · have p9673_0 := h9673c.1
                                          have p9673_1 := h9673c.2.1
                                          have p9673_2 := h9673c.2.2.1
                                          have p9673_3 := h9673c.2.2.2
                                          rcases p9673_3 (m.d 0 3) (by simp) with h9675 | h9675
                                          · rcases p9673_3 (m.d 1 3) (by simp) with h9676 | h9676
                                            · linarith only [h1, h9676, hlam]
                                            · rcases p9673_3 (m.d 2 3) (by simp) with h9678 | h9678
                                              · rcases p9673_3 (m.d 3 4) (by simp) with h9679 | h9679
                                                · linarith only [h9441, h9679, hlam]
                                                · rcases p9673_3 (m.d 3 5) (by simp) with h9681 | h9681
                                                  · linarith only [h9442, h9681, hlam]
                                                  · linarith only [h9451, h9681, hlam]
                                              · linarith only [h9445, h9678, hlam]
                                          · linarith only [h1, h9675, hlam]
                                        · have p9673_0 := h9673c.1
                                          have p9673_1 := h9673c.2.1
                                          have p9673_2 := h9673c.2.2.1
                                          have p9673_3 := h9673c.2.2.2
                                          linarith only [h4, hlam, p9673_1]
                                        · have p9673_0 := h9673c.1
                                          have p9673_1 := h9673c.2.1
                                          have p9673_2 := h9673c.2.2.1
                                          have p9673_3 := h9673c.2.2.2
                                          linarith only [h9442, h9445, h9447, h9451, h9633, hlam, p9673_2]
                                        · have p9673_0 := h9673c.1
                                          have p9673_1 := h9673c.2.1
                                          have p9673_2 := h9673c.2.2.1
                                          have p9673_3 := h9673c.2.2.2
                                          linarith only [h4, h9445, h9447, h9451, h9633, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9673_1]
                                        · have p9673_0 := h9673c.1
                                          have p9673_1 := h9673c.2.1
                                          have p9673_2 := h9673c.2.2.1
                                          have p9673_3 := h9673c.2.2.2
                                          linarith only [h1, hlam, p9673_0]
                                        · have p9673_0 := h9673c.1
                                          have p9673_1 := h9673c.2.1
                                          have p9673_2 := h9673c.2.2.1
                                          have p9673_3 := h9673c.2.2.2
                                          linarith only [hlam, p9673_0]
                                        · have p9673_0 := h9673c.1
                                          have p9673_1 := h9673c.2.1
                                          have p9673_2 := h9673c.2.2.1
                                          have p9673_3 := h9673c.2.2.2
                                          linarith only [h9445, hlam, p9673_1]
                                        · have p9673_0 := h9673c.1
                                          have p9673_1 := h9673c.2.1
                                          have p9673_2 := h9673c.2.2.1
                                          have p9673_3 := h9673c.2.2.2
                                          linarith only [h8675, h9442, h9451, h9635, hc34, hc45, hlam, hphi, p9673_1]
                                        · have p9673_0 := h9673c.1
                                          have p9673_1 := h9673c.2.1
                                          have p9673_2 := h9673c.2.2.1
                                          have p9673_3 := h9673c.2.2.2
                                          linarith only [h9451, hlam, p9673_0]
                                        · have p9673_0 := h9673c.1
                                          have p9673_1 := h9673c.2.1
                                          have p9673_2 := h9673c.2.2.1
                                          have p9673_3 := h9673c.2.2.2
                                          linarith only [h9442, h9451, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p9673_1]
                                        · have p9673_0 := h9673c.1
                                          have p9673_1 := h9673c.2.1
                                          have p9673_2 := h9673c.2.2.1
                                          have p9673_3 := h9673c.2.2.2
                                          rcases p9673_3 (m.d 0 3) (by simp) with h9695 | h9695
                                          · linarith only [h4, h9695, hlam]
                                          · linarith only [h1, h9695, hlam]
                                        · have p9673_0 := h9673c.1
                                          have p9673_1 := h9673c.2.1
                                          have p9673_2 := h9673c.2.2.1
                                          have p9673_3 := h9673c.2.2.2
                                          linarith only [hlam, p9673_0]
                                        · have p9673_0 := h9673c.1
                                          have p9673_1 := h9673c.2.1
                                          have p9673_2 := h9673c.2.2.1
                                          have p9673_3 := h9673c.2.2.2
                                          linarith only [h4, h9442, h9445, h9447, h9451, h9633, hlam, p9673_2]
                                        · have p9673_0 := h9673c.1
                                          have p9673_1 := h9673c.2.1
                                          have p9673_2 := h9673c.2.2.1
                                          have p9673_3 := h9673c.2.2.2
                                          linarith only [h9445, h9447, h9451, h9633, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9673_1]
                                        · have p9673_0 := h9673c.1
                                          have p9673_1 := h9673c.2.1
                                          have p9673_2 := h9673c.2.2.1
                                          have p9673_3 := h9673c.2.2.2
                                          linarith only [h9441, hlam, p9673_0]
                                        · have p9673_0 := h9673c.1
                                          have p9673_1 := h9673c.2.1
                                          have p9673_2 := h9673c.2.2.1
                                          have p9673_3 := h9673c.2.2.2
                                          linarith only [h9450, hlam, p9673_0]
                                        · have p9673_0 := h9673c.1
                                          have p9673_1 := h9673c.2.1
                                          have p9673_2 := h9673c.2.2.1
                                          have p9673_3 := h9673c.2.2.2
                                          linarith only [h9633, hlam, p9673_0]
                                        · have p9673_0 := h9673c.1
                                          have p9673_1 := h9673c.2.1
                                          have p9673_2 := h9673c.2.2.1
                                          have p9673_3 := h9673c.2.2.2
                                          linarith only [hlam, p9673_0]
                                        · have p9673_0 := h9673c.1
                                          have p9673_1 := h9673c.2.1
                                          have p9673_2 := h9673c.2.2.1
                                          have p9673_3 := h9673c.2.2.2
                                          linarith only [h9637, hlam, p9673_1]
                                        · have p9673_0 := h9673c.1
                                          have p9673_1 := h9673c.2.1
                                          have p9673_2 := h9673c.2.2.1
                                          have p9673_3 := h9673c.2.2.2
                                          linarith only [h9442, hlam, p9673_0]
                                        · have p9673_0 := h9673c.1
                                          have p9673_1 := h9673c.2.1
                                          have p9673_2 := h9673c.2.2.1
                                          have p9673_3 := h9673c.2.2.2
                                          linarith only [h9442, h9445, h9447, h9633, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p9673_1]
                                        · have p9673_0 := h9673c.1
                                          have p9673_1 := h9673c.2.1
                                          have p9673_2 := h9673c.2.2.1
                                          have p9673_3 := h9673c.2.2.2
                                          linarith only [h9634, hlam, p9673_0]
                                        · have p9673_0 := h9673c.1
                                          have p9673_1 := h9673c.2.1
                                          have p9673_2 := h9673c.2.2.1
                                          have p9673_3 := h9673c.2.2.2
                                          rcases p9673_3 (m.d 0 3) (by simp) with h9709 | h9709
                                          · rcases p9673_3 (m.d 1 3) (by simp) with h9710 | h9710
                                            · linarith only [h9451, h9710, hlam]
                                            · linarith only [h9450, h9710, hlam]
                                          · linarith only [h9441, h9709, hlam]
                                        · have p9673_0 := h9673c.1
                                          have p9673_1 := h9673c.2.1
                                          have p9673_2 := h9673c.2.2.1
                                          have p9673_3 := h9673c.2.2.2
                                          linarith only [hlam, p9673_0]
                              · linarith only [h9664, hlam, p9639_0]
                            · have p9639_0 := h9639c.1
                              have p9639_1 := h9639c.2.1
                              have p9639_2 := h9639c.2.2.1
                              have p9639_3 := h9639c.2.2.2
                              linarith only [h0, hlam, p9639_0]
                            · have p9639_0 := h9639c.1
                              have p9639_1 := h9639c.2.1
                              have p9639_2 := h9639c.2.2.1
                              have p9639_3 := h9639c.2.2.2
                              linarith only [hlam, p9639_0]
                            · have p9639_0 := h9639c.1
                              have p9639_1 := h9639c.2.1
                              have p9639_2 := h9639c.2.2.1
                              have p9639_3 := h9639c.2.2.2
                              linarith only [h9445, hlam, p9639_0]
                            · have p9639_0 := h9639c.1
                              have p9639_1 := h9639c.2.1
                              have p9639_2 := h9639c.2.2.1
                              have p9639_3 := h9639c.2.2.2
                              linarith only [h0, h8675, h9635, hc14, hc45, hlam, hphi, p9639_1]
                            · have p9639_0 := h9639c.1
                              have p9639_1 := h9639c.2.1
                              have p9639_2 := h9639c.2.2.1
                              have p9639_3 := h9639c.2.2.2
                              linarith only [h9448, hlam, p9639_0]
                            · have p9639_0 := h9639c.1
                              have p9639_1 := h9639c.2.1
                              have p9639_2 := h9639c.2.2.1
                              have p9639_3 := h9639c.2.2.2
                              linarith only [h1, hlam, p9639_0]
                            · have p9639_0 := h9639c.1
                              have p9639_1 := h9639c.2.1
                              have p9639_2 := h9639c.2.2.1
                              have p9639_3 := h9639c.2.2.2
                              linarith only [h1, h9447, h9633, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9639_1]
                            · have p9639_0 := h9639c.1
                              have p9639_1 := h9639c.2.1
                              have p9639_2 := h9639c.2.2.1
                              have p9639_3 := h9639c.2.2.2
                              linarith only [hlam, p9639_0]
                            · have p9639_0 := h9639c.1
                              have p9639_1 := h9639c.2.1
                              have p9639_2 := h9639c.2.2.1
                              have p9639_3 := h9639c.2.2.2
                              linarith only [h4, h9442, h9447, h9451, h9633, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9639_1]
                            · have p9639_0 := h9639c.1
                              have p9639_1 := h9639c.2.1
                              have p9639_2 := h9639c.2.2.1
                              have p9639_3 := h9639c.2.2.2
                              linarith only [h9451, hlam, p9639_1]
                            · have p9639_0 := h9639c.1
                              have p9639_1 := h9639c.2.1
                              have p9639_2 := h9639c.2.2.1
                              have p9639_3 := h9639c.2.2.2
                              linarith only [h2, hlam, p9639_0]
                            · have p9639_0 := h9639c.1
                              have p9639_1 := h9639c.2.1
                              have p9639_2 := h9639c.2.2.1
                              have p9639_3 := h9639c.2.2.2
                              linarith only [h9447, hlam, p9639_1]
                            · have p9639_0 := h9639c.1
                              have p9639_1 := h9639c.2.1
                              have p9639_2 := h9639c.2.2.1
                              have p9639_3 := h9639c.2.2.2
                              linarith only [h9450, hlam, p9639_0]
                            · have p9639_0 := h9639c.1
                              have p9639_1 := h9639c.2.1
                              have p9639_2 := h9639c.2.2.1
                              have p9639_3 := h9639c.2.2.2
                              linarith only [hlam, p9639_0]
                            · have p9639_0 := h9639c.1
                              have p9639_1 := h9639c.2.1
                              have p9639_2 := h9639c.2.2.1
                              have p9639_3 := h9639c.2.2.2
                              linarith only [h9631, hlam, p9639_1]
                            · have p9639_0 := h9639c.1
                              have p9639_1 := h9639c.2.1
                              have p9639_2 := h9639c.2.2.1
                              have p9639_3 := h9639c.2.2.2
                              linarith only [h3, hlam, p9639_0]
                            · have p9639_0 := h9639c.1
                              have p9639_1 := h9639c.2.1
                              have p9639_2 := h9639c.2.2.1
                              have p9639_3 := h9639c.2.2.2
                              linarith only [h3, h9447, h9633, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9639_1]
                            · have p9639_0 := h9639c.1
                              have p9639_1 := h9639c.2.1
                              have p9639_2 := h9639c.2.2.1
                              have p9639_3 := h9639c.2.2.2
                              linarith only [h4, h9442, h9445, h9447, h9451, h9633, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9639_1]
                            · have p9639_0 := h9639c.1
                              have p9639_1 := h9639c.2.1
                              have p9639_2 := h9639c.2.2.1
                              have p9639_3 := h9639c.2.2.2
                              rcases p9639_3 (m.d 0 1) (by simp) with h9734 | h9734
                              · rcases p9639_3 (m.d 1 2) (by simp) with h9735 | h9735
                                · linarith only [h9448, h9735, hlam]
                                · linarith only [h9447, h9735, hlam]
                              · linarith only [h2, h9734, hlam]
                            · have p9639_0 := h9639c.1
                              have p9639_1 := h9639c.2.1
                              have p9639_2 := h9639c.2.2.1
                              have p9639_3 := h9639c.2.2.2
                              linarith only [hlam, p9639_0]
                      · linarith only [h4, h9442, h9634, hlam]
                    · linarith only [h4, h9441, h9633, hlam]
              · linarith only [h9441, h9443, h9445, h9447, h9450, hc24, hc45, hlam, hphi]
          · linarith only [h4, h8674, h9447, hc12, hc23, hlam, hphi]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h9744 | h9744
      · linarith only [h8674, h8675, h9744, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h9746 | h9746
        · linarith only [h0, h4, h9746, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h9748 | h9748
          · rcases m.htr 1 2 5 (by decide) (by decide) with h9749 | h9749
            · linarith only [h0, h8675, h9749, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9751 | h9751
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9752 | h9752
                · linarith only [h1, h9442, h9752, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9754 | h9754
                  · linarith only [h2, h9744, h9754, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9756 | h9756
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9757 | h9757
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9758 | h9758
                        · linarith only [h4, h8674, h9442, h9757, h9758, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9760 | h9760
                          · linarith only [h9441, h9442, h9757, h9758, h9760, hlam]
                          · rcases h1bigk with h9762c | h9762c | h9762c | h9762c | h9762c | h9762c | h9762c | h9762c | h9762c | h9762c | h9762c | h9762c | h9762c | h9762c | h9762c | h9762c | h9762c | h9762c | h9762c | h9762c | h9762c | h9762c | h9762c | h9762c | h9762c
                            · have p9762_0 := h9762c.1
                              have p9762_1 := h9762c.2.1
                              have p9762_2 := h9762c.2.2.1
                              have p9762_3 := h9762c.2.2.2
                              linarith only [hlam, p9762_0]
                            · have p9762_0 := h9762c.1
                              have p9762_1 := h9762c.2.1
                              have p9762_2 := h9762c.2.2.1
                              have p9762_3 := h9762c.2.2.2
                              rcases p9762_3 (m.d 0 1) (by simp) with h9764 | h9764
                              · rcases p9762_3 (m.d 1 2) (by simp) with h9765 | h9765
                                · linarith only [h9765, hlam, p9762_0]
                                · rcases p9762_3 (m.d 1 3) (by simp) with h9767 | h9767
                                  · linarith only [h1, h9767, hlam]
                                  · linarith only [h9746, h9767, hlam]
                              · linarith only [h9764, hlam, p9762_0]
                            · have p9762_0 := h9762c.1
                              have p9762_1 := h9762c.2.1
                              have p9762_2 := h9762c.2.2.1
                              have p9762_3 := h9762c.2.2.2
                              rcases p9762_3 (m.d 0 1) (by simp) with h9771 | h9771
                              · rcases p9762_3 (m.d 1 2) (by simp) with h9772 | h9772
                                · linarith only [h0, h9772, hlam]
                                · rcases p9762_3 (m.d 1 3) (by simp) with h9774 | h9774
                                  · linarith only [h9774, hlam, p9762_0]
                                  · rcases p9762_3 (m.d 1 4) (by simp) with h9776 | h9776
                                    · linarith only [h2, h9776, hlam]
                                    · rcases p9762_3 (m.d 1 5) (by simp) with h9778 | h9778
                                      · linarith only [h3, h9778, hlam]
                                      · linarith only [h9752, h9778, hlam]
                              · linarith only [h9771, hlam, p9762_0]
                            · have p9762_0 := h9762c.1
                              have p9762_1 := h9762c.2.1
                              have p9762_2 := h9762c.2.2.1
                              have p9762_3 := h9762c.2.2.2
                              rcases p9762_3 (m.d 0 1) (by simp) with h9782 | h9782
                              · rcases p9762_3 (m.d 1 2) (by simp) with h9783 | h9783
                                · linarith only [h0, h9783, hlam]
                                · linarith only [h9748, h9783, hlam]
                              · linarith only [h9782, hlam, p9762_0]
                            · have p9762_0 := h9762c.1
                              have p9762_1 := h9762c.2.1
                              have p9762_2 := h9762c.2.2.1
                              have p9762_3 := h9762c.2.2.2
                              rcases p9762_3 (m.d 0 1) (by simp) with h9787 | h9787
                              · rcases p9762_3 (m.d 1 2) (by simp) with h9788 | h9788
                                · linarith only [h0, h9788, hlam]
                                · rcases p9762_3 (m.d 1 3) (by simp) with h9790 | h9790
                                  · linarith only [h1, h9790, hlam]
                                  · rcases p9762_3 (m.d 1 4) (by simp) with h9792 | h9792
                                    · linarith only [h2, h9792, hlam]
                                    · rcases p9762_3 (m.d 1 5) (by simp) with h9794 | h9794
                                      · linarith only [h9794, hlam, p9762_0]
                                      · rcases h3bigk with h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c | h9796c
                                        · have p9796_0 := h9796c.1
                                          have p9796_1 := h9796c.2.1
                                          have p9796_2 := h9796c.2.2.1
                                          have p9796_3 := h9796c.2.2.2
                                          linarith only [hlam, p9796_0]
                                        · have p9796_0 := h9796c.1
                                          have p9796_1 := h9796c.2.1
                                          have p9796_2 := h9796c.2.2.1
                                          have p9796_3 := h9796c.2.2.2
                                          linarith only [h9442, h9757, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p9796_1]
                                        · have p9796_0 := h9796c.1
                                          have p9796_1 := h9796c.2.1
                                          have p9796_2 := h9796c.2.2.1
                                          have p9796_3 := h9796c.2.2.2
                                          linarith only [h4, hlam, p9796_1]
                                        · have p9796_0 := h9796c.1
                                          have p9796_1 := h9796c.2.1
                                          have p9796_2 := h9796c.2.2.1
                                          have p9796_3 := h9796c.2.2.2
                                          linarith only [h9442, h9757, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9796_1]
                                        · have p9796_0 := h9796c.1
                                          have p9796_1 := h9796c.2.1
                                          have p9796_2 := h9796c.2.2.1
                                          have p9796_3 := h9796c.2.2.2
                                          linarith only [h9442, hlam, p9796_0]
                                        · have p9796_0 := h9796c.1
                                          have p9796_1 := h9796c.2.1
                                          have p9796_2 := h9796c.2.2.1
                                          have p9796_3 := h9796c.2.2.2
                                          linarith only [h1, hlam, p9796_0]
                                        · have p9796_0 := h9796c.1
                                          have p9796_1 := h9796c.2.1
                                          have p9796_2 := h9796c.2.2.1
                                          have p9796_3 := h9796c.2.2.2
                                          linarith only [hlam, p9796_0]
                                        · have p9796_0 := h9796c.1
                                          have p9796_1 := h9796c.2.1
                                          have p9796_2 := h9796c.2.2.1
                                          have p9796_3 := h9796c.2.2.2
                                          linarith only [h9746, hlam, p9796_1]
                                        · have p9796_0 := h9796c.1
                                          have p9796_1 := h9796c.2.1
                                          have p9796_2 := h9796c.2.2.1
                                          have p9796_3 := h9796c.2.2.2
                                          linarith only [h1, h9442, h9757, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9796_1]
                                        · have p9796_0 := h9796c.1
                                          have p9796_1 := h9796c.2.1
                                          have p9796_2 := h9796c.2.2.1
                                          have p9796_3 := h9796c.2.2.2
                                          linarith only [h9752, hlam, p9796_0]
                                        · have p9796_0 := h9796c.1
                                          have p9796_1 := h9796c.2.1
                                          have p9796_2 := h9796c.2.2.1
                                          have p9796_3 := h9796c.2.2.2
                                          rcases p9796_3 (m.d 0 3) (by simp) with h9807 | h9807
                                          · linarith only [h4, h9807, hlam]
                                          · rcases p9796_3 (m.d 1 3) (by simp) with h9809 | h9809
                                            · linarith only [h9746, h9809, hlam]
                                            · rcases p9796_3 (m.d 2 3) (by simp) with h9811 | h9811
                                              · rcases p9796_3 (m.d 3 4) (by simp) with h9812 | h9812
                                                · linarith only [h9756, h9812, hlam]
                                                · rcases p9796_3 (m.d 3 5) (by simp) with h9814 | h9814
                                                  · linarith only [h9757, h9814, hlam]
                                                  · linarith only [h9442, h9814, hlam]
                                              · linarith only [h4, h9811, hlam]
                                        · have p9796_0 := h9796c.1
                                          have p9796_1 := h9796c.2.1
                                          have p9796_2 := h9796c.2.2.1
                                          have p9796_3 := h9796c.2.2.2
                                          rcases p9796_3 (m.d 0 3) (by simp) with h9818 | h9818
                                          · linarith only [h4, h9818, hlam]
                                          · linarith only [h1, h9818, hlam]
                                        · have p9796_0 := h9796c.1
                                          have p9796_1 := h9796c.2.1
                                          have p9796_2 := h9796c.2.2.1
                                          have p9796_3 := h9796c.2.2.2
                                          linarith only [hlam, p9796_0]
                                        · have p9796_0 := h9796c.1
                                          have p9796_1 := h9796c.2.1
                                          have p9796_2 := h9796c.2.2.1
                                          have p9796_3 := h9796c.2.2.2
                                          linarith only [h9441, h9442, h9757, hlam, p9796_2]
                                        · have p9796_0 := h9796c.1
                                          have p9796_1 := h9796c.2.1
                                          have p9796_2 := h9796c.2.2.1
                                          have p9796_3 := h9796c.2.2.2
                                          linarith only [h4, h9442, hc02, hc23, hlam, hphi, p9796_1]
                                        · have p9796_0 := h9796c.1
                                          have p9796_1 := h9796c.2.1
                                          have p9796_2 := h9796c.2.2.1
                                          have p9796_3 := h9796c.2.2.2
                                          linarith only [h9441, hlam, p9796_0]
                                        · have p9796_0 := h9796c.1
                                          have p9796_1 := h9796c.2.1
                                          have p9796_2 := h9796c.2.2.1
                                          have p9796_3 := h9796c.2.2.2
                                          linarith only [h9751, hlam, p9796_0]
                                        · have p9796_0 := h9796c.1
                                          have p9796_1 := h9796c.2.1
                                          have p9796_2 := h9796c.2.2.1
                                          have p9796_3 := h9796c.2.2.2
                                          linarith only [h9756, hlam, p9796_0]
                                        · have p9796_0 := h9796c.1
                                          have p9796_1 := h9796c.2.1
                                          have p9796_2 := h9796c.2.2.1
                                          have p9796_3 := h9796c.2.2.2
                                          linarith only [hlam, p9796_0]
                                        · have p9796_0 := h9796c.1
                                          have p9796_1 := h9796c.2.1
                                          have p9796_2 := h9796c.2.2.1
                                          have p9796_3 := h9796c.2.2.2
                                          linarith only [h9760, hlam, p9796_1]
                                        · have p9796_0 := h9796c.1
                                          have p9796_1 := h9796c.2.1
                                          have p9796_2 := h9796c.2.2.1
                                          have p9796_3 := h9796c.2.2.2
                                          linarith only [h0, h4, h9748, h9757, h9758, hc24, hc45, hlam, hphi, p9796_1]
                                        · have p9796_0 := h9796c.1
                                          have p9796_1 := h9796c.2.1
                                          have p9796_2 := h9796c.2.2.1
                                          have p9796_3 := h9796c.2.2.2
                                          linarith only [h9746, h9748, h9757, h9758, hc24, hc45, hlam, hphi, p9796_1]
                                        · have p9796_0 := h9796c.1
                                          have p9796_1 := h9796c.2.1
                                          have p9796_2 := h9796c.2.2.1
                                          have p9796_3 := h9796c.2.2.2
                                          linarith only [h9757, hlam, p9796_0]
                                        · have p9796_0 := h9796c.1
                                          have p9796_1 := h9796c.2.1
                                          have p9796_2 := h9796c.2.2.1
                                          have p9796_3 := h9796c.2.2.2
                                          rcases p9796_3 (m.d 0 3) (by simp) with h9832 | h9832
                                          · linarith only [h9442, h9832, hlam]
                                          · linarith only [h9441, h9832, hlam]
                                        · have p9796_0 := h9796c.1
                                          have p9796_1 := h9796c.2.1
                                          have p9796_2 := h9796c.2.2.1
                                          have p9796_3 := h9796c.2.2.2
                                          linarith only [hlam, p9796_0]
                              · linarith only [h9787, hlam, p9762_0]
                            · have p9762_0 := h9762c.1
                              have p9762_1 := h9762c.2.1
                              have p9762_2 := h9762c.2.2.1
                              have p9762_3 := h9762c.2.2.2
                              linarith only [h0, hlam, p9762_0]
                            · have p9762_0 := h9762c.1
                              have p9762_1 := h9762c.2.1
                              have p9762_2 := h9762c.2.2.1
                              have p9762_3 := h9762c.2.2.2
                              linarith only [hlam, p9762_0]
                            · have p9762_0 := h9762c.1
                              have p9762_1 := h9762c.2.1
                              have p9762_2 := h9762c.2.2.1
                              have p9762_3 := h9762c.2.2.2
                              linarith only [h9746, hlam, p9762_0]
                            · have p9762_0 := h9762c.1
                              have p9762_1 := h9762c.2.1
                              have p9762_2 := h9762c.2.2.1
                              have p9762_3 := h9762c.2.2.2
                              linarith only [h0, h8675, h9758, hc14, hc45, hlam, hphi, p9762_1]
                            · have p9762_0 := h9762c.1
                              have p9762_1 := h9762c.2.1
                              have p9762_2 := h9762c.2.2.1
                              have p9762_3 := h9762c.2.2.2
                              linarith only [h9749, hlam, p9762_0]
                            · have p9762_0 := h9762c.1
                              have p9762_1 := h9762c.2.1
                              have p9762_2 := h9762c.2.2.1
                              have p9762_3 := h9762c.2.2.2
                              linarith only [h1, hlam, p9762_0]
                            · have p9762_0 := h9762c.1
                              have p9762_1 := h9762c.2.1
                              have p9762_2 := h9762c.2.2.1
                              have p9762_3 := h9762c.2.2.2
                              linarith only [h1, h9442, h9757, hc12, hc23, hlam, hphi, p9762_1]
                            · have p9762_0 := h9762c.1
                              have p9762_1 := h9762c.2.1
                              have p9762_2 := h9762c.2.2.1
                              have p9762_3 := h9762c.2.2.2
                              linarith only [hlam, p9762_0]
                            · have p9762_0 := h9762c.1
                              have p9762_1 := h9762c.2.1
                              have p9762_2 := h9762c.2.2.1
                              have p9762_3 := h9762c.2.2.2
                              linarith only [h1, h9442, h9748, h9756, h9757, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9762_1]
                            · have p9762_0 := h9762c.1
                              have p9762_1 := h9762c.2.1
                              have p9762_2 := h9762c.2.2.1
                              have p9762_3 := h9762c.2.2.2
                              linarith only [h9752, hlam, p9762_1]
                            · have p9762_0 := h9762c.1
                              have p9762_1 := h9762c.2.1
                              have p9762_2 := h9762c.2.2.1
                              have p9762_3 := h9762c.2.2.2
                              linarith only [h2, hlam, p9762_0]
                            · have p9762_0 := h9762c.1
                              have p9762_1 := h9762c.2.1
                              have p9762_2 := h9762c.2.2.1
                              have p9762_3 := h9762c.2.2.2
                              linarith only [h9748, hlam, p9762_1]
                            · have p9762_0 := h9762c.1
                              have p9762_1 := h9762c.2.1
                              have p9762_2 := h9762c.2.2.1
                              have p9762_3 := h9762c.2.2.2
                              linarith only [h9751, hlam, p9762_0]
                            · have p9762_0 := h9762c.1
                              have p9762_1 := h9762c.2.1
                              have p9762_2 := h9762c.2.2.1
                              have p9762_3 := h9762c.2.2.2
                              linarith only [hlam, p9762_0]
                            · have p9762_0 := h9762c.1
                              have p9762_1 := h9762c.2.1
                              have p9762_2 := h9762c.2.2.1
                              have p9762_3 := h9762c.2.2.2
                              linarith only [h9754, hlam, p9762_1]
                            · have p9762_0 := h9762c.1
                              have p9762_1 := h9762c.2.1
                              have p9762_2 := h9762c.2.2.1
                              have p9762_3 := h9762c.2.2.2
                              linarith only [h3, hlam, p9762_0]
                            · have p9762_0 := h9762c.1
                              have p9762_1 := h9762c.2.1
                              have p9762_2 := h9762c.2.2.1
                              have p9762_3 := h9762c.2.2.2
                              linarith only [h3, h9442, h9748, h9756, h9757, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9762_1]
                            · have p9762_0 := h9762c.1
                              have p9762_1 := h9762c.2.1
                              have p9762_2 := h9762c.2.2.1
                              have p9762_3 := h9762c.2.2.2
                              linarith only [h3, h9442, h9746, h9748, h9756, h9757, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9762_1]
                            · have p9762_0 := h9762c.1
                              have p9762_1 := h9762c.2.1
                              have p9762_2 := h9762c.2.2.1
                              have p9762_3 := h9762c.2.2.2
                              rcases p9762_3 (m.d 0 1) (by simp) with h9855 | h9855
                              · rcases p9762_3 (m.d 1 2) (by simp) with h9856 | h9856
                                · linarith only [h9749, h9856, hlam]
                                · linarith only [h9748, h9856, hlam]
                              · linarith only [h2, h9855, hlam]
                            · have p9762_0 := h9762c.1
                              have p9762_1 := h9762c.2.1
                              have p9762_2 := h9762c.2.2.1
                              have p9762_3 := h9762c.2.2.2
                              linarith only [hlam, p9762_0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9861 | h9861
                        · linarith only [h0, h4, h9748, h9757, h9861, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9863 | h9863
                          · linarith only [h0, h4, h8675, h9748, h9756, h9757, h9861, h9863, hc05, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h0, h4, h9748, h9756, h9757, h9863, hc34, hc45, hlam, hphi]
                    · linarith only [h4, h9441, h9756, hlam]
              · linarith only [h9441, h9442, h9746, h9748, h9751, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
          · linarith only [h4, h8674, h9748, hc12, hc23, hlam, hphi]
  · linarith only [h4, h8674, h9441, hlam]

set_option maxHeartbeats 9670000 in
set_option maxHeartbeats 9670000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s10_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h8674 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 2 5 (by decide) (by decide) with h8675 | h8675
  · exact r1l7_11_13_25_L_I_L_I_H_I_s10_x0_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h8674 h8675
  · exact r1l7_11_13_25_L_I_L_I_H_I_s10_x0_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h8674 h8675

set_option maxHeartbeats 9670000 in
set_option maxHeartbeats 9670000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s10_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h8674 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  exact r1l7_11_13_25_L_I_L_I_H_I_s11 m hb1 hb3 hb5 h0 h1 h2 h3 h4 h8674

set_option maxHeartbeats 9670000 in
set_option maxHeartbeats 9670000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s10 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 2 4 (by decide) (by decide) with h8674 | h8674
  · exact r1l7_11_13_25_L_I_L_I_H_I_s10_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h8674
  · exact r1l7_11_13_25_L_I_L_I_H_I_s10_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h8674

set_option maxHeartbeats 27010000 in
set_option maxHeartbeats 27010000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s3 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_11_13_25_L_I_L_I_H_I_s4 m hb1 hb3 hb5 h0 h1 h2 h3 h4
  · exact r1l7_11_13_25_L_I_L_I_H_I_s10 m hb1 hb3 hb5 h0 h1 h2 h3 h4

set_option maxHeartbeats 27258000 in
set_option maxHeartbeats 27258000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s2 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_11_13_25_L_I_L_I_H_I_s3 m hb1 hb3 hb5 h0 h1 h2 h3
  · rcases m.htr 0 2 3 (by decide) (by decide) with h13509 | h13509
    · rcases m.htr 0 2 4 (by decide) (by decide) with h13510 | h13510
      · rcases m.htr 0 2 5 (by decide) (by decide) with h13511 | h13511
        · linarith only [h0, h13511, h3, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h13513 | h13513
          · rcases m.htr 0 3 5 (by decide) (by decide) with h13514 | h13514
            · linarith only [h0, h13509, h13514, h3, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h13516 | h13516
              · linarith only [h0, h13509, h13513, h13516, h3, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h13518 | h13518
                · rcases m.htr 1 2 4 (by decide) (by decide) with h13519 | h13519
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h13520 | h13520
                    · linarith only [h0, h13511, h13520, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h13522 | h13522
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h13523 | h13523
                        · linarith only [h1, h13514, h13523, hlam]
                        · linarith only [h0, h13518, h13523, h3, hc23, hc35, hlam, hphi]
                      · linarith only [h13513, h13514, h13522, hc13, hc35, hlam, hphi]
                  · linarith only [h0, h13510, h13518, h13519, h3, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h13509, h13511, h13518, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h13529 | h13529
            · linarith only [h1, h13529, h3, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h13531 | h13531
              · linarith only [h0, h13510, h13531, h3, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h13533 | h13533
                · rcases m.htr 1 2 4 (by decide) (by decide) with h13534 | h13534
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h13535 | h13535
                    · linarith only [h0, h13511, h13535, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h13537 | h13537
                      · linarith only [h1, h13513, h13537, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h13539 | h13539
                        · linarith only [h0, h1, h13513, h13529, h13539, h3, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h13533, h13539, h3, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h13510, h13533, h13534, h3, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h13509, h13511, h13533, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h13544 | h13544
        · linarith only [h13510, h13544, h2, h3, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h13546 | h13546
          · linarith only [h13509, h13510, h13546, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h13548 | h13548
            · linarith only [h0, h13509, h13548, h3, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h13550 | h13550
              · linarith only [h13550, h2, h3, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h13552 | h13552
                · rcases m.htr 1 2 4 (by decide) (by decide) with h13553 | h13553
                  · linarith only [h0, h13510, h13553, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h13555 | h13555
                    · linarith only [h0, h13544, h13555, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h13557 | h13557
                      · linarith only [h1, h13546, h13555, h13557, h3, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h13559 | h13559
                        · linarith only [h1, h13548, h13559, hlam]
                        · linarith only [h0, h13552, h13559, h3, hc23, hc35, hlam, hphi]
                · linarith only [h13509, h13510, h13552, hc12, hc24, hlam, hphi]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h13563 | h13563
      · rcases m.htr 0 2 5 (by decide) (by decide) with h13564 | h13564
        · linarith only [h0, h13564, h3, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h13566 | h13566
          · rcases m.htr 0 3 5 (by decide) (by decide) with h13567 | h13567
            · linarith only [h1, h13567, h3, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h13569 | h13569
              · linarith only [h0, h13563, h13569, h3, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h13571 | h13571
                · linarith only [h0, h13509, h13571, h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h13573 | h13573
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h13574 | h13574
                    · linarith only [h0, h13564, h13574, h3, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h13576 | h13576
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h13577 | h13577
                        · linarith only [h1, h13509, h13567, h13574, h13577, h3, hc02, hc25, hlam, hphi]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h13579 | h13579
                          · linarith only [h13569, h13579, h2, h3, hlam]
                          · linarith only [h1, h13571, h13573, h13579, h3, hc24, hc45, hlam, hphi]
                      · linarith only [h1, h13566, h13571, h13573, h13576, h3, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h13509, h13563, h13573, hc12, hc23, hlam, hphi]
          · linarith only [h13509, h13563, h13566, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h13585 | h13585
        · linarith only [h0, h13585, h3, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h13587 | h13587
          · rcases m.htr 0 3 5 (by decide) (by decide) with h13588 | h13588
            · linarith only [h1, h13588, h3, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h13590 | h13590
              · linarith only [h1, h13587, h13590, h3, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h13592 | h13592
                · linarith only [h0, h13509, h13592, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h13594 | h13594
                  · linarith only [h0, h13563, h13594, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h13596 | h13596
                    · linarith only [h1, h13585, h13592, h13596, h3, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h13598 | h13598
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h13599 | h13599
                        · linarith only [h1, h13588, h13596, h13599, h3, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h13601 | h13601
                          · linarith only [h1, h13590, h13598, h13601, h3, hlam]
                          · linarith only [h1, h13598, h13601, h3, hc34, hc45, hlam, hphi]
                      · linarith only [h13587, h13588, h13598, hc13, hc35, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h13605 | h13605
            · linarith only [h1, h13605, h3, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h13607 | h13607
              · linarith only [h13607, h2, h3, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h13609 | h13609
                · linarith only [h0, h13509, h13609, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h13611 | h13611
                  · linarith only [h0, h13563, h13611, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h13613 | h13613
                    · linarith only [h0, h13585, h13613, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h13615 | h13615
                      · linarith only [h1, h13587, h13615, h3, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h13617 | h13617
                        · linarith only [h13605, h13615, h13617, h2, h3, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h13619 | h13619
                          · linarith only [h13607, h13617, h13619, h2, h3, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13621 | h13621
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h13622 | h13622
                              · linarith only [h13609, h13615, h13617, h13622, h2, h3, hc12, hc23, hlam, hphi]
                              · linarith only [h1, h13587, h13609, h13621, h13622, hc12, hc35, hlam, hphi, ht23]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h13625 | h13625
                              · linarith only [h1, h13605, h13609, h13621, h13625, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h13627 | h13627
                                · linarith only [h13609, h13615, h13619, h13627, h2, h3, hc12, hc24, hlam, hphi]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h13629 | h13629
                                  · linarith only [h0, h13509, h13621, h13627, h13629, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h0, h13509, h13621, h13629, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 27898000 in
set_option maxHeartbeats 27898000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_11_13_25_L_I_L_I_H_I_s2 m hb1 hb3 hb5 h0 h1 h2
  · rcases m.htr 0 1 5 (by decide) (by decide) with h13632 | h13632
    · rcases m.htr 0 2 3 (by decide) (by decide) with h13633 | h13633
      · rcases m.htr 0 2 4 (by decide) (by decide) with h13634 | h13634
        · linarith only [h0, h13634, h2, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h13636 | h13636
          · rcases m.htr 0 3 4 (by decide) (by decide) with h13637 | h13637
            · linarith only [h1, h13637, h2, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h13639 | h13639
              · rcases m.htr 0 4 5 (by decide) (by decide) with h13640 | h13640
                · rcases m.htr 1 2 3 (by decide) (by decide) with h13641 | h13641
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h13642 | h13642
                    · linarith only [h0, h13634, h13642, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h13644 | h13644
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h13645 | h13645
                        · linarith only [h1, h13637, h13645, h2, hlam]
                        · linarith only [h0, h13641, h13645, h2, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h13636, h13641, h13642, h13644, h2, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h13633, h13634, h13641, hc12, hc24, hlam, hphi]
                · linarith only [h13632, h13640, h2, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h13651 | h13651
                · rcases m.htr 1 2 3 (by decide) (by decide) with h13652 | h13652
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h13653 | h13653
                    · linarith only [h0, h13634, h13653, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h13655 | h13655
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h13656 | h13656
                        · linarith only [h0, h1, h13637, h13639, h13652, h13656, h2, hc23, hc35, hlam, hphi]
                        · linarith only [h0, h13652, h13656, h2, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h13636, h13652, h13655, h2, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h13633, h13634, h13652, hc12, hc24, hlam, hphi]
                · linarith only [h0, h13636, h13651, h2, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h13662 | h13662
            · linarith only [h1, h13662, h2, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h13664 | h13664
              · linarith only [h13633, h13636, h13664, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h13666 | h13666
                · rcases m.htr 1 2 3 (by decide) (by decide) with h13667 | h13667
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h13668 | h13668
                    · linarith only [h0, h13634, h13668, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h13670 | h13670
                      · linarith only [h0, h13636, h13670, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h13672 | h13672
                        · linarith only [h0, h13662, h13667, h13672, h2, hlam]
                        · linarith only [h13632, h13667, h13670, h13672, h2, hc23, hc34, hlam, hphi]
                  · linarith only [h13633, h13636, h13667, hc12, hc25, hlam, hphi]
                · linarith only [h13632, h13666, h2, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h13677 | h13677
        · linarith only [h0, h13677, h2, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h13679 | h13679
          · rcases m.htr 0 3 4 (by decide) (by decide) with h13680 | h13680
            · linarith only [h1, h13680, h2, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h13682 | h13682
              · rcases m.htr 0 4 5 (by decide) (by decide) with h13683 | h13683
                · rcases m.htr 1 2 3 (by decide) (by decide) with h13684 | h13684
                  · linarith only [h0, h13633, h13684, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h13686 | h13686
                    · linarith only [h0, h13677, h13686, h2, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h13688 | h13688
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h13689 | h13689
                        · linarith only [h1, h13680, h13686, h13689, h2, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h13691 | h13691
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h13692 | h13692
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h13693 | h13693
                              · linarith only [h1, h13684, h13689, h13693, h2, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h13695 | h13695
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h13696 | h13696
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h13697 | h13697
                                    · rcases h1bigk with h13698c | h13698c | h13698c | h13698c | h13698c | h13698c | h13698c | h13698c | h13698c | h13698c | h13698c | h13698c | h13698c | h13698c | h13698c | h13698c | h13698c | h13698c | h13698c | h13698c | h13698c | h13698c | h13698c | h13698c | h13698c
                                      · have p13698_0 := h13698c.1
                                        have p13698_1 := h13698c.2.1
                                        have p13698_2 := h13698c.2.2.1
                                        have p13698_3 := h13698c.2.2.2
                                        linarith only [hlam, p13698_0]
                                      · have p13698_0 := h13698c.1
                                        have p13698_1 := h13698c.2.1
                                        have p13698_2 := h13698c.2.2.1
                                        have p13698_3 := h13698c.2.2.2
                                        linarith only [h13688, h13695, h13697, h2, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p13698_1]
                                      · have p13698_0 := h13698c.1
                                        have p13698_1 := h13698c.2.1
                                        have p13698_2 := h13698c.2.2.1
                                        have p13698_3 := h13698c.2.2.2
                                        linarith only [h13684, h13686, h13688, h13695, h13697, h2, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p13698_1]
                                      · have p13698_0 := h13698c.1
                                        have p13698_1 := h13698c.2.1
                                        have p13698_2 := h13698c.2.2.1
                                        have p13698_3 := h13698c.2.2.2
                                        linarith only [h2, hlam, p13698_0]
                                      · have p13698_0 := h13698c.1
                                        have p13698_1 := h13698c.2.1
                                        have p13698_2 := h13698c.2.2.1
                                        have p13698_3 := h13698c.2.2.2
                                        rcases p13698_3 (m.d 0 1) (by simp) with h13703 | h13703
                                        · rcases p13698_3 (m.d 1 2) (by simp) with h13704 | h13704
                                          · linarith only [h0, h13704, hlam]
                                          · linarith only [h13688, h13704, hlam]
                                        · linarith only [h13703, hlam, p13698_0]
                                      · have p13698_0 := h13698c.1
                                        have p13698_1 := h13698c.2.1
                                        have p13698_2 := h13698c.2.2.1
                                        have p13698_3 := h13698c.2.2.2
                                        linarith only [h0, hlam, p13698_0]
                                      · have p13698_0 := h13698c.1
                                        have p13698_1 := h13698c.2.1
                                        have p13698_2 := h13698c.2.2.1
                                        have p13698_3 := h13698c.2.2.2
                                        linarith only [hlam, p13698_0]
                                      · have p13698_0 := h13698c.1
                                        have p13698_1 := h13698c.2.1
                                        have p13698_2 := h13698c.2.2.1
                                        have p13698_3 := h13698c.2.2.2
                                        linarith only [h13684, hlam, p13698_0]
                                      · have p13698_0 := h13698c.1
                                        have p13698_1 := h13698c.2.1
                                        have p13698_2 := h13698c.2.2.1
                                        have p13698_3 := h13698c.2.2.2
                                        linarith only [h13686, hlam, p13698_0]
                                      · have p13698_0 := h13698c.1
                                        have p13698_1 := h13698c.2.1
                                        have p13698_2 := h13698c.2.2.1
                                        have p13698_3 := h13698c.2.2.2
                                        linarith only [h0, h13686, h13693, h2, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13698_1]
                                      · have p13698_0 := h13698c.1
                                        have p13698_1 := h13698c.2.1
                                        have p13698_2 := h13698c.2.2.1
                                        have p13698_3 := h13698c.2.2.2
                                        linarith only [h1, hlam, p13698_0]
                                      · have p13698_0 := h13698c.1
                                        have p13698_1 := h13698c.2.1
                                        have p13698_2 := h13698c.2.2.1
                                        have p13698_3 := h13698c.2.2.2
                                        linarith only [h1, h13686, h13693, h2, hc12, hc34, hlam, hphi, ht23, p13698_1]
                                      · have p13698_0 := h13698c.1
                                        have p13698_1 := h13698c.2.1
                                        have p13698_2 := h13698c.2.2.1
                                        have p13698_3 := h13698c.2.2.2
                                        linarith only [hlam, p13698_0]
                                      · have p13698_0 := h13698c.1
                                        have p13698_1 := h13698c.2.1
                                        have p13698_2 := h13698c.2.2.1
                                        have p13698_3 := h13698c.2.2.2
                                        linarith only [h13689, hlam, p13698_1]
                                      · have p13698_0 := h13698c.1
                                        have p13698_1 := h13698c.2.1
                                        have p13698_2 := h13698c.2.2.1
                                        have p13698_3 := h13698c.2.2.2
                                        linarith only [h1, h13686, h13688, h13693, h13695, h13697, h2, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13698_1]
                                      · have p13698_0 := h13698c.1
                                        have p13698_1 := h13698c.2.1
                                        have p13698_2 := h13698c.2.2.1
                                        have p13698_3 := h13698c.2.2.2
                                        linarith only [h1, h13686, h13693, hc13, hc34, hlam, hphi, p13698_1]
                                      · have p13698_0 := h13698c.1
                                        have p13698_1 := h13698c.2.1
                                        have p13698_2 := h13698c.2.2.1
                                        have p13698_3 := h13698c.2.2.2
                                        rcases p13698_3 (m.d 0 1) (by simp) with h13719 | h13719
                                        · linarith only [h13719, h2, hlam]
                                        · linarith only [h0, h13719, hlam]
                                      · have p13698_0 := h13698c.1
                                        have p13698_1 := h13698c.2.1
                                        have p13698_2 := h13698c.2.2.1
                                        have p13698_3 := h13698c.2.2.2
                                        rcases p13698_3 (m.d 0 1) (by simp) with h13722 | h13722
                                        · linarith only [h13722, h2, hlam]
                                        · linarith only [h1, h13722, hlam]
                                      · have p13698_0 := h13698c.1
                                        have p13698_1 := h13698c.2.1
                                        have p13698_2 := h13698c.2.2.1
                                        have p13698_3 := h13698c.2.2.2
                                        linarith only [hlam, p13698_0]
                                      · have p13698_0 := h13698c.1
                                        have p13698_1 := h13698c.2.1
                                        have p13698_2 := h13698c.2.2.1
                                        have p13698_3 := h13698c.2.2.2
                                        rcases p13698_3 (m.d 0 1) (by simp) with h13726 | h13726
                                        · linarith only [h13726, h2, hlam]
                                        · linarith only [h13632, h13726, hlam]
                                      · have p13698_0 := h13698c.1
                                        have p13698_1 := h13698c.2.1
                                        have p13698_2 := h13698c.2.2.1
                                        have p13698_3 := h13698c.2.2.2
                                        linarith only [h13632, hlam, p13698_0]
                                      · have p13698_0 := h13698c.1
                                        have p13698_1 := h13698c.2.1
                                        have p13698_2 := h13698c.2.2.1
                                        have p13698_3 := h13698c.2.2.2
                                        linarith only [h13688, hlam, p13698_1]
                                      · have p13698_0 := h13698c.1
                                        have p13698_1 := h13698c.2.1
                                        have p13698_2 := h13698c.2.2.1
                                        have p13698_3 := h13698c.2.2.2
                                        linarith only [h13691, hlam, p13698_0]
                                      · have p13698_0 := h13698c.1
                                        have p13698_1 := h13698c.2.1
                                        have p13698_2 := h13698c.2.2.1
                                        have p13698_3 := h13698c.2.2.2
                                        linarith only [h13692, hlam, p13698_0]
                                      · have p13698_0 := h13698c.1
                                        have p13698_1 := h13698c.2.1
                                        have p13698_2 := h13698c.2.2.1
                                        have p13698_3 := h13698c.2.2.2
                                        linarith only [hlam, p13698_0]
                                    · linarith only [h0, h13677, h13683, h13688, h13693, h13695, h13697, hc04, hc35, hlam, hphi, ht0b, ht5b]
                                  · linarith only [h1, h13684, h13686, h13688, h13695, h13696, h2, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                                · linarith only [h0, h13633, h13682, h13688, h13695, hc03, hc25, hlam, hphi, ht0b, ht5b]
                            · linarith only [h1, h13684, h13688, h13692, h2, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h1, h13682, h13684, h13688, h13691, h2, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h13633, h13679, h13688, hc12, hc23, hlam, hphi]
                · linarith only [h1, h13633, h13679, h13683, h2, hlam]
              · linarith only [h13633, h13679, h13682, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h13742 | h13742
            · linarith only [h1, h13742, h2, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h13744 | h13744
              · rcases m.htr 0 4 5 (by decide) (by decide) with h13745 | h13745
                · rcases m.htr 1 2 3 (by decide) (by decide) with h13746 | h13746
                  · linarith only [h0, h13633, h13746, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h13748 | h13748
                    · linarith only [h0, h13677, h13748, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h13750 | h13750
                      · linarith only [h0, h13679, h13750, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h13752 | h13752
                        · linarith only [h1, h13742, h13748, h13752, h2, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h13754 | h13754
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h13755 | h13755
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h13756 | h13756
                              · linarith only [h0, h13752, h13756, h2, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h13758 | h13758
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h13759 | h13759
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h13760 | h13760
                                    · rcases h1bigk with h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c
                                      · have p13761_0 := h13761c.1
                                        have p13761_1 := h13761c.2.1
                                        have p13761_2 := h13761c.2.2.1
                                        have p13761_3 := h13761c.2.2.2
                                        linarith only [hlam, p13761_0]
                                      · have p13761_0 := h13761c.1
                                        have p13761_1 := h13761c.2.1
                                        have p13761_2 := h13761c.2.2.1
                                        have p13761_3 := h13761c.2.2.2
                                        linarith only [h13748, h2, hc12, hc24, hlam, hphi, p13761_1]
                                      · have p13761_0 := h13761c.1
                                        have p13761_1 := h13761c.2.1
                                        have p13761_2 := h13761c.2.2.1
                                        have p13761_3 := h13761c.2.2.2
                                        linarith only [h13748, h13754, h13756, h13760, h2, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13761_1]
                                      · have p13761_0 := h13761c.1
                                        have p13761_1 := h13761c.2.1
                                        have p13761_2 := h13761c.2.2.1
                                        have p13761_3 := h13761c.2.2.2
                                        linarith only [h2, hlam, p13761_0]
                                      · have p13761_0 := h13761c.1
                                        have p13761_1 := h13761c.2.1
                                        have p13761_2 := h13761c.2.2.1
                                        have p13761_3 := h13761c.2.2.2
                                        linarith only [h13748, h13750, h13756, h2, hc12, hc34, hlam, hphi, ht23, p13761_1]
                                      · have p13761_0 := h13761c.1
                                        have p13761_1 := h13761c.2.1
                                        have p13761_2 := h13761c.2.2.1
                                        have p13761_3 := h13761c.2.2.2
                                        linarith only [h0, hlam, p13761_0]
                                      · have p13761_0 := h13761c.1
                                        have p13761_1 := h13761c.2.1
                                        have p13761_2 := h13761c.2.2.1
                                        have p13761_3 := h13761c.2.2.2
                                        linarith only [hlam, p13761_0]
                                      · have p13761_0 := h13761c.1
                                        have p13761_1 := h13761c.2.1
                                        have p13761_2 := h13761c.2.2.1
                                        have p13761_3 := h13761c.2.2.2
                                        linarith only [h13746, hlam, p13761_0]
                                      · have p13761_0 := h13761c.1
                                        have p13761_1 := h13761c.2.1
                                        have p13761_2 := h13761c.2.2.1
                                        have p13761_3 := h13761c.2.2.2
                                        linarith only [h13748, hlam, p13761_0]
                                      · have p13761_0 := h13761c.1
                                        have p13761_1 := h13761c.2.1
                                        have p13761_2 := h13761c.2.2.1
                                        have p13761_3 := h13761c.2.2.2
                                        linarith only [h13750, hlam, p13761_0]
                                      · have p13761_0 := h13761c.1
                                        have p13761_1 := h13761c.2.1
                                        have p13761_2 := h13761c.2.2.1
                                        have p13761_3 := h13761c.2.2.2
                                        linarith only [h1, hlam, p13761_0]
                                      · have p13761_0 := h13761c.1
                                        have p13761_1 := h13761c.2.1
                                        have p13761_2 := h13761c.2.2.1
                                        have p13761_3 := h13761c.2.2.2
                                        linarith only [h1, h13748, h13756, h2, hc12, hc34, hlam, hphi, ht23, p13761_1]
                                      · have p13761_0 := h13761c.1
                                        have p13761_1 := h13761c.2.1
                                        have p13761_2 := h13761c.2.2.1
                                        have p13761_3 := h13761c.2.2.2
                                        linarith only [hlam, p13761_0]
                                      · have p13761_0 := h13761c.1
                                        have p13761_1 := h13761c.2.1
                                        have p13761_2 := h13761c.2.2.1
                                        have p13761_3 := h13761c.2.2.2
                                        linarith only [h13752, hlam, p13761_1]
                                      · have p13761_0 := h13761c.1
                                        have p13761_1 := h13761c.2.1
                                        have p13761_2 := h13761c.2.2.1
                                        have p13761_3 := h13761c.2.2.2
                                        linarith only [h1, h13748, h13750, h13756, h2, hc12, hc34, hlam, hphi, ht23, p13761_1]
                                      · have p13761_0 := h13761c.1
                                        have p13761_1 := h13761c.2.1
                                        have p13761_2 := h13761c.2.2.1
                                        have p13761_3 := h13761c.2.2.2
                                        linarith only [h1, h13748, h13756, hc13, hc34, hlam, hphi, p13761_1]
                                      · have p13761_0 := h13761c.1
                                        have p13761_1 := h13761c.2.1
                                        have p13761_2 := h13761c.2.2.1
                                        have p13761_3 := h13761c.2.2.2
                                        rcases p13761_3 (m.d 0 1) (by simp) with h13778 | h13778
                                        · linarith only [h13778, h2, hlam]
                                        · linarith only [h0, h13778, hlam]
                                      · have p13761_0 := h13761c.1
                                        have p13761_1 := h13761c.2.1
                                        have p13761_2 := h13761c.2.2.1
                                        have p13761_3 := h13761c.2.2.2
                                        rcases p13761_3 (m.d 0 1) (by simp) with h13781 | h13781
                                        · linarith only [h13781, h2, hlam]
                                        · linarith only [h1, h13781, hlam]
                                      · have p13761_0 := h13761c.1
                                        have p13761_1 := h13761c.2.1
                                        have p13761_2 := h13761c.2.2.1
                                        have p13761_3 := h13761c.2.2.2
                                        linarith only [hlam, p13761_0]
                                      · have p13761_0 := h13761c.1
                                        have p13761_1 := h13761c.2.1
                                        have p13761_2 := h13761c.2.2.1
                                        have p13761_3 := h13761c.2.2.2
                                        rcases p13761_3 (m.d 0 1) (by simp) with h13785 | h13785
                                        · linarith only [h13785, h2, hlam]
                                        · linarith only [h13632, h13785, hlam]
                                      · have p13761_0 := h13761c.1
                                        have p13761_1 := h13761c.2.1
                                        have p13761_2 := h13761c.2.2.1
                                        have p13761_3 := h13761c.2.2.2
                                        linarith only [h13632, hlam, p13761_0]
                                      · have p13761_0 := h13761c.1
                                        have p13761_1 := h13761c.2.1
                                        have p13761_2 := h13761c.2.2.1
                                        have p13761_3 := h13761c.2.2.2
                                        linarith only [h13632, h13748, h13756, h2, hc12, hc34, hlam, hphi, ht23, p13761_1]
                                      · have p13761_0 := h13761c.1
                                        have p13761_1 := h13761c.2.1
                                        have p13761_2 := h13761c.2.2.1
                                        have p13761_3 := h13761c.2.2.2
                                        linarith only [h13754, hlam, p13761_0]
                                      · have p13761_0 := h13761c.1
                                        have p13761_1 := h13761c.2.1
                                        have p13761_2 := h13761c.2.2.1
                                        have p13761_3 := h13761c.2.2.2
                                        linarith only [h13755, hlam, p13761_0]
                                      · have p13761_0 := h13761c.1
                                        have p13761_1 := h13761c.2.1
                                        have p13761_2 := h13761c.2.2.1
                                        have p13761_3 := h13761c.2.2.2
                                        linarith only [hlam, p13761_0]
                                    · linarith only [h0, h13748, h13756, h13760, h2, hc12, hc45, hlam, hphi, ht23, ht34]
                                  · linarith only [h1, h13748, h13754, h13755, h13759, h2, hc15, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h1, h13754, h13758, h2, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · linarith only [h1, h13745, h13754, h13755, h2, hc05, hc35, hlam, hphi, ht0b, ht5b]
                          · linarith only [h1, h13744, h13752, h13754, h2, hc13, hc34, hlam, hphi]
                · linarith only [h1, h13744, h13745, h2, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h13799 | h13799
                · rcases m.htr 1 2 3 (by decide) (by decide) with h13800 | h13800
                  · linarith only [h0, h13633, h13800, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h13802 | h13802
                    · linarith only [h0, h13677, h13802, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h13804 | h13804
                      · linarith only [h0, h13679, h13804, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h13806 | h13806
                        · linarith only [h1, h13742, h13806, h2, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h13808 | h13808
                          · linarith only [h1, h13633, h13744, h13806, h13808, h2, hc02, hc34, hlam, hphi, ht23]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h13810 | h13810
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h13811 | h13811
                              · linarith only [h0, h13806, h13811, h2, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h13813 | h13813
                                · linarith only [h0, h13633, h13744, h13811, h13813, hc12, hc34, hlam, hphi, ht23]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h13815 | h13815
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h13816 | h13816
                                    · rcases h1bigk with h13817c | h13817c | h13817c | h13817c | h13817c | h13817c | h13817c | h13817c | h13817c | h13817c | h13817c | h13817c | h13817c | h13817c | h13817c | h13817c | h13817c | h13817c | h13817c | h13817c | h13817c | h13817c | h13817c | h13817c | h13817c
                                      · have p13817_0 := h13817c.1
                                        have p13817_1 := h13817c.2.1
                                        have p13817_2 := h13817c.2.2.1
                                        have p13817_3 := h13817c.2.2.2
                                        linarith only [hlam, p13817_0]
                                      · have p13817_0 := h13817c.1
                                        have p13817_1 := h13817c.2.1
                                        have p13817_2 := h13817c.2.2.1
                                        have p13817_3 := h13817c.2.2.2
                                        linarith only [h13802, h2, hc12, hc24, hlam, hphi, p13817_1]
                                      · have p13817_0 := h13817c.1
                                        have p13817_1 := h13817c.2.1
                                        have p13817_2 := h13817c.2.2.1
                                        have p13817_3 := h13817c.2.2.2
                                        linarith only [h13800, h13802, h2, hc12, hc24, hlam, hphi, p13817_1]
                                      · have p13817_0 := h13817c.1
                                        have p13817_1 := h13817c.2.1
                                        have p13817_2 := h13817c.2.2.1
                                        have p13817_3 := h13817c.2.2.2
                                        linarith only [h2, hlam, p13817_0]
                                      · have p13817_0 := h13817c.1
                                        have p13817_1 := h13817c.2.1
                                        have p13817_2 := h13817c.2.2.1
                                        have p13817_3 := h13817c.2.2.2
                                        linarith only [h13800, h13802, h13808, h2, hc12, hc24, hlam, hphi, p13817_1]
                                      · have p13817_0 := h13817c.1
                                        have p13817_1 := h13817c.2.1
                                        have p13817_2 := h13817c.2.2.1
                                        have p13817_3 := h13817c.2.2.2
                                        linarith only [h0, hlam, p13817_0]
                                      · have p13817_0 := h13817c.1
                                        have p13817_1 := h13817c.2.1
                                        have p13817_2 := h13817c.2.2.1
                                        have p13817_3 := h13817c.2.2.2
                                        linarith only [hlam, p13817_0]
                                      · have p13817_0 := h13817c.1
                                        have p13817_1 := h13817c.2.1
                                        have p13817_2 := h13817c.2.2.1
                                        have p13817_3 := h13817c.2.2.2
                                        linarith only [h13800, hlam, p13817_0]
                                      · have p13817_0 := h13817c.1
                                        have p13817_1 := h13817c.2.1
                                        have p13817_2 := h13817c.2.2.1
                                        have p13817_3 := h13817c.2.2.2
                                        linarith only [h13802, hlam, p13817_0]
                                      · have p13817_0 := h13817c.1
                                        have p13817_1 := h13817c.2.1
                                        have p13817_2 := h13817c.2.2.1
                                        have p13817_3 := h13817c.2.2.2
                                        linarith only [h13804, hlam, p13817_0]
                                      · have p13817_0 := h13817c.1
                                        have p13817_1 := h13817c.2.1
                                        have p13817_2 := h13817c.2.2.1
                                        have p13817_3 := h13817c.2.2.2
                                        linarith only [h1, hlam, p13817_0]
                                      · have p13817_0 := h13817c.1
                                        have p13817_1 := h13817c.2.1
                                        have p13817_2 := h13817c.2.2.1
                                        have p13817_3 := h13817c.2.2.2
                                        linarith only [h1, h13802, h2, hc12, hc24, hlam, hphi, p13817_1]
                                      · have p13817_0 := h13817c.1
                                        have p13817_1 := h13817c.2.1
                                        have p13817_2 := h13817c.2.2.1
                                        have p13817_3 := h13817c.2.2.2
                                        linarith only [hlam, p13817_0]
                                      · have p13817_0 := h13817c.1
                                        have p13817_1 := h13817c.2.1
                                        have p13817_2 := h13817c.2.2.1
                                        have p13817_3 := h13817c.2.2.2
                                        linarith only [h13806, hlam, p13817_1]
                                      · have p13817_0 := h13817c.1
                                        have p13817_1 := h13817c.2.1
                                        have p13817_2 := h13817c.2.2.1
                                        have p13817_3 := h13817c.2.2.2
                                        linarith only [h13808, hlam, p13817_1]
                                      · have p13817_0 := h13817c.1
                                        have p13817_1 := h13817c.2.1
                                        have p13817_2 := h13817c.2.2.1
                                        have p13817_3 := h13817c.2.2.2
                                        linarith only [h0, h13802, hc12, hc24, hlam, hphi, p13817_1]
                                      · have p13817_0 := h13817c.1
                                        have p13817_1 := h13817c.2.1
                                        have p13817_2 := h13817c.2.2.1
                                        have p13817_3 := h13817c.2.2.2
                                        rcases p13817_3 (m.d 0 1) (by simp) with h13834 | h13834
                                        · linarith only [h13834, h2, hlam]
                                        · linarith only [h0, h13834, hlam]
                                      · have p13817_0 := h13817c.1
                                        have p13817_1 := h13817c.2.1
                                        have p13817_2 := h13817c.2.2.1
                                        have p13817_3 := h13817c.2.2.2
                                        rcases p13817_3 (m.d 0 1) (by simp) with h13837 | h13837
                                        · linarith only [h13837, h2, hlam]
                                        · linarith only [h1, h13837, hlam]
                                      · have p13817_0 := h13817c.1
                                        have p13817_1 := h13817c.2.1
                                        have p13817_2 := h13817c.2.2.1
                                        have p13817_3 := h13817c.2.2.2
                                        linarith only [hlam, p13817_0]
                                      · have p13817_0 := h13817c.1
                                        have p13817_1 := h13817c.2.1
                                        have p13817_2 := h13817c.2.2.1
                                        have p13817_3 := h13817c.2.2.2
                                        rcases p13817_3 (m.d 0 1) (by simp) with h13841 | h13841
                                        · linarith only [h13841, h2, hlam]
                                        · linarith only [h13632, h13841, hlam]
                                      · have p13817_0 := h13817c.1
                                        have p13817_1 := h13817c.2.1
                                        have p13817_2 := h13817c.2.2.1
                                        have p13817_3 := h13817c.2.2.2
                                        linarith only [h13632, hlam, p13817_0]
                                      · have p13817_0 := h13817c.1
                                        have p13817_1 := h13817c.2.1
                                        have p13817_2 := h13817c.2.2.1
                                        have p13817_3 := h13817c.2.2.2
                                        linarith only [h13632, h13802, h13811, h2, hc12, hc34, hlam, hphi, ht23, p13817_1]
                                      · have p13817_0 := h13817c.1
                                        have p13817_1 := h13817c.2.1
                                        have p13817_2 := h13817c.2.2.1
                                        have p13817_3 := h13817c.2.2.2
                                        linarith only [h13632, h13802, h13811, h2, hc13, hc34, hlam, hphi, p13817_1]
                                      · have p13817_0 := h13817c.1
                                        have p13817_1 := h13817c.2.1
                                        have p13817_2 := h13817c.2.2.1
                                        have p13817_3 := h13817c.2.2.2
                                        linarith only [h13810, hlam, p13817_0]
                                      · have p13817_0 := h13817c.1
                                        have p13817_1 := h13817c.2.1
                                        have p13817_2 := h13817c.2.2.1
                                        have p13817_3 := h13817c.2.2.2
                                        linarith only [hlam, p13817_0]
                                    · linarith only [h13632, h13802, h13810, h13811, h13816, h2, hlam]
                                  · linarith only [h13632, h13802, h13810, h13815, h2, hlam]
                            · linarith only [h0, h13810, h2, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h13632, h13799, h2, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h13853 | h13853
      · rcases m.htr 0 2 4 (by decide) (by decide) with h13854 | h13854
        · linarith only [h0, h13854, h2, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h13856 | h13856
          · linarith only [h0, h13632, h13856, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h13858 | h13858
            · linarith only [h1, h13858, h2, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h13860 | h13860
              · linarith only [h0, h13632, h13853, h13860, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h13862 | h13862
                · rcases m.htr 1 2 3 (by decide) (by decide) with h13863 | h13863
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h13864 | h13864
                    · linarith only [h0, h13854, h13864, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h13866 | h13866
                      · linarith only [h0, h13632, h13856, h13866, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h13868 | h13868
                        · linarith only [h0, h13632, h13858, h13862, h13863, h13868, hlam]
                        · linarith only [h0, h13863, h13868, h2, hc23, hc34, hlam, hphi]
                  · linarith only [h13853, h13854, h13863, hc12, hc24, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h13872 | h13872
                  · linarith only [h0, h13862, h13872, h2, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h13853, h13862, h13872, h2, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h13875 | h13875
        · linarith only [h0, h13875, h2, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h13877 | h13877
          · linarith only [h1, h13632, h13853, h13877, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h13879 | h13879
            · linarith only [h1, h13879, h2, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h13881 | h13881
              · linarith only [h1, h13632, h13881, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h13883 | h13883
                · rcases m.htr 1 2 3 (by decide) (by decide) with h13884 | h13884
                  · linarith only [h0, h13853, h13884, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h13886 | h13886
                    · linarith only [h0, h13632, h13875, h13883, h13886, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h13888 | h13888
                      · linarith only [h1, h13877, h13884, h13888, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h13890 | h13890
                        · linarith only [h1, h13879, h13886, h13890, h2, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h13892 | h13892
                          · linarith only [h1, h13632, h13881, h13892, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h13894 | h13894
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h13895 | h13895
                              · linarith only [h0, h13632, h13890, h13894, h13895, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h13897 | h13897
                                · linarith only [h13632, h13892, h13895, h13897, hc01, hc34, hlam, hphi, ht12, ht23]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h13899 | h13899
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h13900 | h13900
                                    · rcases h1bigk with h13901c | h13901c | h13901c | h13901c | h13901c | h13901c | h13901c | h13901c | h13901c | h13901c | h13901c | h13901c | h13901c | h13901c | h13901c | h13901c | h13901c | h13901c | h13901c | h13901c | h13901c | h13901c | h13901c | h13901c | h13901c
                                      · have p13901_0 := h13901c.1
                                        have p13901_1 := h13901c.2.1
                                        have p13901_2 := h13901c.2.2.1
                                        have p13901_3 := h13901c.2.2.2
                                        linarith only [hlam, p13901_0]
                                      · have p13901_0 := h13901c.1
                                        have p13901_1 := h13901c.2.1
                                        have p13901_2 := h13901c.2.2.1
                                        have p13901_3 := h13901c.2.2.2
                                        linarith only [h13632, h13886, h13894, hc12, hc24, hlam, hphi, p13901_1]
                                      · have p13901_0 := h13901c.1
                                        have p13901_1 := h13901c.2.1
                                        have p13901_2 := h13901c.2.2.1
                                        have p13901_3 := h13901c.2.2.2
                                        linarith only [h13632, h13884, h13886, h13894, hc12, hc24, hlam, hphi, p13901_1]
                                      · have p13901_0 := h13901c.1
                                        have p13901_1 := h13901c.2.1
                                        have p13901_2 := h13901c.2.2.1
                                        have p13901_3 := h13901c.2.2.2
                                        linarith only [h2, hlam, p13901_0]
                                      · have p13901_0 := h13901c.1
                                        have p13901_1 := h13901c.2.1
                                        have p13901_2 := h13901c.2.2.1
                                        have p13901_3 := h13901c.2.2.2
                                        linarith only [h13632, hlam, p13901_0]
                                      · have p13901_0 := h13901c.1
                                        have p13901_1 := h13901c.2.1
                                        have p13901_2 := h13901c.2.2.1
                                        have p13901_3 := h13901c.2.2.2
                                        linarith only [h0, hlam, p13901_0]
                                      · have p13901_0 := h13901c.1
                                        have p13901_1 := h13901c.2.1
                                        have p13901_2 := h13901c.2.2.1
                                        have p13901_3 := h13901c.2.2.2
                                        linarith only [hlam, p13901_0]
                                      · have p13901_0 := h13901c.1
                                        have p13901_1 := h13901c.2.1
                                        have p13901_2 := h13901c.2.2.1
                                        have p13901_3 := h13901c.2.2.2
                                        linarith only [h13884, hlam, p13901_0]
                                      · have p13901_0 := h13901c.1
                                        have p13901_1 := h13901c.2.1
                                        have p13901_2 := h13901c.2.2.1
                                        have p13901_3 := h13901c.2.2.2
                                        linarith only [h13886, hlam, p13901_0]
                                      · have p13901_0 := h13901c.1
                                        have p13901_1 := h13901c.2.1
                                        have p13901_2 := h13901c.2.2.1
                                        have p13901_3 := h13901c.2.2.2
                                        linarith only [h13888, hlam, p13901_0]
                                      · have p13901_0 := h13901c.1
                                        have p13901_1 := h13901c.2.1
                                        have p13901_2 := h13901c.2.2.1
                                        have p13901_3 := h13901c.2.2.2
                                        linarith only [h1, hlam, p13901_0]
                                      · have p13901_0 := h13901c.1
                                        have p13901_1 := h13901c.2.1
                                        have p13901_2 := h13901c.2.2.1
                                        have p13901_3 := h13901c.2.2.2
                                        linarith only [h1, h13632, h13886, h13894, hc12, hc24, hlam, hphi, p13901_1]
                                      · have p13901_0 := h13901c.1
                                        have p13901_1 := h13901c.2.1
                                        have p13901_2 := h13901c.2.2.1
                                        have p13901_3 := h13901c.2.2.2
                                        linarith only [hlam, p13901_0]
                                      · have p13901_0 := h13901c.1
                                        have p13901_1 := h13901c.2.1
                                        have p13901_2 := h13901c.2.2.1
                                        have p13901_3 := h13901c.2.2.2
                                        linarith only [h13890, hlam, p13901_1]
                                      · have p13901_0 := h13901c.1
                                        have p13901_1 := h13901c.2.1
                                        have p13901_2 := h13901c.2.2.1
                                        have p13901_3 := h13901c.2.2.2
                                        linarith only [h13892, hlam, p13901_1]
                                      · have p13901_0 := h13901c.1
                                        have p13901_1 := h13901c.2.1
                                        have p13901_2 := h13901c.2.2.1
                                        have p13901_3 := h13901c.2.2.2
                                        linarith only [h0, h13886, hc12, hc24, hlam, hphi, p13901_1]
                                      · have p13901_0 := h13901c.1
                                        have p13901_1 := h13901c.2.1
                                        have p13901_2 := h13901c.2.2.1
                                        have p13901_3 := h13901c.2.2.2
                                        rcases p13901_3 (m.d 0 1) (by simp) with h13918 | h13918
                                        · linarith only [h13918, h2, hlam]
                                        · linarith only [h0, h13918, hlam]
                                      · have p13901_0 := h13901c.1
                                        have p13901_1 := h13901c.2.1
                                        have p13901_2 := h13901c.2.2.1
                                        have p13901_3 := h13901c.2.2.2
                                        rcases p13901_3 (m.d 0 1) (by simp) with h13921 | h13921
                                        · linarith only [h13921, h2, hlam]
                                        · linarith only [h1, h13921, hlam]
                                      · have p13901_0 := h13901c.1
                                        have p13901_1 := h13901c.2.1
                                        have p13901_2 := h13901c.2.2.1
                                        have p13901_3 := h13901c.2.2.2
                                        linarith only [hlam, p13901_0]
                                      · have p13901_0 := h13901c.1
                                        have p13901_1 := h13901c.2.1
                                        have p13901_2 := h13901c.2.2.1
                                        have p13901_3 := h13901c.2.2.2
                                        linarith only [h1, h13632, h13884, h13886, h13895, hc12, hc34, hlam, hphi, ht23, p13901_1]
                                      · have p13901_0 := h13901c.1
                                        have p13901_1 := h13901c.2.1
                                        have p13901_2 := h13901c.2.2.1
                                        have p13901_3 := h13901c.2.2.2
                                        linarith only [h1, h13884, h13888, hc12, hc25, hlam, hphi, p13901_1]
                                      · have p13901_0 := h13901c.1
                                        have p13901_1 := h13901c.2.1
                                        have p13901_2 := h13901c.2.2.1
                                        have p13901_3 := h13901c.2.2.2
                                        rcases p13901_3 (m.d 0 1) (by simp) with h13927 | h13927
                                        · linarith only [h13632, h13927, hlam]
                                        · linarith only [h0, h13927, hlam]
                                      · have p13901_0 := h13901c.1
                                        have p13901_1 := h13901c.2.1
                                        have p13901_2 := h13901c.2.2.1
                                        have p13901_3 := h13901c.2.2.2
                                        rcases p13901_3 (m.d 0 1) (by simp) with h13930 | h13930
                                        · linarith only [h13632, h13930, hlam]
                                        · linarith only [h1, h13930, hlam]
                                      · have p13901_0 := h13901c.1
                                        have p13901_1 := h13901c.2.1
                                        have p13901_2 := h13901c.2.2.1
                                        have p13901_3 := h13901c.2.2.2
                                        linarith only [h13894, hlam, p13901_0]
                                      · have p13901_0 := h13901c.1
                                        have p13901_1 := h13901c.2.1
                                        have p13901_2 := h13901c.2.2.1
                                        have p13901_3 := h13901c.2.2.2
                                        linarith only [hlam, p13901_0]
                                    · linarith only [h1, h13883, h13884, h13886, h13895, h13900, h2, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                  · linarith only [h13883, h13886, h13899, h2, hlam]
                            · linarith only [h13883, h13894, h2, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h13938 | h13938
                  · linarith only [h0, h13883, h13938, h2, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h13940 | h13940
                    · linarith only [h0, h13883, h13940, h2, hc24, hc45, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h13942 | h13942
                      · linarith only [h0, h13877, h13942, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h13944 | h13944
                        · linarith only [h1, h13883, h13944, h2, hc34, hc45, hlam, hphi]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h13946 | h13946
                          · linarith only [h1, h13853, h13881, h13883, h13946, h2, hc02, hc45, hlam, hphi, ht23, ht34]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h13948 | h13948
                            · linarith only [h0, h13883, h13944, h13948, h2, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h1, h13938, h13948, h2, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
