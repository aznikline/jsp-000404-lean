import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_4S13

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5858000 in
set_option maxHeartbeats 5858000 in
theorem r1l7_11_23_L_I_H_I_s10_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg6364 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h7232 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h9180 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h6364 := hg6364
  rcases m.htr 0 4 5 (by decide) (by decide) with h9578 | h9578
  · rcases m.htr 1 2 3 (by decide) (by decide) with h9579 | h9579
    · linarith only [h0, h4, h9579, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h9581 | h9581
      · linarith only [h0, h6364, h9581, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h9583 | h9583
        · rcases m.htr 1 3 4 (by decide) (by decide) with h9584 | h9584
          · linarith only [h1, h7232, h9584, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h9586 | h9586
            · linarith only [h0, h1, h4, h9180, h9583, h9586, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · linarith only [h9579, h9583, h9586, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h9589 | h9589
          · linarith only [h1, h7232, h9589, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h9591 | h9591
            · linarith only [h1, h9180, h9591, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h9593 | h9593
              · rcases m.htr 2 3 4 (by decide) (by decide) with h9594 | h9594
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9595 | h9595
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9596 | h9596
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9597 | h9597
                      · rcases h1bigk with h9598c | h9598c | h9598c | h9598c | h9598c | h9598c | h9598c | h9598c | h9598c | h9598c | h9598c | h9598c | h9598c | h9598c | h9598c | h9598c | h9598c | h9598c | h9598c | h9598c | h9598c | h9598c | h9598c | h9598c | h9598c
                        · have p9598_0 := h9598c.1
                          have p9598_1 := h9598c.2.1
                          have p9598_2 := h9598c.2.2.1
                          have p9598_3 := h9598c.2.2.2
                          linarith only [hlam, p9598_0]
                        · have p9598_0 := h9598c.1
                          have p9598_1 := h9598c.2.1
                          have p9598_2 := h9598c.2.2.1
                          have p9598_3 := h9598c.2.2.2
                          rcases p9598_3 (m.d 0 1) (by simp) with h9600 | h9600
                          · rcases p9598_3 (m.d 1 2) (by simp) with h9601 | h9601
                            · linarith only [h9601, hlam, p9598_0]
                            · rcases p9598_3 (m.d 1 3) (by simp) with h9603 | h9603
                              · linarith only [h1, h9603, hlam]
                              · linarith only [h9579, h9603, hlam]
                          · linarith only [h9600, hlam, p9598_0]
                        · have p9598_0 := h9598c.1
                          have p9598_1 := h9598c.2.1
                          have p9598_2 := h9598c.2.2.1
                          have p9598_3 := h9598c.2.2.2
                          rcases p9598_3 (m.d 0 1) (by simp) with h9607 | h9607
                          · rcases p9598_3 (m.d 1 2) (by simp) with h9608 | h9608
                            · linarith only [h0, h9608, hlam]
                            · rcases p9598_3 (m.d 1 3) (by simp) with h9610 | h9610
                              · linarith only [h9610, hlam, p9598_0]
                              · rcases p9598_3 (m.d 1 4) (by simp) with h9612 | h9612
                                · linarith only [h2, h9612, hlam]
                                · linarith only [h9589, h9612, hlam]
                          · linarith only [h9607, hlam, p9598_0]
                        · have p9598_0 := h9598c.1
                          have p9598_1 := h9598c.2.1
                          have p9598_2 := h9598c.2.2.1
                          have p9598_3 := h9598c.2.2.2
                          rcases p9598_3 (m.d 0 1) (by simp) with h9616 | h9616
                          · rcases p9598_3 (m.d 1 2) (by simp) with h9617 | h9617
                            · linarith only [h0, h9617, hlam]
                            · rcases p9598_3 (m.d 1 3) (by simp) with h9619 | h9619
                              · linarith only [h1, h9619, hlam]
                              · rcases p9598_3 (m.d 1 4) (by simp) with h9621 | h9621
                                · linarith only [h9621, hlam, p9598_0]
                                · rcases p9598_3 (m.d 1 5) (by simp) with h9623 | h9623
                                  · linarith only [h3, h9623, hlam]
                                  · rcases h3bigk with h9625c | h9625c | h9625c | h9625c | h9625c | h9625c | h9625c | h9625c | h9625c | h9625c | h9625c | h9625c | h9625c | h9625c | h9625c | h9625c | h9625c | h9625c | h9625c | h9625c | h9625c | h9625c | h9625c | h9625c | h9625c
                                    · have p9625_0 := h9625c.1
                                      have p9625_1 := h9625c.2.1
                                      have p9625_2 := h9625c.2.2.1
                                      have p9625_3 := h9625c.2.2.2
                                      linarith only [hlam, p9625_0]
                                    · have p9625_0 := h9625c.1
                                      have p9625_1 := h9625c.2.1
                                      have p9625_2 := h9625c.2.2.1
                                      have p9625_3 := h9625c.2.2.2
                                      linarith only [h9180, h9594, h9597, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p9625_1]
                                    · have p9625_0 := h9625c.1
                                      have p9625_1 := h9625c.2.1
                                      have p9625_2 := h9625c.2.2.1
                                      have p9625_3 := h9625c.2.2.2
                                      linarith only [h4, hlam, p9625_1]
                                    · have p9625_0 := h9625c.1
                                      have p9625_1 := h9625c.2.1
                                      have p9625_2 := h9625c.2.2.1
                                      have p9625_3 := h9625c.2.2.2
                                      linarith only [h7232, hlam, p9625_0]
                                    · have p9625_0 := h9625c.1
                                      have p9625_1 := h9625c.2.1
                                      have p9625_2 := h9625c.2.2.1
                                      have p9625_3 := h9625c.2.2.2
                                      linarith only [h9180, hlam, p9625_0]
                                    · have p9625_0 := h9625c.1
                                      have p9625_1 := h9625c.2.1
                                      have p9625_2 := h9625c.2.2.1
                                      have p9625_3 := h9625c.2.2.2
                                      linarith only [h1, hlam, p9625_0]
                                    · have p9625_0 := h9625c.1
                                      have p9625_1 := h9625c.2.1
                                      have p9625_2 := h9625c.2.2.1
                                      have p9625_3 := h9625c.2.2.2
                                      linarith only [hlam, p9625_0]
                                    · have p9625_0 := h9625c.1
                                      have p9625_1 := h9625c.2.1
                                      have p9625_2 := h9625c.2.2.1
                                      have p9625_3 := h9625c.2.2.2
                                      linarith only [h9579, hlam, p9625_1]
                                    · have p9625_0 := h9625c.1
                                      have p9625_1 := h9625c.2.1
                                      have p9625_2 := h9625c.2.2.1
                                      have p9625_3 := h9625c.2.2.2
                                      linarith only [h9589, hlam, p9625_0]
                                    · have p9625_0 := h9625c.1
                                      have p9625_1 := h9625c.2.1
                                      have p9625_2 := h9625c.2.2.1
                                      have p9625_3 := h9625c.2.2.2
                                      linarith only [h9591, hlam, p9625_0]
                                    · have p9625_0 := h9625c.1
                                      have p9625_1 := h9625c.2.1
                                      have p9625_2 := h9625c.2.2.1
                                      have p9625_3 := h9625c.2.2.2
                                      linarith only [h0, h4, hc12, hc23, hlam, hphi, p9625_1]
                                    · have p9625_0 := h9625c.1
                                      have p9625_1 := h9625c.2.1
                                      have p9625_2 := h9625c.2.2.1
                                      have p9625_3 := h9625c.2.2.2
                                      linarith only [h9579, hc12, hc23, hlam, hphi, p9625_1]
                                    · have p9625_0 := h9625c.1
                                      have p9625_1 := h9625c.2.1
                                      have p9625_2 := h9625c.2.2.1
                                      have p9625_3 := h9625c.2.2.2
                                      linarith only [hlam, p9625_0]
                                    · have p9625_0 := h9625c.1
                                      have p9625_1 := h9625c.2.1
                                      have p9625_2 := h9625c.2.2.1
                                      have p9625_3 := h9625c.2.2.2
                                      linarith only [h0, h4, h7232, hc12, hc23, hlam, hphi, p9625_1]
                                    · have p9625_0 := h9625c.1
                                      have p9625_1 := h9625c.2.1
                                      have p9625_2 := h9625c.2.2.1
                                      have p9625_3 := h9625c.2.2.2
                                      linarith only [h0, h4, h9180, hc12, hc23, hlam, hphi, p9625_1]
                                    · have p9625_0 := h9625c.1
                                      have p9625_1 := h9625c.2.1
                                      have p9625_2 := h9625c.2.2.1
                                      have p9625_3 := h9625c.2.2.2
                                      linarith only [h0, h4, h9594, hc12, hc24, hlam, hphi, p9625_1]
                                    · have p9625_0 := h9625c.1
                                      have p9625_1 := h9625c.2.1
                                      have p9625_2 := h9625c.2.2.1
                                      have p9625_3 := h9625c.2.2.2
                                      linarith only [h9579, h9594, hc12, hc24, hlam, hphi, p9625_1]
                                    · have p9625_0 := h9625c.1
                                      have p9625_1 := h9625c.2.1
                                      have p9625_2 := h9625c.2.2.1
                                      have p9625_3 := h9625c.2.2.2
                                      linarith only [h9594, hlam, p9625_0]
                                    · have p9625_0 := h9625c.1
                                      have p9625_1 := h9625c.2.1
                                      have p9625_2 := h9625c.2.2.1
                                      have p9625_3 := h9625c.2.2.2
                                      linarith only [hlam, p9625_0]
                                    · have p9625_0 := h9625c.1
                                      have p9625_1 := h9625c.2.1
                                      have p9625_2 := h9625c.2.2.1
                                      have p9625_3 := h9625c.2.2.2
                                      linarith only [h0, h4, h9180, h9594, hc12, hc23, hlam, hphi, p9625_1]
                                    · have p9625_0 := h9625c.1
                                      have p9625_1 := h9625c.2.1
                                      have p9625_2 := h9625c.2.2.1
                                      have p9625_3 := h9625c.2.2.2
                                      linarith only [h0, h4, h9595, hc12, hc25, hlam, hphi, p9625_1]
                                    · have p9625_0 := h9625c.1
                                      have p9625_1 := h9625c.2.1
                                      have p9625_2 := h9625c.2.2.1
                                      have p9625_3 := h9625c.2.2.2
                                      linarith only [h9579, h9595, hc12, hc25, hlam, hphi, p9625_1]
                                    · have p9625_0 := h9625c.1
                                      have p9625_1 := h9625c.2.1
                                      have p9625_2 := h9625c.2.2.1
                                      have p9625_3 := h9625c.2.2.2
                                      linarith only [h9595, hlam, p9625_0]
                                    · have p9625_0 := h9625c.1
                                      have p9625_1 := h9625c.2.1
                                      have p9625_2 := h9625c.2.2.1
                                      have p9625_3 := h9625c.2.2.2
                                      linarith only [h9597, hlam, p9625_0]
                                    · have p9625_0 := h9625c.1
                                      have p9625_1 := h9625c.2.1
                                      have p9625_2 := h9625c.2.2.1
                                      have p9625_3 := h9625c.2.2.2
                                      linarith only [hlam, p9625_0]
                          · linarith only [h9616, hlam, p9598_0]
                        · have p9598_0 := h9598c.1
                          have p9598_1 := h9598c.2.1
                          have p9598_2 := h9598c.2.2.1
                          have p9598_3 := h9598c.2.2.2
                          rcases p9598_3 (m.d 0 1) (by simp) with h9652 | h9652
                          · rcases p9598_3 (m.d 1 2) (by simp) with h9653 | h9653
                            · linarith only [h0, h9653, hlam]
                            · rcases p9598_3 (m.d 1 3) (by simp) with h9655 | h9655
                              · linarith only [h1, h9655, hlam]
                              · rcases p9598_3 (m.d 1 4) (by simp) with h9657 | h9657
                                · linarith only [h2, h9657, hlam]
                                · linarith only [h9593, h9657, hlam]
                          · linarith only [h9652, hlam, p9598_0]
                        · have p9598_0 := h9598c.1
                          have p9598_1 := h9598c.2.1
                          have p9598_2 := h9598c.2.2.1
                          have p9598_3 := h9598c.2.2.2
                          linarith only [h0, hlam, p9598_0]
                        · have p9598_0 := h9598c.1
                          have p9598_1 := h9598c.2.1
                          have p9598_2 := h9598c.2.2.1
                          have p9598_3 := h9598c.2.2.2
                          linarith only [hlam, p9598_0]
                        · have p9598_0 := h9598c.1
                          have p9598_1 := h9598c.2.1
                          have p9598_2 := h9598c.2.2.1
                          have p9598_3 := h9598c.2.2.2
                          linarith only [h9579, hlam, p9598_0]
                        · have p9598_0 := h9598c.1
                          have p9598_1 := h9598c.2.1
                          have p9598_2 := h9598c.2.2.1
                          have p9598_3 := h9598c.2.2.2
                          linarith only [h9581, hlam, p9598_0]
                        · have p9598_0 := h9598c.1
                          have p9598_1 := h9598c.2.1
                          have p9598_2 := h9598c.2.2.1
                          have p9598_3 := h9598c.2.2.2
                          linarith only [h9583, hlam, p9598_0]
                        · have p9598_0 := h9598c.1
                          have p9598_1 := h9598c.2.1
                          have p9598_2 := h9598c.2.2.1
                          have p9598_3 := h9598c.2.2.2
                          linarith only [h1, hlam, p9598_0]
                        · have p9598_0 := h9598c.1
                          have p9598_1 := h9598c.2.1
                          have p9598_2 := h9598c.2.2.1
                          have p9598_3 := h9598c.2.2.2
                          linarith only [h1, h7232, h9594, hc12, hc23, hlam, hphi, p9598_1]
                        · have p9598_0 := h9598c.1
                          have p9598_1 := h9598c.2.1
                          have p9598_2 := h9598c.2.2.1
                          have p9598_3 := h9598c.2.2.2
                          linarith only [hlam, p9598_0]
                        · have p9598_0 := h9598c.1
                          have p9598_1 := h9598c.2.1
                          have p9598_2 := h9598c.2.2.1
                          have p9598_3 := h9598c.2.2.2
                          linarith only [h9589, hlam, p9598_1]
                        · have p9598_0 := h9598c.1
                          have p9598_1 := h9598c.2.1
                          have p9598_2 := h9598c.2.2.1
                          have p9598_3 := h9598c.2.2.2
                          linarith only [h9591, hlam, p9598_1]
                        · have p9598_0 := h9598c.1
                          have p9598_1 := h9598c.2.1
                          have p9598_2 := h9598c.2.2.1
                          have p9598_3 := h9598c.2.2.2
                          linarith only [h2, hlam, p9598_0]
                        · have p9598_0 := h9598c.1
                          have p9598_1 := h9598c.2.1
                          have p9598_2 := h9598c.2.2.1
                          have p9598_3 := h9598c.2.2.2
                          linarith only [h2, h7232, h9594, hc12, hc23, hlam, hphi, p9598_1]
                        · have p9598_0 := h9598c.1
                          have p9598_1 := h9598c.2.1
                          have p9598_2 := h9598c.2.2.1
                          have p9598_3 := h9598c.2.2.2
                          linarith only [h2, h7232, h9579, h9594, hc12, hc23, hlam, hphi, p9598_1]
                        · have p9598_0 := h9598c.1
                          have p9598_1 := h9598c.2.1
                          have p9598_2 := h9598c.2.2.1
                          have p9598_3 := h9598c.2.2.2
                          linarith only [hlam, p9598_0]
                        · have p9598_0 := h9598c.1
                          have p9598_1 := h9598c.2.1
                          have p9598_2 := h9598c.2.2.1
                          have p9598_3 := h9598c.2.2.2
                          linarith only [h2, h7232, h9579, h9591, h9594, hc12, hc23, hlam, hphi, p9598_1]
                        · have p9598_0 := h9598c.1
                          have p9598_1 := h9598c.2.1
                          have p9598_2 := h9598c.2.2.1
                          have p9598_3 := h9598c.2.2.2
                          linarith only [h3, hlam, p9598_0]
                        · have p9598_0 := h9598c.1
                          have p9598_1 := h9598c.2.1
                          have p9598_2 := h9598c.2.2.1
                          have p9598_3 := h9598c.2.2.2
                          linarith only [h3, h9180, h9594, h9597, hc12, hc23, hlam, hphi, p9598_1]
                        · have p9598_0 := h9598c.1
                          have p9598_1 := h9598c.2.1
                          have p9598_2 := h9598c.2.2.1
                          have p9598_3 := h9598c.2.2.2
                          linarith only [h3, h9180, h9579, h9594, h9597, hc12, hc23, hlam, hphi, p9598_1]
                        · have p9598_0 := h9598c.1
                          have p9598_1 := h9598c.2.1
                          have p9598_2 := h9598c.2.2.1
                          have p9598_3 := h9598c.2.2.2
                          linarith only [h9593, hlam, p9598_0]
                        · have p9598_0 := h9598c.1
                          have p9598_1 := h9598c.2.1
                          have p9598_2 := h9598c.2.2.1
                          have p9598_3 := h9598c.2.2.2
                          linarith only [hlam, p9598_0]
                      · linarith only [h7232, h9578, h9597, hlam]
                    · linarith only [h0, h2, h6364, h9593, h9596, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h1, h7232, h9579, h9594, h9595, hc12, hc35, hlam, hphi, ht23]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9684 | h9684
                  · linarith only [h1, h9180, h9579, h9594, h9684, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9686 | h9686
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9687 | h9687
                      · rcases h1bigk with h9688c | h9688c | h9688c | h9688c | h9688c | h9688c | h9688c | h9688c | h9688c | h9688c | h9688c | h9688c | h9688c | h9688c | h9688c | h9688c | h9688c | h9688c | h9688c | h9688c | h9688c | h9688c | h9688c | h9688c | h9688c
                        · have p9688_0 := h9688c.1
                          have p9688_1 := h9688c.2.1
                          have p9688_2 := h9688c.2.2.1
                          have p9688_3 := h9688c.2.2.2
                          linarith only [hlam, p9688_0]
                        · have p9688_0 := h9688c.1
                          have p9688_1 := h9688c.2.1
                          have p9688_2 := h9688c.2.2.1
                          have p9688_3 := h9688c.2.2.2
                          rcases p9688_3 (m.d 0 1) (by simp) with h9690 | h9690
                          · rcases p9688_3 (m.d 1 2) (by simp) with h9691 | h9691
                            · linarith only [h9691, hlam, p9688_0]
                            · rcases p9688_3 (m.d 1 3) (by simp) with h9693 | h9693
                              · linarith only [h1, h9693, hlam]
                              · linarith only [h9579, h9693, hlam]
                          · linarith only [h9690, hlam, p9688_0]
                        · have p9688_0 := h9688c.1
                          have p9688_1 := h9688c.2.1
                          have p9688_2 := h9688c.2.2.1
                          have p9688_3 := h9688c.2.2.2
                          rcases p9688_3 (m.d 0 1) (by simp) with h9697 | h9697
                          · rcases p9688_3 (m.d 1 2) (by simp) with h9698 | h9698
                            · linarith only [h0, h9698, hlam]
                            · rcases p9688_3 (m.d 1 3) (by simp) with h9700 | h9700
                              · linarith only [h9700, hlam, p9688_0]
                              · rcases p9688_3 (m.d 1 4) (by simp) with h9702 | h9702
                                · linarith only [h2, h9702, hlam]
                                · linarith only [h9589, h9702, hlam]
                          · linarith only [h9697, hlam, p9688_0]
                        · have p9688_0 := h9688c.1
                          have p9688_1 := h9688c.2.1
                          have p9688_2 := h9688c.2.2.1
                          have p9688_3 := h9688c.2.2.2
                          rcases p9688_3 (m.d 0 1) (by simp) with h9706 | h9706
                          · rcases p9688_3 (m.d 1 2) (by simp) with h9707 | h9707
                            · linarith only [h0, h9707, hlam]
                            · rcases p9688_3 (m.d 1 3) (by simp) with h9709 | h9709
                              · linarith only [h1, h9709, hlam]
                              · rcases p9688_3 (m.d 1 4) (by simp) with h9711 | h9711
                                · linarith only [h9711, hlam, p9688_0]
                                · rcases p9688_3 (m.d 1 5) (by simp) with h9713 | h9713
                                  · linarith only [h3, h9713, hlam]
                                  · rcases h3bigk with h9715c | h9715c | h9715c | h9715c | h9715c | h9715c | h9715c | h9715c | h9715c | h9715c | h9715c | h9715c | h9715c | h9715c | h9715c | h9715c | h9715c | h9715c | h9715c | h9715c | h9715c | h9715c | h9715c | h9715c | h9715c
                                    · have p9715_0 := h9715c.1
                                      have p9715_1 := h9715c.2.1
                                      have p9715_2 := h9715c.2.2.1
                                      have p9715_3 := h9715c.2.2.2
                                      linarith only [hlam, p9715_0]
                                    · have p9715_0 := h9715c.1
                                      have p9715_1 := h9715c.2.1
                                      have p9715_2 := h9715c.2.2.1
                                      have p9715_3 := h9715c.2.2.2
                                      linarith only [h4, h9579, h9684, h9687, hc12, hc34, hlam, hphi, ht23, p9715_1]
                                    · have p9715_0 := h9715c.1
                                      have p9715_1 := h9715c.2.1
                                      have p9715_2 := h9715c.2.2.1
                                      have p9715_3 := h9715c.2.2.2
                                      linarith only [h4, hlam, p9715_1]
                                    · have p9715_0 := h9715c.1
                                      have p9715_1 := h9715c.2.1
                                      have p9715_2 := h9715c.2.2.1
                                      have p9715_3 := h9715c.2.2.2
                                      linarith only [h7232, hlam, p9715_0]
                                    · have p9715_0 := h9715c.1
                                      have p9715_1 := h9715c.2.1
                                      have p9715_2 := h9715c.2.2.1
                                      have p9715_3 := h9715c.2.2.2
                                      linarith only [h9180, hlam, p9715_0]
                                    · have p9715_0 := h9715c.1
                                      have p9715_1 := h9715c.2.1
                                      have p9715_2 := h9715c.2.2.1
                                      have p9715_3 := h9715c.2.2.2
                                      linarith only [h1, hlam, p9715_0]
                                    · have p9715_0 := h9715c.1
                                      have p9715_1 := h9715c.2.1
                                      have p9715_2 := h9715c.2.2.1
                                      have p9715_3 := h9715c.2.2.2
                                      linarith only [hlam, p9715_0]
                                    · have p9715_0 := h9715c.1
                                      have p9715_1 := h9715c.2.1
                                      have p9715_2 := h9715c.2.2.1
                                      have p9715_3 := h9715c.2.2.2
                                      linarith only [h9579, hlam, p9715_1]
                                    · have p9715_0 := h9715c.1
                                      have p9715_1 := h9715c.2.1
                                      have p9715_2 := h9715c.2.2.1
                                      have p9715_3 := h9715c.2.2.2
                                      linarith only [h9589, hlam, p9715_0]
                                    · have p9715_0 := h9715c.1
                                      have p9715_1 := h9715c.2.1
                                      have p9715_2 := h9715c.2.2.1
                                      have p9715_3 := h9715c.2.2.2
                                      linarith only [h9591, hlam, p9715_0]
                                    · have p9715_0 := h9715c.1
                                      have p9715_1 := h9715c.2.1
                                      have p9715_2 := h9715c.2.2.1
                                      have p9715_3 := h9715c.2.2.2
                                      linarith only [h9684, h9687, hc03, hc34, hlam, hphi, p9715_1]
                                    · have p9715_0 := h9715c.1
                                      have p9715_1 := h9715c.2.1
                                      have p9715_2 := h9715c.2.2.1
                                      have p9715_3 := h9715c.2.2.2
                                      linarith only [h9579, h9684, h9687, hc12, hc34, hlam, hphi, ht23, p9715_1]
                                    · have p9715_0 := h9715c.1
                                      have p9715_1 := h9715c.2.1
                                      have p9715_2 := h9715c.2.2.1
                                      have p9715_3 := h9715c.2.2.2
                                      linarith only [hlam, p9715_0]
                                    · have p9715_0 := h9715c.1
                                      have p9715_1 := h9715c.2.1
                                      have p9715_2 := h9715c.2.2.1
                                      have p9715_3 := h9715c.2.2.2
                                      linarith only [h9594, hlam, p9715_0]
                                    · have p9715_0 := h9715c.1
                                      have p9715_1 := h9715c.2.1
                                      have p9715_2 := h9715c.2.2.1
                                      have p9715_3 := h9715c.2.2.2
                                      linarith only [h9684, hlam, p9715_0]
                                    · have p9715_0 := h9715c.1
                                      have p9715_1 := h9715c.2.1
                                      have p9715_2 := h9715c.2.2.1
                                      have p9715_3 := h9715c.2.2.2
                                      linarith only [h1, h9579, hc12, hc34, hlam, hphi, ht23, p9715_1]
                                    · have p9715_0 := h9715c.1
                                      have p9715_1 := h9715c.2.1
                                      have p9715_2 := h9715c.2.2.1
                                      have p9715_3 := h9715c.2.2.2
                                      linarith only [h9579, hc12, hc34, hlam, hphi, ht23, p9715_1]
                                    · have p9715_0 := h9715c.1
                                      have p9715_1 := h9715c.2.1
                                      have p9715_2 := h9715c.2.2.1
                                      have p9715_3 := h9715c.2.2.2
                                      linarith only [hc23, hc34, hlam, hphi, p9715_1]
                                    · have p9715_0 := h9715c.1
                                      have p9715_1 := h9715c.2.1
                                      have p9715_2 := h9715c.2.2.1
                                      have p9715_3 := h9715c.2.2.2
                                      linarith only [hlam, p9715_0]
                                    · have p9715_0 := h9715c.1
                                      have p9715_1 := h9715c.2.1
                                      have p9715_2 := h9715c.2.2.1
                                      have p9715_3 := h9715c.2.2.2
                                      linarith only [h1, h9180, h9579, hc12, hc34, hlam, hphi, ht23, p9715_1]
                                    · have p9715_0 := h9715c.1
                                      have p9715_1 := h9715c.2.1
                                      have p9715_2 := h9715c.2.2.1
                                      have p9715_3 := h9715c.2.2.2
                                      linarith only [h1, h9579, hc12, hc35, hlam, hphi, ht23, p9715_1]
                                    · have p9715_0 := h9715c.1
                                      have p9715_1 := h9715c.2.1
                                      have p9715_2 := h9715c.2.2.1
                                      have p9715_3 := h9715c.2.2.2
                                      linarith only [h9579, hc12, hc35, hlam, hphi, ht23, p9715_1]
                                    · have p9715_0 := h9715c.1
                                      have p9715_1 := h9715c.2.1
                                      have p9715_2 := h9715c.2.2.1
                                      have p9715_3 := h9715c.2.2.2
                                      linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p9715_1]
                                    · have p9715_0 := h9715c.1
                                      have p9715_1 := h9715c.2.1
                                      have p9715_2 := h9715c.2.2.1
                                      have p9715_3 := h9715c.2.2.2
                                      linarith only [h9687, hlam, p9715_0]
                                    · have p9715_0 := h9715c.1
                                      have p9715_1 := h9715c.2.1
                                      have p9715_2 := h9715c.2.2.1
                                      have p9715_3 := h9715c.2.2.2
                                      linarith only [hlam, p9715_0]
                          · linarith only [h9706, hlam, p9688_0]
                        · have p9688_0 := h9688c.1
                          have p9688_1 := h9688c.2.1
                          have p9688_2 := h9688c.2.2.1
                          have p9688_3 := h9688c.2.2.2
                          rcases p9688_3 (m.d 0 1) (by simp) with h9742 | h9742
                          · rcases p9688_3 (m.d 1 2) (by simp) with h9743 | h9743
                            · linarith only [h0, h9743, hlam]
                            · rcases p9688_3 (m.d 1 3) (by simp) with h9745 | h9745
                              · linarith only [h1, h9745, hlam]
                              · rcases p9688_3 (m.d 1 4) (by simp) with h9747 | h9747
                                · linarith only [h2, h9747, hlam]
                                · linarith only [h9593, h9747, hlam]
                          · linarith only [h9742, hlam, p9688_0]
                        · have p9688_0 := h9688c.1
                          have p9688_1 := h9688c.2.1
                          have p9688_2 := h9688c.2.2.1
                          have p9688_3 := h9688c.2.2.2
                          linarith only [h0, hlam, p9688_0]
                        · have p9688_0 := h9688c.1
                          have p9688_1 := h9688c.2.1
                          have p9688_2 := h9688c.2.2.1
                          have p9688_3 := h9688c.2.2.2
                          linarith only [hlam, p9688_0]
                        · have p9688_0 := h9688c.1
                          have p9688_1 := h9688c.2.1
                          have p9688_2 := h9688c.2.2.1
                          have p9688_3 := h9688c.2.2.2
                          linarith only [h9579, hlam, p9688_0]
                        · have p9688_0 := h9688c.1
                          have p9688_1 := h9688c.2.1
                          have p9688_2 := h9688c.2.2.1
                          have p9688_3 := h9688c.2.2.2
                          linarith only [h9581, hlam, p9688_0]
                        · have p9688_0 := h9688c.1
                          have p9688_1 := h9688c.2.1
                          have p9688_2 := h9688c.2.2.1
                          have p9688_3 := h9688c.2.2.2
                          linarith only [h9583, hlam, p9688_0]
                        · have p9688_0 := h9688c.1
                          have p9688_1 := h9688c.2.1
                          have p9688_2 := h9688c.2.2.1
                          have p9688_3 := h9688c.2.2.2
                          linarith only [h1, hlam, p9688_0]
                        · have p9688_0 := h9688c.1
                          have p9688_1 := h9688c.2.1
                          have p9688_2 := h9688c.2.2.1
                          have p9688_3 := h9688c.2.2.2
                          linarith only [h1, h7232, hc12, hc34, hlam, hphi, ht23, p9688_1]
                        · have p9688_0 := h9688c.1
                          have p9688_1 := h9688c.2.1
                          have p9688_2 := h9688c.2.2.1
                          have p9688_3 := h9688c.2.2.2
                          linarith only [hlam, p9688_0]
                        · have p9688_0 := h9688c.1
                          have p9688_1 := h9688c.2.1
                          have p9688_2 := h9688c.2.2.1
                          have p9688_3 := h9688c.2.2.2
                          linarith only [h9589, hlam, p9688_1]
                        · have p9688_0 := h9688c.1
                          have p9688_1 := h9688c.2.1
                          have p9688_2 := h9688c.2.2.1
                          have p9688_3 := h9688c.2.2.2
                          linarith only [h9591, hlam, p9688_1]
                        · have p9688_0 := h9688c.1
                          have p9688_1 := h9688c.2.1
                          have p9688_2 := h9688c.2.2.1
                          have p9688_3 := h9688c.2.2.2
                          linarith only [h2, hlam, p9688_0]
                        · have p9688_0 := h9688c.1
                          have p9688_1 := h9688c.2.1
                          have p9688_2 := h9688c.2.2.1
                          have p9688_3 := h9688c.2.2.2
                          rcases p9688_3 (m.d 0 1) (by simp) with h9762 | h9762
                          · rcases p9688_3 (m.d 1 2) (by simp) with h9763 | h9763
                            · linarith only [h9581, h9763, hlam]
                            · rcases p9688_3 (m.d 1 3) (by simp) with h9765 | h9765
                              · linarith only [h9589, h9765, hlam]
                              · linarith only [h9579, h9765, hlam]
                          · linarith only [h0, h9762, hlam]
                        · have p9688_0 := h9688c.1
                          have p9688_1 := h9688c.2.1
                          have p9688_2 := h9688c.2.2.1
                          have p9688_3 := h9688c.2.2.2
                          rcases p9688_3 (m.d 0 1) (by simp) with h9769 | h9769
                          · rcases p9688_3 (m.d 1 2) (by simp) with h9770 | h9770
                            · linarith only [h9581, h9770, hlam]
                            · rcases p9688_3 (m.d 1 3) (by simp) with h9772 | h9772
                              · linarith only [h9589, h9772, hlam]
                              · rcases p9688_3 (m.d 1 4) (by simp) with h9774 | h9774
                                · rcases p9688_3 (m.d 1 5) (by simp) with h9775 | h9775
                                  · linarith only [h9593, h9775, hlam]
                                  · linarith only [h9591, h9775, hlam]
                                · linarith only [h9589, h9774, hlam]
                          · linarith only [h1, h9769, hlam]
                        · have p9688_0 := h9688c.1
                          have p9688_1 := h9688c.2.1
                          have p9688_2 := h9688c.2.2.1
                          have p9688_3 := h9688c.2.2.2
                          linarith only [hlam, p9688_0]
                        · have p9688_0 := h9688c.1
                          have p9688_1 := h9688c.2.1
                          have p9688_2 := h9688c.2.2.1
                          have p9688_3 := h9688c.2.2.2
                          rcases p9688_3 (m.d 0 1) (by simp) with h9781 | h9781
                          · rcases p9688_3 (m.d 1 2) (by simp) with h9782 | h9782
                            · linarith only [h9581, h9782, hlam]
                            · rcases p9688_3 (m.d 1 3) (by simp) with h9784 | h9784
                              · linarith only [h9589, h9784, hlam]
                              · rcases p9688_3 (m.d 1 4) (by simp) with h9786 | h9786
                                · rcases p9688_3 (m.d 1 5) (by simp) with h9787 | h9787
                                  · linarith only [h9593, h9787, hlam]
                                  · rcases h3bigk with h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [hlam, p9789_0]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h4, h9579, h9684, h9687, hc12, hc34, hlam, hphi, ht23, p9789_1]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h4, hlam, p9789_1]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h7232, hlam, p9789_0]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h9180, hlam, p9789_0]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h1, hlam, p9789_0]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [hlam, p9789_0]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h9579, hlam, p9789_1]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h9589, hlam, p9789_0]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h9591, hlam, p9789_0]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h9684, h9687, hc03, hc34, hlam, hphi, p9789_1]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h9579, h9684, h9687, hc12, hc34, hlam, hphi, ht23, p9789_1]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [hlam, p9789_0]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h9594, hlam, p9789_0]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h9684, hlam, p9789_0]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h1, h9579, hc12, hc34, hlam, hphi, ht23, p9789_1]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h9579, hc12, hc34, hlam, hphi, ht23, p9789_1]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [hc23, hc34, hlam, hphi, p9789_1]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [hlam, p9789_0]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h1, h9180, h9579, hc12, hc34, hlam, hphi, ht23, p9789_1]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h1, h9579, hc12, hc35, hlam, hphi, ht23, p9789_1]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h9579, hc12, hc35, hlam, hphi, ht23, p9789_1]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p9789_1]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h9687, hlam, p9789_0]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [hlam, p9789_0]
                                · linarith only [h9593, h9786, hlam]
                          · linarith only [h3, h9781, hlam]
                        · have p9688_0 := h9688c.1
                          have p9688_1 := h9688c.2.1
                          have p9688_2 := h9688c.2.2.1
                          have p9688_3 := h9688c.2.2.2
                          linarith only [h3, hlam, p9688_0]
                        · have p9688_0 := h9688c.1
                          have p9688_1 := h9688c.2.1
                          have p9688_2 := h9688c.2.2.1
                          have p9688_3 := h9688c.2.2.2
                          rcases p9688_3 (m.d 0 1) (by simp) with h9818 | h9818
                          · rcases p9688_3 (m.d 1 2) (by simp) with h9819 | h9819
                            · linarith only [h9583, h9819, hlam]
                            · rcases p9688_3 (m.d 1 3) (by simp) with h9821 | h9821
                              · linarith only [h9591, h9821, hlam]
                              · linarith only [h9579, h9821, hlam]
                          · linarith only [h0, h9818, hlam]
                        · have p9688_0 := h9688c.1
                          have p9688_1 := h9688c.2.1
                          have p9688_2 := h9688c.2.2.1
                          have p9688_3 := h9688c.2.2.2
                          rcases p9688_3 (m.d 0 1) (by simp) with h9825 | h9825
                          · rcases p9688_3 (m.d 1 2) (by simp) with h9826 | h9826
                            · linarith only [h9583, h9826, hlam]
                            · rcases p9688_3 (m.d 1 3) (by simp) with h9828 | h9828
                              · linarith only [h9591, h9828, hlam]
                              · rcases p9688_3 (m.d 1 4) (by simp) with h9830 | h9830
                                · rcases p9688_3 (m.d 1 5) (by simp) with h9831 | h9831
                                  · rcases h3bigk with h9832c | h9832c | h9832c | h9832c | h9832c | h9832c | h9832c | h9832c | h9832c | h9832c | h9832c | h9832c | h9832c | h9832c | h9832c | h9832c | h9832c | h9832c | h9832c | h9832c | h9832c | h9832c | h9832c | h9832c | h9832c
                                    · have p9832_0 := h9832c.1
                                      have p9832_1 := h9832c.2.1
                                      have p9832_2 := h9832c.2.2.1
                                      have p9832_3 := h9832c.2.2.2
                                      linarith only [hlam, p9832_0]
                                    · have p9832_0 := h9832c.1
                                      have p9832_1 := h9832c.2.1
                                      have p9832_2 := h9832c.2.2.1
                                      have p9832_3 := h9832c.2.2.2
                                      linarith only [h4, h9579, hc12, hc23, hlam, hphi, p9832_1]
                                    · have p9832_0 := h9832c.1
                                      have p9832_1 := h9832c.2.1
                                      have p9832_2 := h9832c.2.2.1
                                      have p9832_3 := h9832c.2.2.2
                                      linarith only [h4, hlam, p9832_1]
                                    · have p9832_0 := h9832c.1
                                      have p9832_1 := h9832c.2.1
                                      have p9832_2 := h9832c.2.2.1
                                      have p9832_3 := h9832c.2.2.2
                                      linarith only [h7232, hlam, p9832_0]
                                    · have p9832_0 := h9832c.1
                                      have p9832_1 := h9832c.2.1
                                      have p9832_2 := h9832c.2.2.1
                                      have p9832_3 := h9832c.2.2.2
                                      linarith only [h9180, hlam, p9832_0]
                                    · have p9832_0 := h9832c.1
                                      have p9832_1 := h9832c.2.1
                                      have p9832_2 := h9832c.2.2.1
                                      have p9832_3 := h9832c.2.2.2
                                      linarith only [h1, hlam, p9832_0]
                                    · have p9832_0 := h9832c.1
                                      have p9832_1 := h9832c.2.1
                                      have p9832_2 := h9832c.2.2.1
                                      have p9832_3 := h9832c.2.2.2
                                      linarith only [hlam, p9832_0]
                                    · have p9832_0 := h9832c.1
                                      have p9832_1 := h9832c.2.1
                                      have p9832_2 := h9832c.2.2.1
                                      have p9832_3 := h9832c.2.2.2
                                      linarith only [h9579, hlam, p9832_1]
                                    · have p9832_0 := h9832c.1
                                      have p9832_1 := h9832c.2.1
                                      have p9832_2 := h9832c.2.2.1
                                      have p9832_3 := h9832c.2.2.2
                                      linarith only [h9589, hlam, p9832_0]
                                    · have p9832_0 := h9832c.1
                                      have p9832_1 := h9832c.2.1
                                      have p9832_2 := h9832c.2.2.1
                                      have p9832_3 := h9832c.2.2.2
                                      linarith only [h9591, hlam, p9832_0]
                                    · have p9832_0 := h9832c.1
                                      have p9832_1 := h9832c.2.1
                                      have p9832_2 := h9832c.2.2.1
                                      have p9832_3 := h9832c.2.2.2
                                      linarith only [h1, h9579, hc12, hc23, hlam, hphi, p9832_1]
                                    · have p9832_0 := h9832c.1
                                      have p9832_1 := h9832c.2.1
                                      have p9832_2 := h9832c.2.2.1
                                      have p9832_3 := h9832c.2.2.2
                                      linarith only [h9579, hc12, hc23, hlam, hphi, p9832_1]
                                    · have p9832_0 := h9832c.1
                                      have p9832_1 := h9832c.2.1
                                      have p9832_2 := h9832c.2.2.1
                                      have p9832_3 := h9832c.2.2.2
                                      linarith only [hlam, p9832_0]
                                    · have p9832_0 := h9832c.1
                                      have p9832_1 := h9832c.2.1
                                      have p9832_2 := h9832c.2.2.1
                                      have p9832_3 := h9832c.2.2.2
                                      linarith only [h9594, hlam, p9832_0]
                                    · have p9832_0 := h9832c.1
                                      have p9832_1 := h9832c.2.1
                                      have p9832_2 := h9832c.2.2.1
                                      have p9832_3 := h9832c.2.2.2
                                      linarith only [h9684, hlam, p9832_0]
                                    · have p9832_0 := h9832c.1
                                      have p9832_1 := h9832c.2.1
                                      have p9832_2 := h9832c.2.2.1
                                      have p9832_3 := h9832c.2.2.2
                                      linarith only [h1, h9579, hc12, hc34, hlam, hphi, ht23, p9832_1]
                                    · have p9832_0 := h9832c.1
                                      have p9832_1 := h9832c.2.1
                                      have p9832_2 := h9832c.2.2.1
                                      have p9832_3 := h9832c.2.2.2
                                      linarith only [h9579, hc12, hc34, hlam, hphi, ht23, p9832_1]
                                    · have p9832_0 := h9832c.1
                                      have p9832_1 := h9832c.2.1
                                      have p9832_2 := h9832c.2.2.1
                                      have p9832_3 := h9832c.2.2.2
                                      linarith only [hc23, hc34, hlam, hphi, p9832_1]
                                    · have p9832_0 := h9832c.1
                                      have p9832_1 := h9832c.2.1
                                      have p9832_2 := h9832c.2.2.1
                                      have p9832_3 := h9832c.2.2.2
                                      linarith only [hlam, p9832_0]
                                    · have p9832_0 := h9832c.1
                                      have p9832_1 := h9832c.2.1
                                      have p9832_2 := h9832c.2.2.1
                                      have p9832_3 := h9832c.2.2.2
                                      linarith only [h1, h9180, h9579, hc12, hc34, hlam, hphi, ht23, p9832_1]
                                    · have p9832_0 := h9832c.1
                                      have p9832_1 := h9832c.2.1
                                      have p9832_2 := h9832c.2.2.1
                                      have p9832_3 := h9832c.2.2.2
                                      linarith only [h1, h9579, hc12, hc35, hlam, hphi, ht23, p9832_1]
                                    · have p9832_0 := h9832c.1
                                      have p9832_1 := h9832c.2.1
                                      have p9832_2 := h9832c.2.2.1
                                      have p9832_3 := h9832c.2.2.2
                                      linarith only [h9579, hc12, hc35, hlam, hphi, ht23, p9832_1]
                                    · have p9832_0 := h9832c.1
                                      have p9832_1 := h9832c.2.1
                                      have p9832_2 := h9832c.2.2.1
                                      have p9832_3 := h9832c.2.2.2
                                      linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p9832_1]
                                    · have p9832_0 := h9832c.1
                                      have p9832_1 := h9832c.2.1
                                      have p9832_2 := h9832c.2.2.1
                                      have p9832_3 := h9832c.2.2.2
                                      linarith only [h9687, hlam, p9832_0]
                                    · have p9832_0 := h9832c.1
                                      have p9832_1 := h9832c.2.1
                                      have p9832_2 := h9832c.2.2.1
                                      have p9832_3 := h9832c.2.2.2
                                      linarith only [hlam, p9832_0]
                                  · linarith only [h9591, h9831, hlam]
                                · linarith only [h9589, h9830, hlam]
                          · linarith only [h1, h9825, hlam]
                        · have p9688_0 := h9688c.1
                          have p9688_1 := h9688c.2.1
                          have p9688_2 := h9688c.2.2.1
                          have p9688_3 := h9688c.2.2.2
                          linarith only [h9593, hlam, p9688_0]
                        · have p9688_0 := h9688c.1
                          have p9688_1 := h9688c.2.1
                          have p9688_2 := h9688c.2.2.1
                          have p9688_3 := h9688c.2.2.2
                          linarith only [hlam, p9688_0]
                      · linarith only [h6364, h9578, h9594, h9687, hlam]
                    · linarith only [h2, h6364, h9593, h9686, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h9865 | h9865
                · linarith only [h7232, h9578, h9581, h9593, h9865, hc12, hc23, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9867 | h9867
                  · linarith only [h1, h9180, h9579, h9865, h9867, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9869 | h9869
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9870 | h9870
                      · rcases h1bigk with h9871c | h9871c | h9871c | h9871c | h9871c | h9871c | h9871c | h9871c | h9871c | h9871c | h9871c | h9871c | h9871c | h9871c | h9871c | h9871c | h9871c | h9871c | h9871c | h9871c | h9871c | h9871c | h9871c | h9871c | h9871c
                        · have p9871_0 := h9871c.1
                          have p9871_1 := h9871c.2.1
                          have p9871_2 := h9871c.2.2.1
                          have p9871_3 := h9871c.2.2.2
                          linarith only [hlam, p9871_0]
                        · have p9871_0 := h9871c.1
                          have p9871_1 := h9871c.2.1
                          have p9871_2 := h9871c.2.2.1
                          have p9871_3 := h9871c.2.2.2
                          rcases p9871_3 (m.d 0 1) (by simp) with h9873 | h9873
                          · rcases p9871_3 (m.d 1 2) (by simp) with h9874 | h9874
                            · linarith only [h9874, hlam, p9871_0]
                            · rcases p9871_3 (m.d 1 3) (by simp) with h9876 | h9876
                              · linarith only [h1, h9876, hlam]
                              · linarith only [h9579, h9876, hlam]
                          · linarith only [h9873, hlam, p9871_0]
                        · have p9871_0 := h9871c.1
                          have p9871_1 := h9871c.2.1
                          have p9871_2 := h9871c.2.2.1
                          have p9871_3 := h9871c.2.2.2
                          rcases p9871_3 (m.d 0 1) (by simp) with h9880 | h9880
                          · rcases p9871_3 (m.d 1 2) (by simp) with h9881 | h9881
                            · linarith only [h0, h9881, hlam]
                            · rcases p9871_3 (m.d 1 3) (by simp) with h9883 | h9883
                              · linarith only [h9883, hlam, p9871_0]
                              · rcases p9871_3 (m.d 1 4) (by simp) with h9885 | h9885
                                · linarith only [h2, h9885, hlam]
                                · linarith only [h9589, h9885, hlam]
                          · linarith only [h9880, hlam, p9871_0]
                        · have p9871_0 := h9871c.1
                          have p9871_1 := h9871c.2.1
                          have p9871_2 := h9871c.2.2.1
                          have p9871_3 := h9871c.2.2.2
                          rcases p9871_3 (m.d 0 1) (by simp) with h9889 | h9889
                          · rcases p9871_3 (m.d 1 2) (by simp) with h9890 | h9890
                            · linarith only [h0, h9890, hlam]
                            · rcases p9871_3 (m.d 1 3) (by simp) with h9892 | h9892
                              · linarith only [h1, h9892, hlam]
                              · rcases p9871_3 (m.d 1 4) (by simp) with h9894 | h9894
                                · linarith only [h9894, hlam, p9871_0]
                                · rcases p9871_3 (m.d 1 5) (by simp) with h9896 | h9896
                                  · linarith only [h3, h9896, hlam]
                                  · linarith only [h9593, h9896, hlam]
                          · linarith only [h9889, hlam, p9871_0]
                        · have p9871_0 := h9871c.1
                          have p9871_1 := h9871c.2.1
                          have p9871_2 := h9871c.2.2.1
                          have p9871_3 := h9871c.2.2.2
                          rcases p9871_3 (m.d 0 1) (by simp) with h9900 | h9900
                          · rcases p9871_3 (m.d 1 2) (by simp) with h9901 | h9901
                            · linarith only [h0, h9901, hlam]
                            · rcases p9871_3 (m.d 1 3) (by simp) with h9903 | h9903
                              · linarith only [h1, h9903, hlam]
                              · rcases p9871_3 (m.d 1 4) (by simp) with h9905 | h9905
                                · linarith only [h2, h9905, hlam]
                                · rcases p9871_3 (m.d 1 5) (by simp) with h9907 | h9907
                                  · linarith only [h9907, hlam, p9871_0]
                                  · rcases h3bigk with h9909c | h9909c | h9909c | h9909c | h9909c | h9909c | h9909c | h9909c | h9909c | h9909c | h9909c | h9909c | h9909c | h9909c | h9909c | h9909c | h9909c | h9909c | h9909c | h9909c | h9909c | h9909c | h9909c | h9909c | h9909c
                                    · have p9909_0 := h9909c.1
                                      have p9909_1 := h9909c.2.1
                                      have p9909_2 := h9909c.2.2.1
                                      have p9909_3 := h9909c.2.2.2
                                      linarith only [hlam, p9909_0]
                                    · have p9909_0 := h9909c.1
                                      have p9909_1 := h9909c.2.1
                                      have p9909_2 := h9909c.2.2.1
                                      have p9909_3 := h9909c.2.2.2
                                      linarith only [h4, h9579, h9867, h9870, hc12, hc34, hlam, hphi, ht23, p9909_1]
                                    · have p9909_0 := h9909c.1
                                      have p9909_1 := h9909c.2.1
                                      have p9909_2 := h9909c.2.2.1
                                      have p9909_3 := h9909c.2.2.2
                                      linarith only [h4, hlam, p9909_1]
                                    · have p9909_0 := h9909c.1
                                      have p9909_1 := h9909c.2.1
                                      have p9909_2 := h9909c.2.2.1
                                      have p9909_3 := h9909c.2.2.2
                                      linarith only [h7232, hlam, p9909_0]
                                    · have p9909_0 := h9909c.1
                                      have p9909_1 := h9909c.2.1
                                      have p9909_2 := h9909c.2.2.1
                                      have p9909_3 := h9909c.2.2.2
                                      linarith only [h9180, hlam, p9909_0]
                                    · have p9909_0 := h9909c.1
                                      have p9909_1 := h9909c.2.1
                                      have p9909_2 := h9909c.2.2.1
                                      have p9909_3 := h9909c.2.2.2
                                      linarith only [h1, hlam, p9909_0]
                                    · have p9909_0 := h9909c.1
                                      have p9909_1 := h9909c.2.1
                                      have p9909_2 := h9909c.2.2.1
                                      have p9909_3 := h9909c.2.2.2
                                      linarith only [hlam, p9909_0]
                                    · have p9909_0 := h9909c.1
                                      have p9909_1 := h9909c.2.1
                                      have p9909_2 := h9909c.2.2.1
                                      have p9909_3 := h9909c.2.2.2
                                      linarith only [h9579, hlam, p9909_1]
                                    · have p9909_0 := h9909c.1
                                      have p9909_1 := h9909c.2.1
                                      have p9909_2 := h9909c.2.2.1
                                      have p9909_3 := h9909c.2.2.2
                                      linarith only [h9589, hlam, p9909_0]
                                    · have p9909_0 := h9909c.1
                                      have p9909_1 := h9909c.2.1
                                      have p9909_2 := h9909c.2.2.1
                                      have p9909_3 := h9909c.2.2.2
                                      linarith only [h9591, hlam, p9909_0]
                                    · have p9909_0 := h9909c.1
                                      have p9909_1 := h9909c.2.1
                                      have p9909_2 := h9909c.2.2.1
                                      have p9909_3 := h9909c.2.2.2
                                      linarith only [h9867, h9870, hc03, hc34, hlam, hphi, p9909_1]
                                    · have p9909_0 := h9909c.1
                                      have p9909_1 := h9909c.2.1
                                      have p9909_2 := h9909c.2.2.1
                                      have p9909_3 := h9909c.2.2.2
                                      linarith only [h9579, h9867, h9870, hc12, hc34, hlam, hphi, ht23, p9909_1]
                                    · have p9909_0 := h9909c.1
                                      have p9909_1 := h9909c.2.1
                                      have p9909_2 := h9909c.2.2.1
                                      have p9909_3 := h9909c.2.2.2
                                      linarith only [hlam, p9909_0]
                                    · have p9909_0 := h9909c.1
                                      have p9909_1 := h9909c.2.1
                                      have p9909_2 := h9909c.2.2.1
                                      have p9909_3 := h9909c.2.2.2
                                      linarith only [h9865, hlam, p9909_0]
                                    · have p9909_0 := h9909c.1
                                      have p9909_1 := h9909c.2.1
                                      have p9909_2 := h9909c.2.2.1
                                      have p9909_3 := h9909c.2.2.2
                                      linarith only [h9867, hlam, p9909_0]
                                    · have p9909_0 := h9909c.1
                                      have p9909_1 := h9909c.2.1
                                      have p9909_2 := h9909c.2.2.1
                                      have p9909_3 := h9909c.2.2.2
                                      linarith only [h1, h9579, hc12, hc34, hlam, hphi, ht23, p9909_1]
                                    · have p9909_0 := h9909c.1
                                      have p9909_1 := h9909c.2.1
                                      have p9909_2 := h9909c.2.2.1
                                      have p9909_3 := h9909c.2.2.2
                                      linarith only [h9579, hc12, hc34, hlam, hphi, ht23, p9909_1]
                                    · have p9909_0 := h9909c.1
                                      have p9909_1 := h9909c.2.1
                                      have p9909_2 := h9909c.2.2.1
                                      have p9909_3 := h9909c.2.2.2
                                      linarith only [hc23, hc34, hlam, hphi, p9909_1]
                                    · have p9909_0 := h9909c.1
                                      have p9909_1 := h9909c.2.1
                                      have p9909_2 := h9909c.2.2.1
                                      have p9909_3 := h9909c.2.2.2
                                      linarith only [hlam, p9909_0]
                                    · have p9909_0 := h9909c.1
                                      have p9909_1 := h9909c.2.1
                                      have p9909_2 := h9909c.2.2.1
                                      have p9909_3 := h9909c.2.2.2
                                      linarith only [h1, h9180, h9579, hc12, hc34, hlam, hphi, ht23, p9909_1]
                                    · have p9909_0 := h9909c.1
                                      have p9909_1 := h9909c.2.1
                                      have p9909_2 := h9909c.2.2.1
                                      have p9909_3 := h9909c.2.2.2
                                      linarith only [h1, h9579, hc12, hc35, hlam, hphi, ht23, p9909_1]
                                    · have p9909_0 := h9909c.1
                                      have p9909_1 := h9909c.2.1
                                      have p9909_2 := h9909c.2.2.1
                                      have p9909_3 := h9909c.2.2.2
                                      linarith only [h9579, hc12, hc35, hlam, hphi, ht23, p9909_1]
                                    · have p9909_0 := h9909c.1
                                      have p9909_1 := h9909c.2.1
                                      have p9909_2 := h9909c.2.2.1
                                      have p9909_3 := h9909c.2.2.2
                                      linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p9909_1]
                                    · have p9909_0 := h9909c.1
                                      have p9909_1 := h9909c.2.1
                                      have p9909_2 := h9909c.2.2.1
                                      have p9909_3 := h9909c.2.2.2
                                      linarith only [h9870, hlam, p9909_0]
                                    · have p9909_0 := h9909c.1
                                      have p9909_1 := h9909c.2.1
                                      have p9909_2 := h9909c.2.2.1
                                      have p9909_3 := h9909c.2.2.2
                                      linarith only [hlam, p9909_0]
                          · linarith only [h9900, hlam, p9871_0]
                        · have p9871_0 := h9871c.1
                          have p9871_1 := h9871c.2.1
                          have p9871_2 := h9871c.2.2.1
                          have p9871_3 := h9871c.2.2.2
                          linarith only [h0, hlam, p9871_0]
                        · have p9871_0 := h9871c.1
                          have p9871_1 := h9871c.2.1
                          have p9871_2 := h9871c.2.2.1
                          have p9871_3 := h9871c.2.2.2
                          linarith only [hlam, p9871_0]
                        · have p9871_0 := h9871c.1
                          have p9871_1 := h9871c.2.1
                          have p9871_2 := h9871c.2.2.1
                          have p9871_3 := h9871c.2.2.2
                          linarith only [h9579, hlam, p9871_0]
                        · have p9871_0 := h9871c.1
                          have p9871_1 := h9871c.2.1
                          have p9871_2 := h9871c.2.2.1
                          have p9871_3 := h9871c.2.2.2
                          linarith only [h9581, hlam, p9871_0]
                        · have p9871_0 := h9871c.1
                          have p9871_1 := h9871c.2.1
                          have p9871_2 := h9871c.2.2.1
                          have p9871_3 := h9871c.2.2.2
                          linarith only [h9583, hlam, p9871_0]
                        · have p9871_0 := h9871c.1
                          have p9871_1 := h9871c.2.1
                          have p9871_2 := h9871c.2.2.1
                          have p9871_3 := h9871c.2.2.2
                          linarith only [h1, hlam, p9871_0]
                        · have p9871_0 := h9871c.1
                          have p9871_1 := h9871c.2.1
                          have p9871_2 := h9871c.2.2.1
                          have p9871_3 := h9871c.2.2.2
                          linarith only [h2, h9578, h9589, h9593, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p9871_1]
                        · have p9871_0 := h9871c.1
                          have p9871_1 := h9871c.2.1
                          have p9871_2 := h9871c.2.2.1
                          have p9871_3 := h9871c.2.2.2
                          linarith only [hlam, p9871_0]
                        · have p9871_0 := h9871c.1
                          have p9871_1 := h9871c.2.1
                          have p9871_2 := h9871c.2.2.1
                          have p9871_3 := h9871c.2.2.2
                          linarith only [h9589, hlam, p9871_1]
                        · have p9871_0 := h9871c.1
                          have p9871_1 := h9871c.2.1
                          have p9871_2 := h9871c.2.2.1
                          have p9871_3 := h9871c.2.2.2
                          linarith only [h9591, hlam, p9871_1]
                        · have p9871_0 := h9871c.1
                          have p9871_1 := h9871c.2.1
                          have p9871_2 := h9871c.2.2.1
                          have p9871_3 := h9871c.2.2.2
                          linarith only [h2, hlam, p9871_0]
                        · have p9871_0 := h9871c.1
                          have p9871_1 := h9871c.2.1
                          have p9871_2 := h9871c.2.2.1
                          have p9871_3 := h9871c.2.2.2
                          linarith only [h7232, h9578, h9593, hc12, hc34, hlam, hphi, ht23, p9871_1]
                        · have p9871_0 := h9871c.1
                          have p9871_1 := h9871c.2.1
                          have p9871_2 := h9871c.2.2.1
                          have p9871_3 := h9871c.2.2.2
                          linarith only [h7232, h9578, h9593, hc13, hc34, hlam, hphi, p9871_1]
                        · have p9871_0 := h9871c.1
                          have p9871_1 := h9871c.2.1
                          have p9871_2 := h9871c.2.2.1
                          have p9871_3 := h9871c.2.2.2
                          linarith only [hlam, p9871_0]
                        · have p9871_0 := h9871c.1
                          have p9871_1 := h9871c.2.1
                          have p9871_2 := h9871c.2.2.1
                          have p9871_3 := h9871c.2.2.2
                          linarith only [h9593, hlam, p9871_1]
                        · have p9871_0 := h9871c.1
                          have p9871_1 := h9871c.2.1
                          have p9871_2 := h9871c.2.2.1
                          have p9871_3 := h9871c.2.2.2
                          linarith only [h3, hlam, p9871_0]
                        · have p9871_0 := h9871c.1
                          have p9871_1 := h9871c.2.1
                          have p9871_2 := h9871c.2.2.1
                          have p9871_3 := h9871c.2.2.2
                          linarith only [h7232, h9578, h9593, hc12, hc34, hlam, hphi, ht23, p9871_1]
                        · have p9871_0 := h9871c.1
                          have p9871_1 := h9871c.2.1
                          have p9871_2 := h9871c.2.2.1
                          have p9871_3 := h9871c.2.2.2
                          linarith only [h7232, h9578, h9579, h9593, hc12, hc34, hlam, hphi, ht23, p9871_1]
                        · have p9871_0 := h9871c.1
                          have p9871_1 := h9871c.2.1
                          have p9871_2 := h9871c.2.2.1
                          have p9871_3 := h9871c.2.2.2
                          linarith only [h7232, h9578, h9581, h9593, hc12, hc34, hlam, hphi, ht23, p9871_1]
                        · have p9871_0 := h9871c.1
                          have p9871_1 := h9871c.2.1
                          have p9871_2 := h9871c.2.2.1
                          have p9871_3 := h9871c.2.2.2
                          linarith only [hlam, p9871_0]
                      · linarith only [h6364, h9578, h9865, h9870, hlam]
                    · linarith only [h6364, h9578, h9869, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h9958 | h9958
    · linarith only [h0, h4, h9958, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h9960 | h9960
      · linarith only [h0, h6364, h9960, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h9962 | h9962
        · rcases m.htr 1 3 4 (by decide) (by decide) with h9963 | h9963
          · linarith only [h0, h1, h4, h7232, h9962, h9963, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h9965 | h9965
            · linarith only [h1, h9180, h9965, hlam]
            · linarith only [h9958, h9962, h9965, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h9968 | h9968
          · linarith only [h1, h7232, h9968, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h9970 | h9970
            · linarith only [h1, h9180, h9970, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h9972 | h9972
              · linarith only [h2, h9578, h9972, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h9974 | h9974
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9975 | h9975
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9976 | h9976
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9977 | h9977
                      · linarith only [h0, h4, h7232, h9578, h9974, h9977, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h4, h7232, h9976, h9977, hc12, hc24, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9980 | h9980
                      · linarith only [h0, h6364, h9976, h9980, hc12, hc34, hlam, hphi, ht23]
                      · rcases h1bigk with h9982c | h9982c | h9982c | h9982c | h9982c | h9982c | h9982c | h9982c | h9982c | h9982c | h9982c | h9982c | h9982c | h9982c | h9982c | h9982c | h9982c | h9982c | h9982c | h9982c | h9982c | h9982c | h9982c | h9982c | h9982c
                        · have p9982_0 := h9982c.1
                          have p9982_1 := h9982c.2.1
                          have p9982_2 := h9982c.2.2.1
                          have p9982_3 := h9982c.2.2.2
                          linarith only [hlam, p9982_0]
                        · have p9982_0 := h9982c.1
                          have p9982_1 := h9982c.2.1
                          have p9982_2 := h9982c.2.2.1
                          have p9982_3 := h9982c.2.2.2
                          rcases p9982_3 (m.d 0 1) (by simp) with h9984 | h9984
                          · rcases p9982_3 (m.d 1 2) (by simp) with h9985 | h9985
                            · linarith only [h9985, hlam, p9982_0]
                            · rcases p9982_3 (m.d 1 3) (by simp) with h9987 | h9987
                              · linarith only [h1, h9987, hlam]
                              · linarith only [h9958, h9987, hlam]
                          · linarith only [h9984, hlam, p9982_0]
                        · have p9982_0 := h9982c.1
                          have p9982_1 := h9982c.2.1
                          have p9982_2 := h9982c.2.2.1
                          have p9982_3 := h9982c.2.2.2
                          rcases p9982_3 (m.d 0 1) (by simp) with h9991 | h9991
                          · rcases p9982_3 (m.d 1 2) (by simp) with h9992 | h9992
                            · linarith only [h0, h9992, hlam]
                            · rcases p9982_3 (m.d 1 3) (by simp) with h9994 | h9994
                              · linarith only [h9994, hlam, p9982_0]
                              · rcases p9982_3 (m.d 1 4) (by simp) with h9996 | h9996
                                · linarith only [h2, h9996, hlam]
                                · linarith only [h9968, h9996, hlam]
                          · linarith only [h9991, hlam, p9982_0]
                        · have p9982_0 := h9982c.1
                          have p9982_1 := h9982c.2.1
                          have p9982_2 := h9982c.2.2.1
                          have p9982_3 := h9982c.2.2.2
                          rcases p9982_3 (m.d 0 1) (by simp) with h10000 | h10000
                          · rcases p9982_3 (m.d 1 2) (by simp) with h10001 | h10001
                            · linarith only [h0, h10001, hlam]
                            · rcases p9982_3 (m.d 1 3) (by simp) with h10003 | h10003
                              · linarith only [h1, h10003, hlam]
                              · rcases p9982_3 (m.d 1 4) (by simp) with h10005 | h10005
                                · linarith only [h10005, hlam, p9982_0]
                                · rcases p9982_3 (m.d 1 5) (by simp) with h10007 | h10007
                                  · linarith only [h10007, h3, hlam]
                                  · linarith only [h10007, h9972, hlam]
                          · linarith only [h10000, hlam, p9982_0]
                        · have p9982_0 := h9982c.1
                          have p9982_1 := h9982c.2.1
                          have p9982_2 := h9982c.2.2.1
                          have p9982_3 := h9982c.2.2.2
                          rcases p9982_3 (m.d 0 1) (by simp) with h10011 | h10011
                          · rcases p9982_3 (m.d 1 2) (by simp) with h10012 | h10012
                            · linarith only [h0, h10012, hlam]
                            · rcases p9982_3 (m.d 1 3) (by simp) with h10014 | h10014
                              · linarith only [h1, h10014, hlam]
                              · rcases p9982_3 (m.d 1 4) (by simp) with h10016 | h10016
                                · linarith only [h10016, h2, hlam]
                                · rcases p9982_3 (m.d 1 5) (by simp) with h10018 | h10018
                                  · linarith only [h10018, hlam, p9982_0]
                                  · rcases h3bigk with h10020c | h10020c | h10020c | h10020c | h10020c | h10020c | h10020c | h10020c | h10020c | h10020c | h10020c | h10020c | h10020c | h10020c | h10020c | h10020c | h10020c | h10020c | h10020c | h10020c | h10020c | h10020c | h10020c | h10020c | h10020c
                                    · have p10020_0 := h10020c.1
                                      have p10020_1 := h10020c.2.1
                                      have p10020_2 := h10020c.2.2.1
                                      have p10020_3 := h10020c.2.2.2
                                      linarith only [hlam, p10020_0]
                                    · have p10020_0 := h10020c.1
                                      have p10020_1 := h10020c.2.1
                                      have p10020_2 := h10020c.2.2.1
                                      have p10020_3 := h10020c.2.2.2
                                      linarith only [h7232, h9974, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p10020_1]
                                    · have p10020_0 := h10020c.1
                                      have p10020_1 := h10020c.2.1
                                      have p10020_2 := h10020c.2.2.1
                                      have p10020_3 := h10020c.2.2.2
                                      linarith only [h4, hlam, p10020_1]
                                    · have p10020_0 := h10020c.1
                                      have p10020_1 := h10020c.2.1
                                      have p10020_2 := h10020c.2.2.1
                                      have p10020_3 := h10020c.2.2.2
                                      linarith only [h7232, hlam, p10020_0]
                                    · have p10020_0 := h10020c.1
                                      have p10020_1 := h10020c.2.1
                                      have p10020_2 := h10020c.2.2.1
                                      have p10020_3 := h10020c.2.2.2
                                      linarith only [h9180, hlam, p10020_0]
                                    · have p10020_0 := h10020c.1
                                      have p10020_1 := h10020c.2.1
                                      have p10020_2 := h10020c.2.2.1
                                      have p10020_3 := h10020c.2.2.2
                                      linarith only [h1, hlam, p10020_0]
                                    · have p10020_0 := h10020c.1
                                      have p10020_1 := h10020c.2.1
                                      have p10020_2 := h10020c.2.2.1
                                      have p10020_3 := h10020c.2.2.2
                                      linarith only [hlam, p10020_0]
                                    · have p10020_0 := h10020c.1
                                      have p10020_1 := h10020c.2.1
                                      have p10020_2 := h10020c.2.2.1
                                      have p10020_3 := h10020c.2.2.2
                                      linarith only [h9958, hlam, p10020_1]
                                    · have p10020_0 := h10020c.1
                                      have p10020_1 := h10020c.2.1
                                      have p10020_2 := h10020c.2.2.1
                                      have p10020_3 := h10020c.2.2.2
                                      linarith only [h9968, hlam, p10020_0]
                                    · have p10020_0 := h10020c.1
                                      have p10020_1 := h10020c.2.1
                                      have p10020_2 := h10020c.2.2.1
                                      have p10020_3 := h10020c.2.2.2
                                      linarith only [h9970, hlam, p10020_0]
                                    · have p10020_0 := h10020c.1
                                      have p10020_1 := h10020c.2.1
                                      have p10020_2 := h10020c.2.2.1
                                      have p10020_3 := h10020c.2.2.2
                                      linarith only [h4, hc02, hc23, hlam, hphi, p10020_1]
                                    · have p10020_0 := h10020c.1
                                      have p10020_1 := h10020c.2.1
                                      have p10020_2 := h10020c.2.2.1
                                      have p10020_3 := h10020c.2.2.2
                                      linarith only [h9958, hc12, hc23, hlam, hphi, p10020_1]
                                    · have p10020_0 := h10020c.1
                                      have p10020_1 := h10020c.2.1
                                      have p10020_2 := h10020c.2.2.1
                                      have p10020_3 := h10020c.2.2.2
                                      linarith only [hlam, p10020_0]
                                    · have p10020_0 := h10020c.1
                                      have p10020_1 := h10020c.2.1
                                      have p10020_2 := h10020c.2.2.1
                                      have p10020_3 := h10020c.2.2.2
                                      linarith only [h0, h4, h7232, hc12, hc23, hlam, hphi, p10020_1]
                                    · have p10020_0 := h10020c.1
                                      have p10020_1 := h10020c.2.1
                                      have p10020_2 := h10020c.2.2.1
                                      have p10020_3 := h10020c.2.2.2
                                      linarith only [h0, h4, h9180, hc12, hc23, hlam, hphi, p10020_1]
                                    · have p10020_0 := h10020c.1
                                      have p10020_1 := h10020c.2.1
                                      have p10020_2 := h10020c.2.2.1
                                      have p10020_3 := h10020c.2.2.2
                                      linarith only [h0, h4, h9974, hc12, hc24, hlam, hphi, p10020_1]
                                    · have p10020_0 := h10020c.1
                                      have p10020_1 := h10020c.2.1
                                      have p10020_2 := h10020c.2.2.1
                                      have p10020_3 := h10020c.2.2.2
                                      linarith only [h9958, h9974, h9976, hc12, hc45, hlam, hphi, ht23, ht34, p10020_1]
                                    · have p10020_0 := h10020c.1
                                      have p10020_1 := h10020c.2.1
                                      have p10020_2 := h10020c.2.2.1
                                      have p10020_3 := h10020c.2.2.2
                                      linarith only [h9974, hlam, p10020_0]
                                    · have p10020_0 := h10020c.1
                                      have p10020_1 := h10020c.2.1
                                      have p10020_2 := h10020c.2.2.1
                                      have p10020_3 := h10020c.2.2.2
                                      linarith only [hlam, p10020_0]
                                    · have p10020_0 := h10020c.1
                                      have p10020_1 := h10020c.2.1
                                      have p10020_2 := h10020c.2.2.1
                                      have p10020_3 := h10020c.2.2.2
                                      linarith only [h9980, hlam, p10020_1]
                                    · have p10020_0 := h10020c.1
                                      have p10020_1 := h10020c.2.1
                                      have p10020_2 := h10020c.2.2.1
                                      have p10020_3 := h10020c.2.2.2
                                      linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p10020_1]
                                    · have p10020_0 := h10020c.1
                                      have p10020_1 := h10020c.2.1
                                      have p10020_2 := h10020c.2.2.1
                                      have p10020_3 := h10020c.2.2.2
                                      linarith only [h9958, hc12, hc35, hlam, hphi, ht23, p10020_1]
                                    · have p10020_0 := h10020c.1
                                      have p10020_1 := h10020c.2.1
                                      have p10020_2 := h10020c.2.2.1
                                      have p10020_3 := h10020c.2.2.2
                                      linarith only [h9975, hlam, p10020_0]
                                    · have p10020_0 := h10020c.1
                                      have p10020_1 := h10020c.2.1
                                      have p10020_2 := h10020c.2.2.1
                                      have p10020_3 := h10020c.2.2.2
                                      linarith only [h9975, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10020_1]
                                    · have p10020_0 := h10020c.1
                                      have p10020_1 := h10020c.2.1
                                      have p10020_2 := h10020c.2.2.1
                                      have p10020_3 := h10020c.2.2.2
                                      linarith only [hlam, p10020_0]
                          · linarith only [h10011, hlam, p9982_0]
                        · have p9982_0 := h9982c.1
                          have p9982_1 := h9982c.2.1
                          have p9982_2 := h9982c.2.2.1
                          have p9982_3 := h9982c.2.2.2
                          linarith only [h0, hlam, p9982_0]
                        · have p9982_0 := h9982c.1
                          have p9982_1 := h9982c.2.1
                          have p9982_2 := h9982c.2.2.1
                          have p9982_3 := h9982c.2.2.2
                          linarith only [hlam, p9982_0]
                        · have p9982_0 := h9982c.1
                          have p9982_1 := h9982c.2.1
                          have p9982_2 := h9982c.2.2.1
                          have p9982_3 := h9982c.2.2.2
                          linarith only [h9958, hlam, p9982_0]
                        · have p9982_0 := h9982c.1
                          have p9982_1 := h9982c.2.1
                          have p9982_2 := h9982c.2.2.1
                          have p9982_3 := h9982c.2.2.2
                          linarith only [h9960, hlam, p9982_0]
                        · have p9982_0 := h9982c.1
                          have p9982_1 := h9982c.2.1
                          have p9982_2 := h9982c.2.2.1
                          have p9982_3 := h9982c.2.2.2
                          linarith only [h9962, hlam, p9982_0]
                        · have p9982_0 := h9982c.1
                          have p9982_1 := h9982c.2.1
                          have p9982_2 := h9982c.2.2.1
                          have p9982_3 := h9982c.2.2.2
                          linarith only [h1, hlam, p9982_0]
                        · have p9982_0 := h9982c.1
                          have p9982_1 := h9982c.2.1
                          have p9982_2 := h9982c.2.2.1
                          have p9982_3 := h9982c.2.2.2
                          linarith only [h1, h6364, h7232, h9976, hc12, hc45, hlam, hphi, ht23, ht34, p9982_1]
                        · have p9982_0 := h9982c.1
                          have p9982_1 := h9982c.2.1
                          have p9982_2 := h9982c.2.2.1
                          have p9982_3 := h9982c.2.2.2
                          linarith only [hlam, p9982_0]
                        · have p9982_0 := h9982c.1
                          have p9982_1 := h9982c.2.1
                          have p9982_2 := h9982c.2.2.1
                          have p9982_3 := h9982c.2.2.2
                          linarith only [h9968, hlam, p9982_1]
                        · have p9982_0 := h9982c.1
                          have p9982_1 := h9982c.2.1
                          have p9982_2 := h9982c.2.2.1
                          have p9982_3 := h9982c.2.2.2
                          linarith only [h9970, hlam, p9982_1]
                        · have p9982_0 := h9982c.1
                          have p9982_1 := h9982c.2.1
                          have p9982_2 := h9982c.2.2.1
                          have p9982_3 := h9982c.2.2.2
                          linarith only [h2, hlam, p9982_0]
                        · have p9982_0 := h9982c.1
                          have p9982_1 := h9982c.2.1
                          have p9982_2 := h9982c.2.2.1
                          have p9982_3 := h9982c.2.2.2
                          linarith only [h2, h6364, h9976, hc12, hc45, hlam, hphi, ht23, ht34, p9982_1]
                        · have p9982_0 := h9982c.1
                          have p9982_1 := h9982c.2.1
                          have p9982_2 := h9982c.2.2.1
                          have p9982_3 := h9982c.2.2.2
                          linarith only [h2, h6364, h9976, hc13, hc45, hlam, hphi, ht34, p9982_1]
                        · have p9982_0 := h9982c.1
                          have p9982_1 := h9982c.2.1
                          have p9982_2 := h9982c.2.2.1
                          have p9982_3 := h9982c.2.2.2
                          linarith only [hlam, p9982_0]
                        · have p9982_0 := h9982c.1
                          have p9982_1 := h9982c.2.1
                          have p9982_2 := h9982c.2.2.1
                          have p9982_3 := h9982c.2.2.2
                          linarith only [h9972, hlam, p9982_1]
                        · have p9982_0 := h9982c.1
                          have p9982_1 := h9982c.2.1
                          have p9982_2 := h9982c.2.2.1
                          have p9982_3 := h9982c.2.2.2
                          linarith only [h3, hlam, p9982_0]
                        · have p9982_0 := h9982c.1
                          have p9982_1 := h9982c.2.1
                          have p9982_2 := h9982c.2.2.1
                          have p9982_3 := h9982c.2.2.2
                          linarith only [h3, h9180, h9975, hc12, hc23, hlam, hphi, p9982_1]
                        · have p9982_0 := h9982c.1
                          have p9982_1 := h9982c.2.1
                          have p9982_2 := h9982c.2.2.1
                          have p9982_3 := h9982c.2.2.2
                          linarith only [h3, h9180, h9958, h9975, hc12, hc23, hlam, hphi, p9982_1]
                        · have p9982_0 := h9982c.1
                          have p9982_1 := h9982c.2.1
                          have p9982_2 := h9982c.2.2.1
                          have p9982_3 := h9982c.2.2.2
                          linarith only [h3, h9180, h9960, h9975, hc12, hc23, hlam, hphi, p9982_1]
                        · have p9982_0 := h9982c.1
                          have p9982_1 := h9982c.2.1
                          have p9982_2 := h9982c.2.2.1
                          have p9982_3 := h9982c.2.2.2
                          linarith only [hlam, p9982_0]
                  · linarith only [h7232, h9974, h9975, hc03, hc35, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h10068 | h10068
                  · linarith only [h10068, h9180, h9974, hc03, hc34, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h10070 | h10070
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h10071 | h10071
                      · rcases h1bigk with h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c | h10072c
                        · have p10072_0 := h10072c.1
                          have p10072_1 := h10072c.2.1
                          have p10072_2 := h10072c.2.2.1
                          have p10072_3 := h10072c.2.2.2
                          linarith only [hlam, p10072_0]
                        · have p10072_0 := h10072c.1
                          have p10072_1 := h10072c.2.1
                          have p10072_2 := h10072c.2.2.1
                          have p10072_3 := h10072c.2.2.2
                          rcases p10072_3 (m.d 0 1) (by simp) with h10074 | h10074
                          · rcases p10072_3 (m.d 1 2) (by simp) with h10075 | h10075
                            · linarith only [h10075, hlam, p10072_0]
                            · rcases p10072_3 (m.d 1 3) (by simp) with h10077 | h10077
                              · linarith only [h1, h10077, hlam]
                              · linarith only [h10077, h9958, hlam]
                          · linarith only [h10074, hlam, p10072_0]
                        · have p10072_0 := h10072c.1
                          have p10072_1 := h10072c.2.1
                          have p10072_2 := h10072c.2.2.1
                          have p10072_3 := h10072c.2.2.2
                          rcases p10072_3 (m.d 0 1) (by simp) with h10081 | h10081
                          · rcases p10072_3 (m.d 1 2) (by simp) with h10082 | h10082
                            · linarith only [h0, h10082, hlam]
                            · rcases p10072_3 (m.d 1 3) (by simp) with h10084 | h10084
                              · linarith only [h10084, hlam, p10072_0]
                              · rcases p10072_3 (m.d 1 4) (by simp) with h10086 | h10086
                                · linarith only [h10086, h2, hlam]
                                · linarith only [h10086, h9968, hlam]
                          · linarith only [h10081, hlam, p10072_0]
                        · have p10072_0 := h10072c.1
                          have p10072_1 := h10072c.2.1
                          have p10072_2 := h10072c.2.2.1
                          have p10072_3 := h10072c.2.2.2
                          rcases p10072_3 (m.d 0 1) (by simp) with h10090 | h10090
                          · rcases p10072_3 (m.d 1 2) (by simp) with h10091 | h10091
                            · linarith only [h0, h10091, hlam]
                            · rcases p10072_3 (m.d 1 3) (by simp) with h10093 | h10093
                              · linarith only [h1, h10093, hlam]
                              · rcases p10072_3 (m.d 1 4) (by simp) with h10095 | h10095
                                · linarith only [h10095, hlam, p10072_0]
                                · rcases p10072_3 (m.d 1 5) (by simp) with h10097 | h10097
                                  · linarith only [h10097, h3, hlam]
                                  · linarith only [h10097, h9972, hlam]
                          · linarith only [h10090, hlam, p10072_0]
                        · have p10072_0 := h10072c.1
                          have p10072_1 := h10072c.2.1
                          have p10072_2 := h10072c.2.2.1
                          have p10072_3 := h10072c.2.2.2
                          rcases p10072_3 (m.d 0 1) (by simp) with h10101 | h10101
                          · rcases p10072_3 (m.d 1 2) (by simp) with h10102 | h10102
                            · linarith only [h0, h10102, hlam]
                            · rcases p10072_3 (m.d 1 3) (by simp) with h10104 | h10104
                              · linarith only [h1, h10104, hlam]
                              · rcases p10072_3 (m.d 1 4) (by simp) with h10106 | h10106
                                · linarith only [h10106, h2, hlam]
                                · rcases p10072_3 (m.d 1 5) (by simp) with h10108 | h10108
                                  · linarith only [h10108, hlam, p10072_0]
                                  · rcases h3bigk with h10110c | h10110c | h10110c | h10110c | h10110c | h10110c | h10110c | h10110c | h10110c | h10110c | h10110c | h10110c | h10110c | h10110c | h10110c | h10110c | h10110c | h10110c | h10110c | h10110c | h10110c | h10110c | h10110c | h10110c | h10110c
                                    · have p10110_0 := h10110c.1
                                      have p10110_1 := h10110c.2.1
                                      have p10110_2 := h10110c.2.2.1
                                      have p10110_3 := h10110c.2.2.2
                                      linarith only [hlam, p10110_0]
                                    · have p10110_0 := h10110c.1
                                      have p10110_1 := h10110c.2.1
                                      have p10110_2 := h10110c.2.2.1
                                      have p10110_3 := h10110c.2.2.2
                                      linarith only [h10068, h10071, h4, h9958, hc12, hc34, hlam, hphi, ht23, p10110_1]
                                    · have p10110_0 := h10110c.1
                                      have p10110_1 := h10110c.2.1
                                      have p10110_2 := h10110c.2.2.1
                                      have p10110_3 := h10110c.2.2.2
                                      linarith only [h4, hlam, p10110_1]
                                    · have p10110_0 := h10110c.1
                                      have p10110_1 := h10110c.2.1
                                      have p10110_2 := h10110c.2.2.1
                                      have p10110_3 := h10110c.2.2.2
                                      linarith only [h7232, hlam, p10110_0]
                                    · have p10110_0 := h10110c.1
                                      have p10110_1 := h10110c.2.1
                                      have p10110_2 := h10110c.2.2.1
                                      have p10110_3 := h10110c.2.2.2
                                      linarith only [h9180, hlam, p10110_0]
                                    · have p10110_0 := h10110c.1
                                      have p10110_1 := h10110c.2.1
                                      have p10110_2 := h10110c.2.2.1
                                      have p10110_3 := h10110c.2.2.2
                                      linarith only [h1, hlam, p10110_0]
                                    · have p10110_0 := h10110c.1
                                      have p10110_1 := h10110c.2.1
                                      have p10110_2 := h10110c.2.2.1
                                      have p10110_3 := h10110c.2.2.2
                                      linarith only [hlam, p10110_0]
                                    · have p10110_0 := h10110c.1
                                      have p10110_1 := h10110c.2.1
                                      have p10110_2 := h10110c.2.2.1
                                      have p10110_3 := h10110c.2.2.2
                                      linarith only [h9958, hlam, p10110_1]
                                    · have p10110_0 := h10110c.1
                                      have p10110_1 := h10110c.2.1
                                      have p10110_2 := h10110c.2.2.1
                                      have p10110_3 := h10110c.2.2.2
                                      linarith only [h9968, hlam, p10110_0]
                                    · have p10110_0 := h10110c.1
                                      have p10110_1 := h10110c.2.1
                                      have p10110_2 := h10110c.2.2.1
                                      have p10110_3 := h10110c.2.2.2
                                      linarith only [h9970, hlam, p10110_0]
                                    · have p10110_0 := h10110c.1
                                      have p10110_1 := h10110c.2.1
                                      have p10110_2 := h10110c.2.2.1
                                      have p10110_3 := h10110c.2.2.2
                                      linarith only [h10068, h10071, hc03, hc34, hlam, hphi, p10110_1]
                                    · have p10110_0 := h10110c.1
                                      have p10110_1 := h10110c.2.1
                                      have p10110_2 := h10110c.2.2.1
                                      have p10110_3 := h10110c.2.2.2
                                      linarith only [h10068, h10071, h9958, hc12, hc34, hlam, hphi, ht23, p10110_1]
                                    · have p10110_0 := h10110c.1
                                      have p10110_1 := h10110c.2.1
                                      have p10110_2 := h10110c.2.2.1
                                      have p10110_3 := h10110c.2.2.2
                                      linarith only [hlam, p10110_0]
                                    · have p10110_0 := h10110c.1
                                      have p10110_1 := h10110c.2.1
                                      have p10110_2 := h10110c.2.2.1
                                      have p10110_3 := h10110c.2.2.2
                                      linarith only [h9974, hlam, p10110_0]
                                    · have p10110_0 := h10110c.1
                                      have p10110_1 := h10110c.2.1
                                      have p10110_2 := h10110c.2.2.1
                                      have p10110_3 := h10110c.2.2.2
                                      linarith only [h10068, hlam, p10110_0]
                                    · have p10110_0 := h10110c.1
                                      have p10110_1 := h10110c.2.1
                                      have p10110_2 := h10110c.2.2.1
                                      have p10110_3 := h10110c.2.2.2
                                      linarith only [h1, h9958, hc12, hc34, hlam, hphi, ht23, p10110_1]
                                    · have p10110_0 := h10110c.1
                                      have p10110_1 := h10110c.2.1
                                      have p10110_2 := h10110c.2.2.1
                                      have p10110_3 := h10110c.2.2.2
                                      linarith only [h9958, hc12, hc34, hlam, hphi, ht23, p10110_1]
                                    · have p10110_0 := h10110c.1
                                      have p10110_1 := h10110c.2.1
                                      have p10110_2 := h10110c.2.2.1
                                      have p10110_3 := h10110c.2.2.2
                                      linarith only [hc23, hc34, hlam, hphi, p10110_1]
                                    · have p10110_0 := h10110c.1
                                      have p10110_1 := h10110c.2.1
                                      have p10110_2 := h10110c.2.2.1
                                      have p10110_3 := h10110c.2.2.2
                                      linarith only [hlam, p10110_0]
                                    · have p10110_0 := h10110c.1
                                      have p10110_1 := h10110c.2.1
                                      have p10110_2 := h10110c.2.2.1
                                      have p10110_3 := h10110c.2.2.2
                                      linarith only [h1, h9180, h9958, hc12, hc34, hlam, hphi, ht23, p10110_1]
                                    · have p10110_0 := h10110c.1
                                      have p10110_1 := h10110c.2.1
                                      have p10110_2 := h10110c.2.2.1
                                      have p10110_3 := h10110c.2.2.2
                                      linarith only [h1, h9958, hc12, hc35, hlam, hphi, ht23, p10110_1]
                                    · have p10110_0 := h10110c.1
                                      have p10110_1 := h10110c.2.1
                                      have p10110_2 := h10110c.2.2.1
                                      have p10110_3 := h10110c.2.2.2
                                      linarith only [h9958, hc12, hc35, hlam, hphi, ht23, p10110_1]
                                    · have p10110_0 := h10110c.1
                                      have p10110_1 := h10110c.2.1
                                      have p10110_2 := h10110c.2.2.1
                                      have p10110_3 := h10110c.2.2.2
                                      linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p10110_1]
                                    · have p10110_0 := h10110c.1
                                      have p10110_1 := h10110c.2.1
                                      have p10110_2 := h10110c.2.2.1
                                      have p10110_3 := h10110c.2.2.2
                                      linarith only [h10071, hlam, p10110_0]
                                    · have p10110_0 := h10110c.1
                                      have p10110_1 := h10110c.2.1
                                      have p10110_2 := h10110c.2.2.1
                                      have p10110_3 := h10110c.2.2.2
                                      linarith only [hlam, p10110_0]
                          · linarith only [h10101, hlam, p10072_0]
                        · have p10072_0 := h10072c.1
                          have p10072_1 := h10072c.2.1
                          have p10072_2 := h10072c.2.2.1
                          have p10072_3 := h10072c.2.2.2
                          linarith only [h0, hlam, p10072_0]
                        · have p10072_0 := h10072c.1
                          have p10072_1 := h10072c.2.1
                          have p10072_2 := h10072c.2.2.1
                          have p10072_3 := h10072c.2.2.2
                          linarith only [hlam, p10072_0]
                        · have p10072_0 := h10072c.1
                          have p10072_1 := h10072c.2.1
                          have p10072_2 := h10072c.2.2.1
                          have p10072_3 := h10072c.2.2.2
                          linarith only [h9958, hlam, p10072_0]
                        · have p10072_0 := h10072c.1
                          have p10072_1 := h10072c.2.1
                          have p10072_2 := h10072c.2.2.1
                          have p10072_3 := h10072c.2.2.2
                          linarith only [h9960, hlam, p10072_0]
                        · have p10072_0 := h10072c.1
                          have p10072_1 := h10072c.2.1
                          have p10072_2 := h10072c.2.2.1
                          have p10072_3 := h10072c.2.2.2
                          linarith only [h9962, hlam, p10072_0]
                        · have p10072_0 := h10072c.1
                          have p10072_1 := h10072c.2.1
                          have p10072_2 := h10072c.2.2.1
                          have p10072_3 := h10072c.2.2.2
                          linarith only [h1, hlam, p10072_0]
                        · have p10072_0 := h10072c.1
                          have p10072_1 := h10072c.2.1
                          have p10072_2 := h10072c.2.2.1
                          have p10072_3 := h10072c.2.2.2
                          linarith only [h10070, h2, h9578, h9968, h9974, hc12, hc34, hlam, hphi, ht23, p10072_1]
                        · have p10072_0 := h10072c.1
                          have p10072_1 := h10072c.2.1
                          have p10072_2 := h10072c.2.2.1
                          have p10072_3 := h10072c.2.2.2
                          linarith only [hlam, p10072_0]
                        · have p10072_0 := h10072c.1
                          have p10072_1 := h10072c.2.1
                          have p10072_2 := h10072c.2.2.1
                          have p10072_3 := h10072c.2.2.2
                          linarith only [h9968, hlam, p10072_1]
                        · have p10072_0 := h10072c.1
                          have p10072_1 := h10072c.2.1
                          have p10072_2 := h10072c.2.2.1
                          have p10072_3 := h10072c.2.2.2
                          linarith only [h9970, hlam, p10072_1]
                        · have p10072_0 := h10072c.1
                          have p10072_1 := h10072c.2.1
                          have p10072_2 := h10072c.2.2.1
                          have p10072_3 := h10072c.2.2.2
                          linarith only [h2, hlam, p10072_0]
                        · have p10072_0 := h10072c.1
                          have p10072_1 := h10072c.2.1
                          have p10072_2 := h10072c.2.2.1
                          have p10072_3 := h10072c.2.2.2
                          linarith only [h10070, h2, h9578, h9974, hc12, hc34, hlam, hphi, ht23, p10072_1]
                        · have p10072_0 := h10072c.1
                          have p10072_1 := h10072c.2.1
                          have p10072_2 := h10072c.2.2.1
                          have p10072_3 := h10072c.2.2.2
                          linarith only [h10070, h2, h9578, h9974, hc13, hc34, hlam, hphi, p10072_1]
                        · have p10072_0 := h10072c.1
                          have p10072_1 := h10072c.2.1
                          have p10072_2 := h10072c.2.2.1
                          have p10072_3 := h10072c.2.2.2
                          linarith only [hlam, p10072_0]
                        · have p10072_0 := h10072c.1
                          have p10072_1 := h10072c.2.1
                          have p10072_2 := h10072c.2.2.1
                          have p10072_3 := h10072c.2.2.2
                          linarith only [h9972, hlam, p10072_1]
                        · have p10072_0 := h10072c.1
                          have p10072_1 := h10072c.2.1
                          have p10072_2 := h10072c.2.2.1
                          have p10072_3 := h10072c.2.2.2
                          linarith only [h3, hlam, p10072_0]
                        · have p10072_0 := h10072c.1
                          have p10072_1 := h10072c.2.1
                          have p10072_2 := h10072c.2.2.1
                          have p10072_3 := h10072c.2.2.2
                          linarith only [h10070, h3, h9578, h9974, hc12, hc34, hlam, hphi, ht23, p10072_1]
                        · have p10072_0 := h10072c.1
                          have p10072_1 := h10072c.2.1
                          have p10072_2 := h10072c.2.2.1
                          have p10072_3 := h10072c.2.2.2
                          linarith only [h10070, h3, h9578, h9958, h9974, hc12, hc34, hlam, hphi, ht23, p10072_1]
                        · have p10072_0 := h10072c.1
                          have p10072_1 := h10072c.2.1
                          have p10072_2 := h10072c.2.2.1
                          have p10072_3 := h10072c.2.2.2
                          linarith only [h10070, h3, h9578, h9960, h9974, hc12, hc34, hlam, hphi, ht23, p10072_1]
                        · have p10072_0 := h10072c.1
                          have p10072_1 := h10072c.2.1
                          have p10072_2 := h10072c.2.2.1
                          have p10072_3 := h10072c.2.2.2
                          linarith only [hlam, p10072_0]
                      · linarith only [h10070, h10071, h9974, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h10158 | h10158
                      · linarith only [h0, h10070, h10158, h4, h9974, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h10158, h4, h9974, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5858000 in
set_option maxHeartbeats 5858000 in
theorem r1l7_11_23_L_I_H_I_s10_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg6364 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h7232 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h6364 := hg6364
  rcases m.htr 0 3 5 (by decide) (by decide) with h9180 | h9180
  · exact r1l7_11_23_L_I_H_I_s10_x1_x0 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg6364 h7232 h9180
  · exact r1l7_11_23_L_I_H_I_s10_x1_x1 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg6364 h7232 h9180

set_option maxHeartbeats 5858000 in
set_option maxHeartbeats 5858000 in
theorem r1l7_11_23_L_I_H_I_s10 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg6364 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h6364 := hg6364
  rcases m.htr 0 3 4 (by decide) (by decide) with h7232 | h7232
  · exact r1l7_11_23_L_I_H_I_s10_x0 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg6364 h7232
  · exact r1l7_11_23_L_I_H_I_s10_x1 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg6364 h7232

end R2N4
