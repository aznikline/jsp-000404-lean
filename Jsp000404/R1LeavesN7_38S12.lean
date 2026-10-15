import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_38S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7262000 in
set_option maxHeartbeats 7262000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h528 | h528
  · rcases m.htr 0 4 5 (by decide) (by decide) with h529 | h529
    · rcases m.htr 1 2 3 (by decide) (by decide) with h530 | h530
      · rcases m.htr 1 2 4 (by decide) (by decide) with h531 | h531
        · rcases m.htr 1 2 5 (by decide) (by decide) with h532 | h532
          · rcases m.htr 1 3 5 (by decide) (by decide) with h533 | h533
            · rcases m.htr 1 4 5 (by decide) (by decide) with h534 | h534
              · rcases m.htr 2 3 4 (by decide) (by decide) with h535 | h535
                · linarith only [h1, h530, h535, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h537 | h537
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h538 | h538
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h539 | h539
                      · rcases h0bigk with h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c
                        · have p540_0 := h540c.1
                          have p540_1 := h540c.2.1
                          have p540_2 := h540c.2.2.1
                          have p540_3 := h540c.2.2.2
                          linarith only [hlam, p540_0]
                        · have p540_0 := h540c.1
                          have p540_1 := h540c.2.1
                          have p540_2 := h540c.2.2.1
                          have p540_3 := h540c.2.2.2
                          linarith only [h0, h531, h535, h537, h539, hc01, hc45, hlam, hphi, ht0b, ht5b, p540_1]
                        · have p540_0 := h540c.1
                          have p540_1 := h540c.2.1
                          have p540_2 := h540c.2.2.1
                          have p540_3 := h540c.2.2.2
                          linarith only [h1, h530, h537, h539, hc01, hc45, hlam, hphi, ht0b, ht5b, p540_1]
                        · have p540_0 := h540c.1
                          have p540_1 := h540c.2.1
                          have p540_2 := h540c.2.2.1
                          have p540_3 := h540c.2.2.2
                          linarith only [h1, h530, h537, h539, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p540_1]
                        · have p540_0 := h540c.1
                          have p540_1 := h540c.2.1
                          have p540_2 := h540c.2.2.1
                          have p540_3 := h540c.2.2.2
                          rcases p540_3 (m.d 0 1) (by simp) with h545 | h545
                          · rcases p540_3 (m.d 0 2) (by simp) with h546 | h546
                            · linarith only [h0, h546, hlam]
                            · linarith only [h546, h6, hlam]
                          · linarith only [h3, h545, hlam]
                        · have p540_0 := h540c.1
                          have p540_1 := h540c.2.1
                          have p540_2 := h540c.2.2.1
                          have p540_3 := h540c.2.2.2
                          linarith only [h0, hlam, p540_0]
                        · have p540_0 := h540c.1
                          have p540_1 := h540c.2.1
                          have p540_2 := h540c.2.2.1
                          have p540_3 := h540c.2.2.2
                          linarith only [hlam, p540_0]
                        · have p540_0 := h540c.1
                          have p540_1 := h540c.2.1
                          have p540_2 := h540c.2.2.1
                          have p540_3 := h540c.2.2.2
                          linarith only [h1, h530, h537, h539, hc02, hc45, hlam, hphi, ht0b, ht5b, p540_1]
                        · have p540_0 := h540c.1
                          have p540_1 := h540c.2.1
                          have p540_2 := h540c.2.2.1
                          have p540_3 := h540c.2.2.2
                          linarith only [h0, h1, h530, h537, h539, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p540_1]
                        · have p540_0 := h540c.1
                          have p540_1 := h540c.2.1
                          have p540_2 := h540c.2.2.1
                          have p540_3 := h540c.2.2.2
                          rcases p540_3 (m.d 0 1) (by simp) with h554 | h554
                          · rcases p540_3 (m.d 0 2) (by simp) with h555 | h555
                            · rcases p540_3 (m.d 0 3) (by simp) with h556 | h556
                              · linarith only [h4, h556, hlam]
                              · linarith only [h528, h556, hlam]
                            · linarith only [h555, h6, hlam]
                          · linarith only [h3, h554, hlam]
                        · have p540_0 := h540c.1
                          have p540_1 := h540c.2.1
                          have p540_2 := h540c.2.2.1
                          have p540_3 := h540c.2.2.2
                          linarith only [h1, hlam, p540_1]
                        · have p540_0 := h540c.1
                          have p540_1 := h540c.2.1
                          have p540_2 := h540c.2.2.1
                          have p540_3 := h540c.2.2.2
                          linarith only [h4, hlam, p540_1]
                        · have p540_0 := h540c.1
                          have p540_1 := h540c.2.1
                          have p540_2 := h540c.2.2.1
                          have p540_3 := h540c.2.2.2
                          linarith only [hlam, p540_0]
                        · have p540_0 := h540c.1
                          have p540_1 := h540c.2.1
                          have p540_2 := h540c.2.2.1
                          have p540_3 := h540c.2.2.2
                          linarith only [h7, hlam, p540_1]
                        · have p540_0 := h540c.1
                          have p540_1 := h540c.2.1
                          have p540_2 := h540c.2.2.1
                          have p540_3 := h540c.2.2.2
                          linarith only [h3, h532, h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p540_1, u3elo3]
                        · have p540_0 := h540c.1
                          have p540_1 := h540c.2.1
                          have p540_2 := h540c.2.2.1
                          have p540_3 := h540c.2.2.2
                          linarith only [h2, hlam, p540_0]
                        · have p540_0 := h540c.1
                          have p540_1 := h540c.2.1
                          have p540_2 := h540c.2.2.1
                          have p540_3 := h540c.2.2.2
                          linarith only [h5, hlam, p540_0]
                        · have p540_0 := h540c.1
                          have p540_1 := h540c.2.1
                          have p540_2 := h540c.2.2.1
                          have p540_3 := h540c.2.2.2
                          linarith only [h2, h4, h537, hc01, hc35, hlam, hphi, ht0b, ht5b, p540_1]
                        · have p540_0 := h540c.1
                          have p540_1 := h540c.2.1
                          have p540_2 := h540c.2.2.1
                          have p540_3 := h540c.2.2.2
                          linarith only [hlam, p540_0]
                        · have p540_0 := h540c.1
                          have p540_1 := h540c.2.1
                          have p540_2 := h540c.2.2.1
                          have p540_3 := h540c.2.2.2
                          linarith only [h3, h532, h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p540_1, u3elo3]
                        · have p540_0 := h540c.1
                          have p540_1 := h540c.2.1
                          have p540_2 := h540c.2.2.1
                          have p540_3 := h540c.2.2.2
                          linarith only [h3, hlam, p540_0]
                        · have p540_0 := h540c.1
                          have p540_1 := h540c.2.1
                          have p540_2 := h540c.2.2.1
                          have p540_3 := h540c.2.2.2
                          linarith only [h6, hlam, p540_1]
                        · have p540_0 := h540c.1
                          have p540_1 := h540c.2.1
                          have p540_2 := h540c.2.2.1
                          have p540_3 := h540c.2.2.2
                          linarith only [h528, hlam, p540_0]
                        · have p540_0 := h540c.1
                          have p540_1 := h540c.2.1
                          have p540_2 := h540c.2.2.1
                          have p540_3 := h540c.2.2.2
                          linarith only [h529, hlam, p540_1]
                        · have p540_0 := h540c.1
                          have p540_1 := h540c.2.1
                          have p540_2 := h540c.2.2.1
                          have p540_3 := h540c.2.2.2
                          linarith only [hlam, p540_0]
                      · linarith only [h529, h539, h7, hlam]
                    · linarith only [h3, h528, h534, h535, h538, h7, hc23, hlam, hphi, u3elo3]
                  · linarith only [h528, h537, h7, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h579 | h579
                · linarith only [h528, h529, h531, h534, h579, h7, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · linarith only [h528, h529, h531, h534, h579, h7, hc23, hlam, hphi, u3elo3]
            · linarith only [h528, h533, h7, hc13, hlam, hphi, u3elo3]
          · linarith only [h528, h532, h6, h7, hc12, hlam, hphi, ht23, u3elo3]
        · linarith only [h5, h530, h531, h7, hc23, hlam, hphi, u3elo3]
      · linarith only [h4, h530, h7, hc12, hlam, hphi, ht23, u3elo3]
    · linarith only [h528, h529, h7, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h587 | h587
    · rcases m.htr 1 2 3 (by decide) (by decide) with h588 | h588
      · rcases m.htr 1 2 4 (by decide) (by decide) with h589 | h589
        · rcases m.htr 1 2 5 (by decide) (by decide) with h590 | h590
          · rcases m.htr 1 3 5 (by decide) (by decide) with h591 | h591
            · linarith only [h1, h528, h591, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h593 | h593
              · rcases m.htr 2 3 4 (by decide) (by decide) with h594 | h594
                · linarith only [h1, h588, h594, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h596 | h596
                  · linarith only [h1, h528, h588, h596, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h598 | h598
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h599 | h599
                      · rcases h0bigk with h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [hlam, p600_0]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [h0, h589, h596, h598, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p600_1]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          rcases p600_3 (m.d 0 1) (by simp) with h603 | h603
                          · rcases p600_3 (m.d 0 2) (by simp) with h604 | h604
                            · linarith only [h0, h604, hlam]
                            · linarith only [h4, h604, hlam]
                          · linarith only [h1, h603, hlam]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [h2, h589, h598, hc01, hc45, hlam, hphi, ht0b, ht5b, p600_1]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          rcases p600_3 (m.d 0 1) (by simp) with h609 | h609
                          · rcases p600_3 (m.d 0 2) (by simp) with h610 | h610
                            · linarith only [h0, h610, hlam]
                            · linarith only [h6, h610, hlam]
                          · linarith only [h3, h609, hlam]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [h0, hlam, p600_0]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [hlam, p600_0]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          rcases p600_3 (m.d 0 1) (by simp) with h616 | h616
                          · rcases p600_3 (m.d 0 2) (by simp) with h617 | h617
                            · rcases p600_3 (m.d 0 3) (by simp) with h618 | h618
                              · linarith only [h4, h618, hlam]
                              · rcases p600_3 (m.d 0 4) (by simp) with h620 | h620
                                · linarith only [h5, h620, hlam]
                                · linarith only [h620, h7, hlam]
                            · linarith only [h4, h617, hlam]
                          · linarith only [h1, h616, hlam]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [h2, h589, h598, hc02, hc45, hlam, hphi, ht0b, ht5b, p600_1]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          rcases p600_3 (m.d 0 1) (by simp) with h626 | h626
                          · rcases p600_3 (m.d 0 2) (by simp) with h627 | h627
                            · rcases p600_3 (m.d 0 3) (by simp) with h628 | h628
                              · linarith only [h4, h628, hlam]
                              · rcases p600_3 (m.d 0 4) (by simp) with h630 | h630
                                · linarith only [h5, h630, hlam]
                                · linarith only [h587, h630, hlam]
                            · linarith only [h6, h627, hlam]
                          · linarith only [h3, h626, hlam]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [h1, hlam, p600_1]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [h4, hlam, p600_1]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [hlam, p600_0]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [h7, hlam, p600_1]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [h528, hlam, p600_1]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [h2, hlam, p600_0]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [h5, hlam, p600_0]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [h7, hc03, hlam, hphi, p600_1, u3elo3]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [hlam, p600_0]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [h1, h528, h7, hc13, hlam, hphi, p600_1, u3elo3]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [h3, hlam, p600_0]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [h6, hlam, p600_1]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [h1, h528, h599, hc13, hlam, hphi, p600_1, u3elo3]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [h587, hlam, p600_1]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [hlam, p600_0]
                      · linarith only [h0, h589, h598, h599, h7, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h2, h593, h594, h598, h7, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h652 | h652
                · linarith only [h1, h588, h652, h7, hlam]
                · linarith only [h587, h589, h593, h652, h7, hc23, hlam, hphi, u3elo3]
          · linarith only [h528, h588, h590, h6, hc23, hlam, hphi, u3elo4]
        · linarith only [h5, h588, h589, h7, hc23, hlam, hphi, u3elo3]
      · linarith only [h4, h588, h7, hc12, hlam, hphi, ht23, u3elo3]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h658 | h658
      · rcases m.htr 1 2 4 (by decide) (by decide) with h659 | h659
        · rcases m.htr 1 2 5 (by decide) (by decide) with h660 | h660
          · rcases m.htr 1 3 5 (by decide) (by decide) with h661 | h661
            · linarith only [h1, h528, h587, h661, h7, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h663 | h663
              · linarith only [h2, h587, h663, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h665 | h665
                · linarith only [h1, h658, h665, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h667 | h667
                  · linarith only [h1, h528, h658, h667, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h669 | h669
                    · linarith only [h0, h1, h587, h658, h659, h669, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h671 | h671
                      · linarith only [h1, h587, h658, h671, h7, hc23, hlam, hphi, u3elo3]
                      · rcases h0bigk with h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [hlam, p673_0]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p673_1]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          rcases p673_3 (m.d 0 1) (by simp) with h676 | h676
                          · rcases p673_3 (m.d 0 2) (by simp) with h677 | h677
                            · linarith only [h0, h677, hlam]
                            · linarith only [h4, h677, hlam]
                          · linarith only [h1, h676, hlam]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          rcases p673_3 (m.d 0 1) (by simp) with h681 | h681
                          · rcases p673_3 (m.d 0 2) (by simp) with h682 | h682
                            · linarith only [h0, h682, hlam]
                            · linarith only [h5, h682, hlam]
                          · linarith only [h2, h681, hlam]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          rcases p673_3 (m.d 0 1) (by simp) with h686 | h686
                          · rcases p673_3 (m.d 0 2) (by simp) with h687 | h687
                            · linarith only [h0, h687, hlam]
                            · linarith only [h6, h687, hlam]
                          · linarith only [h3, h686, hlam]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [h0, hlam, p673_0]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [hlam, p673_0]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          rcases p673_3 (m.d 0 1) (by simp) with h693 | h693
                          · rcases p673_3 (m.d 0 2) (by simp) with h694 | h694
                            · rcases p673_3 (m.d 0 3) (by simp) with h695 | h695
                              · linarith only [h4, h695, hlam]
                              · rcases p673_3 (m.d 0 4) (by simp) with h697 | h697
                                · linarith only [h5, h697, hlam]
                                · linarith only [h697, h7, hlam]
                            · linarith only [h4, h694, hlam]
                          · linarith only [h1, h693, hlam]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          rcases p673_3 (m.d 0 1) (by simp) with h702 | h702
                          · rcases p673_3 (m.d 0 2) (by simp) with h703 | h703
                            · rcases p673_3 (m.d 0 3) (by simp) with h704 | h704
                              · linarith only [h4, h704, hlam]
                              · rcases p673_3 (m.d 0 4) (by simp) with h706 | h706
                                · linarith only [h5, h706, hlam]
                                · rcases p673_3 (m.d 0 5) (by simp) with h708 | h708
                                  · linarith only [h6, h708, hlam]
                                  · linarith only [h587, h708, hlam]
                            · linarith only [h5, h703, hlam]
                          · linarith only [h2, h702, hlam]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          rcases p673_3 (m.d 0 1) (by simp) with h713 | h713
                          · rcases p673_3 (m.d 0 2) (by simp) with h714 | h714
                            · rcases p673_3 (m.d 0 3) (by simp) with h715 | h715
                              · linarith only [h4, h715, hlam]
                              · rcases p673_3 (m.d 0 4) (by simp) with h717 | h717
                                · linarith only [h5, h717, hlam]
                                · rcases p673_3 (m.d 0 5) (by simp) with h719 | h719
                                  · linarith only [h6, h719, hlam]
                                  · rcases h2bigk with h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c
                                    · have p721_0 := h721c.1
                                      have p721_1 := h721c.2.1
                                      have p721_2 := h721c.2.2.1
                                      have p721_3 := h721c.2.2.2
                                      linarith only [hlam, p721_0]
                                    · have p721_0 := h721c.1
                                      have p721_1 := h721c.2.1
                                      have p721_2 := h721c.2.2.1
                                      have p721_3 := h721c.2.2.2
                                      rcases p721_3 (m.d 0 2) (by simp) with h723 | h723
                                      · rcases p721_3 (m.d 1 2) (by simp) with h724 | h724
                                        · linarith only [h0, h724, hlam]
                                        · rcases p721_3 (m.d 2 3) (by simp) with h726 | h726
                                          · linarith only [h4, h726, hlam]
                                          · rcases p721_3 (m.d 2 4) (by simp) with h728 | h728
                                            · linarith only [h5, h728, hlam]
                                            · rcases p721_3 (m.d 2 5) (by simp) with h730 | h730
                                              · linarith only [h6, h730, hlam]
                                              · rcases h2emin with h732 | h732 | h732 | h732 | h732
                                                · rcases h5bigk with h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c
                                                  · have p733_0 := h733c.1
                                                    have p733_1 := h733c.2.1
                                                    have p733_2 := h733c.2.2.1
                                                    have p733_3 := h733c.2.2.2
                                                    linarith only [hlam, p733_0]
                                                  · have p733_0 := h733c.1
                                                    have p733_1 := h733c.2.1
                                                    have p733_2 := h733c.2.2.1
                                                    have p733_3 := h733c.2.2.2
                                                    linarith only [hc02, hc15, hlam, hphi, ht0b, ht5b, p673_1, p733_1]
                                                  · have p733_0 := h733c.1
                                                    have p733_1 := h733c.2.1
                                                    have p733_2 := h733c.2.2.1
                                                    have p733_3 := h733c.2.2.2
                                                    linarith only [h0, h665, h669, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p673_1, p733_1]
                                                  · have p733_0 := h733c.1
                                                    have p733_1 := h733c.2.1
                                                    have p733_2 := h733c.2.2.1
                                                    have p733_3 := h733c.2.2.2
                                                    linarith only [h528, hlam, p733_1]
                                                  · have p733_0 := h733c.1
                                                    have p733_1 := h733c.2.1
                                                    have p733_2 := h733c.2.2.1
                                                    have p733_3 := h733c.2.2.2
                                                    linarith only [h587, hlam, p733_1]
                                                  · have p733_0 := h733c.1
                                                    have p733_1 := h733c.2.1
                                                    have p733_2 := h733c.2.2.1
                                                    have p733_3 := h733c.2.2.2
                                                    linarith only [h3, hlam, p733_0]
                                                  · have p733_0 := h733c.1
                                                    have p733_1 := h733c.2.1
                                                    have p733_2 := h733c.2.2.1
                                                    have p733_3 := h733c.2.2.2
                                                    linarith only [hlam, p733_0]
                                                  · have p733_0 := h733c.1
                                                    have p733_1 := h733c.2.1
                                                    have p733_2 := h733c.2.2.1
                                                    have p733_3 := h733c.2.2.2
                                                    linarith only [h0, h3, h665, h669, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p673_1, p733_1]
                                                  · have p733_0 := h733c.1
                                                    have p733_1 := h733c.2.1
                                                    have p733_2 := h733c.2.2.1
                                                    have p733_3 := h733c.2.2.2
                                                    linarith only [h661, hlam, p733_1]
                                                  · have p733_0 := h733c.1
                                                    have p733_1 := h733c.2.1
                                                    have p733_2 := h733c.2.2.1
                                                    have p733_3 := h733c.2.2.2
                                                    linarith only [h663, hlam, p733_1]
                                                  · have p733_0 := h733c.1
                                                    have p733_1 := h733c.2.1
                                                    have p733_2 := h733c.2.2.1
                                                    have p733_3 := h733c.2.2.2
                                                    linarith only [h6, hlam, p733_1]
                                                  · have p733_0 := h733c.1
                                                    have p733_1 := h733c.2.1
                                                    have p733_2 := h733c.2.2.1
                                                    have p733_3 := h733c.2.2.2
                                                    linarith only [h660, hlam, p733_1]
                                                  · have p733_0 := h733c.1
                                                    have p733_1 := h733c.2.1
                                                    have p733_2 := h733c.2.2.1
                                                    have p733_3 := h733c.2.2.2
                                                    linarith only [hlam, p733_0]
                                                  · have p733_0 := h733c.1
                                                    have p733_1 := h733c.2.1
                                                    have p733_2 := h733c.2.2.1
                                                    have p733_3 := h733c.2.2.2
                                                    linarith only [h667, hlam, p733_1]
                                                  · have p733_0 := h733c.1
                                                    have p733_1 := h733c.2.1
                                                    have p733_2 := h733c.2.2.1
                                                    have p733_3 := h733c.2.2.2
                                                    linarith only [h669, hlam, p733_1]
                                                  · have p733_0 := h733c.1
                                                    have p733_1 := h733c.2.1
                                                    have p733_2 := h733c.2.2.1
                                                    have p733_3 := h733c.2.2.2
                                                    linarith only [h6, h665, h669, hc23, hlam, hphi, p733_1, u3elo4]
                                                  · have p733_0 := h733c.1
                                                    have p733_1 := h733c.2.1
                                                    have p733_2 := h733c.2.2.1
                                                    have p733_3 := h733c.2.2.2
                                                    linarith only [h660, h665, h669, hc23, hlam, hphi, p733_1, u3elo4]
                                                  · have p733_0 := h733c.1
                                                    have p733_1 := h733c.2.1
                                                    have p733_2 := h733c.2.2.1
                                                    have p733_3 := h733c.2.2.2
                                                    linarith only [h665, h669, hc23, hlam, hphi, p733_1, u3elo4]
                                                  · have p733_0 := h733c.1
                                                    have p733_1 := h733c.2.1
                                                    have p733_2 := h733c.2.2.1
                                                    have p733_3 := h733c.2.2.2
                                                    linarith only [hlam, p733_0]
                                                  · have p733_0 := h733c.1
                                                    have p733_1 := h733c.2.1
                                                    have p733_2 := h733c.2.2.1
                                                    have p733_3 := h733c.2.2.2
                                                    linarith only [h671, hlam, p733_1]
                                                  · have p733_0 := h733c.1
                                                    have p733_1 := h733c.2.1
                                                    have p733_2 := h733c.2.2.1
                                                    have p733_3 := h733c.2.2.2
                                                    rcases p733_3 (m.d 0 5) (by simp) with h754 | h754
                                                    · linarith only [h587, h754, hlam]
                                                    · rcases p733_3 (m.d 1 5) (by simp) with h756 | h756
                                                      · linarith only [h663, h756, hlam]
                                                      · rcases p733_3 (m.d 2 5) (by simp) with h758 | h758
                                                        · linarith only [h669, h758, hlam]
                                                        · rcases p733_3 (m.d 3 5) (by simp) with h760 | h760
                                                          · linarith only [h671, h760, hlam]
                                                          · linarith only [h528, h760, hlam]
                                                  · have p733_0 := h733c.1
                                                    have p733_1 := h733c.2.1
                                                    have p733_2 := h733c.2.2.1
                                                    have p733_3 := h733c.2.2.2
                                                    rcases p733_3 (m.d 0 5) (by simp) with h763 | h763
                                                    · linarith only [h587, h763, hlam]
                                                    · linarith only [h3, h763, hlam]
                                                  · have p733_0 := h733c.1
                                                    have p733_1 := h733c.2.1
                                                    have p733_2 := h733c.2.2.1
                                                    have p733_3 := h733c.2.2.2
                                                    rcases p733_3 (m.d 0 5) (by simp) with h766 | h766
                                                    · linarith only [h587, h766, hlam]
                                                    · linarith only [h6, h766, hlam]
                                                  · have p733_0 := h733c.1
                                                    have p733_1 := h733c.2.1
                                                    have p733_2 := h733c.2.2.1
                                                    have p733_3 := h733c.2.2.2
                                                    linarith only [h1, h528, h658, hc23, hc45, hlam, hphi, ht34, p733_1]
                                                  · have p733_0 := h733c.1
                                                    have p733_1 := h733c.2.1
                                                    have p733_2 := h733c.2.2.1
                                                    have p733_3 := h733c.2.2.2
                                                    linarith only [hlam, p733_0]
                                                · linarith only [h0, h732, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p721_1]
                                                · linarith only [h1, h658, h7, h732, hlam, ht23, u3elo3]
                                                · linarith only [h0, h3, h660, h669, h732, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p673_1]
                                                · linarith only [h0, h3, h660, h732, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p673_1]
                                      · linarith only [h0, h723, hlam]
                                    · have p721_0 := h721c.1
                                      have p721_1 := h721c.2.1
                                      have p721_2 := h721c.2.2.1
                                      have p721_3 := h721c.2.2.2
                                      linarith only [h1, h528, h658, hlam, p673_1, p721_2]
                                    · have p721_0 := h721c.1
                                      have p721_1 := h721c.2.1
                                      have p721_2 := h721c.2.2.1
                                      have p721_3 := h721c.2.2.2
                                      linarith only [h3, h660, h669, hlam, p673_1, p721_2]
                                    · have p721_0 := h721c.1
                                      have p721_1 := h721c.2.1
                                      have p721_2 := h721c.2.2.1
                                      have p721_3 := h721c.2.2.2
                                      linarith only [h3, h660, hlam, p673_1, p721_2]
                                    · have p721_0 := h721c.1
                                      have p721_1 := h721c.2.1
                                      have p721_2 := h721c.2.2.1
                                      have p721_3 := h721c.2.2.2
                                      linarith only [h0, hlam, p721_0]
                                    · have p721_0 := h721c.1
                                      have p721_1 := h721c.2.1
                                      have p721_2 := h721c.2.2.1
                                      have p721_3 := h721c.2.2.2
                                      linarith only [hlam, p721_0]
                                    · have p721_0 := h721c.1
                                      have p721_1 := h721c.2.1
                                      have p721_2 := h721c.2.2.1
                                      have p721_3 := h721c.2.2.2
                                      rcases p721_3 (m.d 0 2) (by simp) with h781 | h781
                                      · rcases p721_3 (m.d 1 2) (by simp) with h782 | h782
                                        · rcases p721_3 (m.d 2 3) (by simp) with h783 | h783
                                          · linarith only [h783, hlam, p721_0]
                                          · rcases p721_3 (m.d 2 4) (by simp) with h785 | h785
                                            · linarith only [h659, h785, hlam]
                                            · linarith only [h665, h785, hlam]
                                        · linarith only [h782, hlam, p721_0]
                                      · linarith only [h4, h781, hlam]
                                    · have p721_0 := h721c.1
                                      have p721_1 := h721c.2.1
                                      have p721_2 := h721c.2.2.1
                                      have p721_3 := h721c.2.2.2
                                      rcases p721_3 (m.d 0 2) (by simp) with h790 | h790
                                      · rcases p721_3 (m.d 1 2) (by simp) with h791 | h791
                                        · rcases p721_3 (m.d 2 3) (by simp) with h792 | h792
                                          · linarith only [h658, h792, hlam]
                                          · rcases p721_3 (m.d 2 4) (by simp) with h794 | h794
                                            · linarith only [h794, hlam, p721_0]
                                            · rcases p721_3 (m.d 2 5) (by simp) with h796 | h796
                                              · linarith only [h660, h796, hlam]
                                              · linarith only [h669, h796, hlam]
                                        · linarith only [h791, hlam, p721_0]
                                      · linarith only [h5, h790, hlam]
                                    · have p721_0 := h721c.1
                                      have p721_1 := h721c.2.1
                                      have p721_2 := h721c.2.2.1
                                      have p721_3 := h721c.2.2.2
                                      rcases p721_3 (m.d 0 2) (by simp) with h801 | h801
                                      · rcases p721_3 (m.d 1 2) (by simp) with h802 | h802
                                        · rcases p721_3 (m.d 2 3) (by simp) with h803 | h803
                                          · linarith only [h658, h803, hlam]
                                          · rcases p721_3 (m.d 2 4) (by simp) with h805 | h805
                                            · linarith only [h659, h805, hlam]
                                            · rcases p721_3 (m.d 2 5) (by simp) with h807 | h807
                                              · linarith only [h807, hlam, p721_0]
                                              · rcases h2emin with h809 | h809 | h809 | h809 | h809
                                                · rcases h5bigk with h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c
                                                  · have p810_0 := h810c.1
                                                    have p810_1 := h810c.2.1
                                                    have p810_2 := h810c.2.2.1
                                                    have p810_3 := h810c.2.2.2
                                                    linarith only [hlam, p810_0]
                                                  · have p810_0 := h810c.1
                                                    have p810_1 := h810c.2.1
                                                    have p810_2 := h810c.2.2.1
                                                    have p810_3 := h810c.2.2.2
                                                    linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p673_1, p810_1]
                                                  · have p810_0 := h810c.1
                                                    have p810_1 := h810c.2.1
                                                    have p810_2 := h810c.2.2.1
                                                    have p810_3 := h810c.2.2.2
                                                    linarith only [h0, h665, h669, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p673_1, p810_1]
                                                  · have p810_0 := h810c.1
                                                    have p810_1 := h810c.2.1
                                                    have p810_2 := h810c.2.2.1
                                                    have p810_3 := h810c.2.2.2
                                                    linarith only [h528, hlam, p810_1]
                                                  · have p810_0 := h810c.1
                                                    have p810_1 := h810c.2.1
                                                    have p810_2 := h810c.2.2.1
                                                    have p810_3 := h810c.2.2.2
                                                    linarith only [h587, hlam, p810_1]
                                                  · have p810_0 := h810c.1
                                                    have p810_1 := h810c.2.1
                                                    have p810_2 := h810c.2.2.1
                                                    have p810_3 := h810c.2.2.2
                                                    linarith only [h3, hlam, p810_0]
                                                  · have p810_0 := h810c.1
                                                    have p810_1 := h810c.2.1
                                                    have p810_2 := h810c.2.2.1
                                                    have p810_3 := h810c.2.2.2
                                                    linarith only [hlam, p810_0]
                                                  · have p810_0 := h810c.1
                                                    have p810_1 := h810c.2.1
                                                    have p810_2 := h810c.2.2.1
                                                    have p810_3 := h810c.2.2.2
                                                    linarith only [h0, h3, h665, h669, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p673_1, p810_1]
                                                  · have p810_0 := h810c.1
                                                    have p810_1 := h810c.2.1
                                                    have p810_2 := h810c.2.2.1
                                                    have p810_3 := h810c.2.2.2
                                                    linarith only [h661, hlam, p810_1]
                                                  · have p810_0 := h810c.1
                                                    have p810_1 := h810c.2.1
                                                    have p810_2 := h810c.2.2.1
                                                    have p810_3 := h810c.2.2.2
                                                    linarith only [h663, hlam, p810_1]
                                                  · have p810_0 := h810c.1
                                                    have p810_1 := h810c.2.1
                                                    have p810_2 := h810c.2.2.1
                                                    have p810_3 := h810c.2.2.2
                                                    linarith only [h6, hlam, p810_1]
                                                  · have p810_0 := h810c.1
                                                    have p810_1 := h810c.2.1
                                                    have p810_2 := h810c.2.2.1
                                                    have p810_3 := h810c.2.2.2
                                                    linarith only [h660, hlam, p810_1]
                                                  · have p810_0 := h810c.1
                                                    have p810_1 := h810c.2.1
                                                    have p810_2 := h810c.2.2.1
                                                    have p810_3 := h810c.2.2.2
                                                    linarith only [hlam, p810_0]
                                                  · have p810_0 := h810c.1
                                                    have p810_1 := h810c.2.1
                                                    have p810_2 := h810c.2.2.1
                                                    have p810_3 := h810c.2.2.2
                                                    linarith only [h667, hlam, p810_1]
                                                  · have p810_0 := h810c.1
                                                    have p810_1 := h810c.2.1
                                                    have p810_2 := h810c.2.2.1
                                                    have p810_3 := h810c.2.2.2
                                                    linarith only [h669, hlam, p810_1]
                                                  · have p810_0 := h810c.1
                                                    have p810_1 := h810c.2.1
                                                    have p810_2 := h810c.2.2.1
                                                    have p810_3 := h810c.2.2.2
                                                    linarith only [h587, h7, hc03, hlam, hphi, p810_1, u3elo4]
                                                  · have p810_0 := h810c.1
                                                    have p810_1 := h810c.2.1
                                                    have p810_2 := h810c.2.2.1
                                                    have p810_3 := h810c.2.2.2
                                                    linarith only [h660, h665, h669, hc23, hlam, hphi, p810_1, u3elo4]
                                                  · have p810_0 := h810c.1
                                                    have p810_1 := h810c.2.1
                                                    have p810_2 := h810c.2.2.1
                                                    have p810_3 := h810c.2.2.2
                                                    linarith only [h665, h669, hc23, hlam, hphi, p810_1, u3elo4]
                                                  · have p810_0 := h810c.1
                                                    have p810_1 := h810c.2.1
                                                    have p810_2 := h810c.2.2.1
                                                    have p810_3 := h810c.2.2.2
                                                    linarith only [hlam, p810_0]
                                                  · have p810_0 := h810c.1
                                                    have p810_1 := h810c.2.1
                                                    have p810_2 := h810c.2.2.1
                                                    have p810_3 := h810c.2.2.2
                                                    linarith only [h671, hlam, p810_1]
                                                  · have p810_0 := h810c.1
                                                    have p810_1 := h810c.2.1
                                                    have p810_2 := h810c.2.2.1
                                                    have p810_3 := h810c.2.2.2
                                                    rcases p810_3 (m.d 0 5) (by simp) with h831 | h831
                                                    · linarith only [h587, h831, hlam]
                                                    · rcases p810_3 (m.d 1 5) (by simp) with h833 | h833
                                                      · linarith only [h663, h833, hlam]
                                                      · rcases p810_3 (m.d 2 5) (by simp) with h835 | h835
                                                        · linarith only [h669, h835, hlam]
                                                        · rcases p810_3 (m.d 3 5) (by simp) with h837 | h837
                                                          · linarith only [h671, h837, hlam]
                                                          · linarith only [h528, h837, hlam]
                                                  · have p810_0 := h810c.1
                                                    have p810_1 := h810c.2.1
                                                    have p810_2 := h810c.2.2.1
                                                    have p810_3 := h810c.2.2.2
                                                    rcases p810_3 (m.d 0 5) (by simp) with h840 | h840
                                                    · linarith only [h587, h840, hlam]
                                                    · linarith only [h3, h840, hlam]
                                                  · have p810_0 := h810c.1
                                                    have p810_1 := h810c.2.1
                                                    have p810_2 := h810c.2.2.1
                                                    have p810_3 := h810c.2.2.2
                                                    rcases p810_3 (m.d 0 5) (by simp) with h843 | h843
                                                    · linarith only [h587, h843, hlam]
                                                    · linarith only [h6, h843, hlam]
                                                  · have p810_0 := h810c.1
                                                    have p810_1 := h810c.2.1
                                                    have p810_2 := h810c.2.2.1
                                                    have p810_3 := h810c.2.2.2
                                                    linarith only [h1, h658, h671, h7, hc23, hc45, hlam, hphi, ht34, p810_1]
                                                  · have p810_0 := h810c.1
                                                    have p810_1 := h810c.2.1
                                                    have p810_2 := h810c.2.2.1
                                                    have p810_3 := h810c.2.2.2
                                                    linarith only [hlam, p810_0]
                                                · rcases h5bigk with h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c
                                                  · have p848_0 := h848c.1
                                                    have p848_1 := h848c.2.1
                                                    have p848_2 := h848c.2.2.1
                                                    have p848_3 := h848c.2.2.2
                                                    linarith only [hlam, p848_0]
                                                  · have p848_0 := h848c.1
                                                    have p848_1 := h848c.2.1
                                                    have p848_2 := h848c.2.2.1
                                                    have p848_3 := h848c.2.2.2
                                                    linarith only [h0, h660, h665, h669, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p673_1, p848_1]
                                                  · have p848_0 := h848c.1
                                                    have p848_1 := h848c.2.1
                                                    have p848_2 := h848c.2.2.1
                                                    have p848_3 := h848c.2.2.2
                                                    linarith only [h0, h665, h669, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p673_1, p848_1]
                                                  · have p848_0 := h848c.1
                                                    have p848_1 := h848c.2.1
                                                    have p848_2 := h848c.2.2.1
                                                    have p848_3 := h848c.2.2.2
                                                    linarith only [h528, hlam, p848_1]
                                                  · have p848_0 := h848c.1
                                                    have p848_1 := h848c.2.1
                                                    have p848_2 := h848c.2.2.1
                                                    have p848_3 := h848c.2.2.2
                                                    linarith only [h587, hlam, p848_1]
                                                  · have p848_0 := h848c.1
                                                    have p848_1 := h848c.2.1
                                                    have p848_2 := h848c.2.2.1
                                                    have p848_3 := h848c.2.2.2
                                                    linarith only [h3, hlam, p848_0]
                                                  · have p848_0 := h848c.1
                                                    have p848_1 := h848c.2.1
                                                    have p848_2 := h848c.2.2.1
                                                    have p848_3 := h848c.2.2.2
                                                    linarith only [hlam, p848_0]
                                                  · have p848_0 := h848c.1
                                                    have p848_1 := h848c.2.1
                                                    have p848_2 := h848c.2.2.1
                                                    have p848_3 := h848c.2.2.2
                                                    linarith only [h0, h3, h665, h669, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p673_1, p848_1]
                                                  · have p848_0 := h848c.1
                                                    have p848_1 := h848c.2.1
                                                    have p848_2 := h848c.2.2.1
                                                    have p848_3 := h848c.2.2.2
                                                    linarith only [h661, hlam, p848_1]
                                                  · have p848_0 := h848c.1
                                                    have p848_1 := h848c.2.1
                                                    have p848_2 := h848c.2.2.1
                                                    have p848_3 := h848c.2.2.2
                                                    linarith only [h663, hlam, p848_1]
                                                  · have p848_0 := h848c.1
                                                    have p848_1 := h848c.2.1
                                                    have p848_2 := h848c.2.2.1
                                                    have p848_3 := h848c.2.2.2
                                                    linarith only [h6, hlam, p848_1]
                                                  · have p848_0 := h848c.1
                                                    have p848_1 := h848c.2.1
                                                    have p848_2 := h848c.2.2.1
                                                    have p848_3 := h848c.2.2.2
                                                    linarith only [h660, hlam, p848_1]
                                                  · have p848_0 := h848c.1
                                                    have p848_1 := h848c.2.1
                                                    have p848_2 := h848c.2.2.1
                                                    have p848_3 := h848c.2.2.2
                                                    linarith only [hlam, p848_0]
                                                  · have p848_0 := h848c.1
                                                    have p848_1 := h848c.2.1
                                                    have p848_2 := h848c.2.2.1
                                                    have p848_3 := h848c.2.2.2
                                                    linarith only [h667, hlam, p848_1]
                                                  · have p848_0 := h848c.1
                                                    have p848_1 := h848c.2.1
                                                    have p848_2 := h848c.2.2.1
                                                    have p848_3 := h848c.2.2.2
                                                    linarith only [h669, hlam, p848_1]
                                                  · have p848_0 := h848c.1
                                                    have p848_1 := h848c.2.1
                                                    have p848_2 := h848c.2.2.1
                                                    have p848_3 := h848c.2.2.2
                                                    linarith only [h6, h665, h669, hc23, hlam, hphi, p848_1, u3elo4]
                                                  · have p848_0 := h848c.1
                                                    have p848_1 := h848c.2.1
                                                    have p848_2 := h848c.2.2.1
                                                    have p848_3 := h848c.2.2.2
                                                    linarith only [h660, h665, h669, hc23, hlam, hphi, p848_1, u3elo4]
                                                  · have p848_0 := h848c.1
                                                    have p848_1 := h848c.2.1
                                                    have p848_2 := h848c.2.2.1
                                                    have p848_3 := h848c.2.2.2
                                                    linarith only [h665, h669, hc23, hlam, hphi, p848_1, u3elo4]
                                                  · have p848_0 := h848c.1
                                                    have p848_1 := h848c.2.1
                                                    have p848_2 := h848c.2.2.1
                                                    have p848_3 := h848c.2.2.2
                                                    linarith only [hlam, p848_0]
                                                  · have p848_0 := h848c.1
                                                    have p848_1 := h848c.2.1
                                                    have p848_2 := h848c.2.2.1
                                                    have p848_3 := h848c.2.2.2
                                                    linarith only [h671, hlam, p848_1]
                                                  · have p848_0 := h848c.1
                                                    have p848_1 := h848c.2.1
                                                    have p848_2 := h848c.2.2.1
                                                    have p848_3 := h848c.2.2.2
                                                    rcases p848_3 (m.d 0 5) (by simp) with h869 | h869
                                                    · linarith only [h587, h869, hlam]
                                                    · rcases p848_3 (m.d 1 5) (by simp) with h871 | h871
                                                      · linarith only [h663, h871, hlam]
                                                      · rcases p848_3 (m.d 2 5) (by simp) with h873 | h873
                                                        · linarith only [h669, h873, hlam]
                                                        · rcases p848_3 (m.d 3 5) (by simp) with h875 | h875
                                                          · linarith only [h671, h875, hlam]
                                                          · linarith only [h528, h875, hlam]
                                                  · have p848_0 := h848c.1
                                                    have p848_1 := h848c.2.1
                                                    have p848_2 := h848c.2.2.1
                                                    have p848_3 := h848c.2.2.2
                                                    rcases p848_3 (m.d 0 5) (by simp) with h878 | h878
                                                    · linarith only [h587, h878, hlam]
                                                    · linarith only [h3, h878, hlam]
                                                  · have p848_0 := h848c.1
                                                    have p848_1 := h848c.2.1
                                                    have p848_2 := h848c.2.2.1
                                                    have p848_3 := h848c.2.2.2
                                                    rcases p848_3 (m.d 0 5) (by simp) with h881 | h881
                                                    · linarith only [h587, h881, hlam]
                                                    · linarith only [h6, h881, hlam]
                                                  · have p848_0 := h848c.1
                                                    have p848_1 := h848c.2.1
                                                    have p848_2 := h848c.2.2.1
                                                    have p848_3 := h848c.2.2.2
                                                    linarith only [h1, h528, h658, hc23, hc45, hlam, hphi, ht34, p848_1]
                                                  · have p848_0 := h848c.1
                                                    have p848_1 := h848c.2.1
                                                    have p848_2 := h848c.2.2.1
                                                    have p848_3 := h848c.2.2.2
                                                    linarith only [hlam, p848_0]
                                                · linarith only [h665, h669, h809, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p721_1]
                                                · linarith only [h669, h809, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p721_1]
                                                · linarith only [h809, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p721_1]
                                        · linarith only [h802, hlam, p721_0]
                                      · linarith only [h6, h801, hlam]
                                    · have p721_0 := h721c.1
                                      have p721_1 := h721c.2.1
                                      have p721_2 := h721c.2.2.1
                                      have p721_3 := h721c.2.2.2
                                      linarith only [h4, hlam, p721_0]
                                    · have p721_0 := h721c.1
                                      have p721_1 := h721c.2.1
                                      have p721_2 := h721c.2.2.1
                                      have p721_3 := h721c.2.2.2
                                      linarith only [h658, hlam, p721_0]
                                    · have p721_0 := h721c.1
                                      have p721_1 := h721c.2.1
                                      have p721_2 := h721c.2.2.1
                                      have p721_3 := h721c.2.2.2
                                      linarith only [hlam, p721_0]
                                    · have p721_0 := h721c.1
                                      have p721_1 := h721c.2.1
                                      have p721_2 := h721c.2.2.1
                                      have p721_3 := h721c.2.2.2
                                      linarith only [h665, hlam, p721_0]
                                    · have p721_0 := h721c.1
                                      have p721_1 := h721c.2.1
                                      have p721_2 := h721c.2.2.1
                                      have p721_3 := h721c.2.2.2
                                      linarith only [h667, hlam, p721_0]
                                    · have p721_0 := h721c.1
                                      have p721_1 := h721c.2.1
                                      have p721_2 := h721c.2.2.1
                                      have p721_3 := h721c.2.2.2
                                      linarith only [h5, hlam, p721_0]
                                    · have p721_0 := h721c.1
                                      have p721_1 := h721c.2.1
                                      have p721_2 := h721c.2.2.1
                                      have p721_3 := h721c.2.2.2
                                      linarith only [h659, hlam, p721_0]
                                    · have p721_0 := h721c.1
                                      have p721_1 := h721c.2.1
                                      have p721_2 := h721c.2.2.1
                                      have p721_3 := h721c.2.2.2
                                      linarith only [h0, h3, h660, h669, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p673_1, p721_1]
                                    · have p721_0 := h721c.1
                                      have p721_1 := h721c.2.1
                                      have p721_2 := h721c.2.2.1
                                      have p721_3 := h721c.2.2.2
                                      linarith only [hlam, p721_0]
                                    · have p721_0 := h721c.1
                                      have p721_1 := h721c.2.1
                                      have p721_2 := h721c.2.2.1
                                      have p721_3 := h721c.2.2.2
                                      linarith only [h669, hlam, p721_1]
                                    · have p721_0 := h721c.1
                                      have p721_1 := h721c.2.1
                                      have p721_2 := h721c.2.2.1
                                      have p721_3 := h721c.2.2.2
                                      linarith only [h6, hlam, p721_0]
                                    · have p721_0 := h721c.1
                                      have p721_1 := h721c.2.1
                                      have p721_2 := h721c.2.2.1
                                      have p721_3 := h721c.2.2.2
                                      linarith only [h660, hlam, p721_0]
                                    · have p721_0 := h721c.1
                                      have p721_1 := h721c.2.1
                                      have p721_2 := h721c.2.2.1
                                      have p721_3 := h721c.2.2.2
                                      linarith only [h0, h3, h660, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p673_1, p721_1]
                                    · have p721_0 := h721c.1
                                      have p721_1 := h721c.2.1
                                      have p721_2 := h721c.2.2.1
                                      have p721_3 := h721c.2.2.2
                                      linarith only [h0, h3, h660, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p673_1, p721_1]
                                    · have p721_0 := h721c.1
                                      have p721_1 := h721c.2.1
                                      have p721_2 := h721c.2.2.1
                                      have p721_3 := h721c.2.2.2
                                      linarith only [hlam, p721_0]
                            · linarith only [h6, h714, hlam]
                          · linarith only [h3, h713, hlam]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [h1, hlam, p673_1]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [h4, hlam, p673_1]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [hlam, p673_0]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [h7, hlam, p673_1]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [h528, hlam, p673_1]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [h2, hlam, p673_0]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [h5, hlam, p673_0]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [h1, h658, h7, hc23, hlam, hphi, p673_1, u3elo3]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [hlam, p673_0]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [h587, hlam, p673_0]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [h3, hlam, p673_0]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [h6, hlam, p673_1]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [h1, h528, h658, hc23, hlam, hphi, p673_1, u3elo4]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [h528, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p673_1, u3elo4]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [hlam, p673_0]
          · linarith only [h528, h6, h658, h660, hc23, hlam, hphi, u3elo4]
        · linarith only [h5, h658, h659, h7, hc23, hlam, hphi, u3elo3]
      · linarith only [h4, h658, h7, hc12, hlam, hphi, ht23, u3elo3]

set_option maxHeartbeats 7262000 in
set_option maxHeartbeats 7262000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
  · exact r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4 h5 h6 h7
  · exact r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4 h5 h6 h7

set_option maxHeartbeats 7262000 in
set_option maxHeartbeats 7262000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h926 | h926
  · rcases m.htr 0 3 5 (by decide) (by decide) with h927 | h927
    · linarith only [h4, h6, h927, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h929 | h929
      · linarith only [h4, h6, h926, h929, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h931 | h931
        · rcases m.htr 1 2 4 (by decide) (by decide) with h932 | h932
          · rcases m.htr 1 2 5 (by decide) (by decide) with h933 | h933
            · linarith only [h0, h6, h933, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h935 | h935
              · linarith only [h1, h927, h935, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h937 | h937
                · linarith only [h2, h929, h937, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h939 | h939
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h940 | h940
                    · linarith only [h0, h1, h6, h927, h931, h940, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h0, h6, h931, h940, hc23, hlam, hphi, u3elo4]
                  · linarith only [h926, h927, h939, hc23, hlam, hphi, u3elo4]
          · linarith only [h5, h6, h931, h932, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
        · linarith only [h4, h927, h931, hc12, hlam, hphi, ht23, u3elo4]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h946 | h946
    · linarith only [h4, h6, h926, h946, hc23, hlam, hphi, u3elo3]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h948 | h948
      · linarith only [h5, h6, h948, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h950 | h950
        · rcases m.htr 1 2 4 (by decide) (by decide) with h951 | h951
          · rcases m.htr 1 2 5 (by decide) (by decide) with h952 | h952
            · linarith only [h0, h6, h952, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h954 | h954
              · linarith only [h946, h954, hc03, hlam, hphi, u3elo1]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h956 | h956
                · linarith only [h2, h948, h956, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h958 | h958
                  · linarith only [h1, h926, h950, h958, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h960 | h960
                    · linarith only [h0, h6, h946, h951, h958, h960, hlam]
                    · linarith only [h0, h6, h951, h958, h960, hc23, hlam, hphi, u3elo4]
          · linarith only [h5, h6, h950, h951, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
        · linarith only [h4, h6, h946, h950, hc12, hlam, hphi, ht23, u3elo4]

set_option maxHeartbeats 7262000 in
set_option maxHeartbeats 7262000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
  · exact r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4 h5 h6
  · exact r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4 h5 h6

set_option maxHeartbeats 7262000 in
set_option maxHeartbeats 7262000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h965 | h965
  · rcases m.htr 0 3 4 (by decide) (by decide) with h966 | h966
    · linarith only [h4, h5, h966, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h968 | h968
      · rcases m.htr 0 4 5 (by decide) (by decide) with h969 | h969
        · rcases m.htr 1 2 3 (by decide) (by decide) with h970 | h970
          · rcases m.htr 1 2 4 (by decide) (by decide) with h971 | h971
            · linarith only [h0, h5, h971, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h973 | h973
              · rcases m.htr 1 3 5 (by decide) (by decide) with h974 | h974
                · rcases m.htr 1 4 5 (by decide) (by decide) with h975 | h975
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h976 | h976
                    · linarith only [h0, h5, h966, h970, h976, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h4, h5, h976, hc23, hlam, hphi, u3elo3]
                  · linarith only [h966, h969, h970, h971, h975, hc23, hlam, hphi, u3elo3]
                · linarith only [h966, h968, h974, hc13, hlam, hphi, u3elo3]
              · linarith only [h5, h965, h970, h973, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · linarith only [h4, h5, h966, h970, hc12, hlam, hphi, ht23, u3elo3]
        · linarith only [h4, h5, h966, h968, h969, hc23, hlam, hphi, u3elo3]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h984 | h984
        · rcases m.htr 1 2 3 (by decide) (by decide) with h985 | h985
          · rcases m.htr 1 2 4 (by decide) (by decide) with h986 | h986
            · linarith only [h0, h5, h965, h986, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h988 | h988
              · rcases m.htr 1 3 5 (by decide) (by decide) with h989 | h989
                · linarith only [h968, h989, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h991 | h991
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h992 | h992
                    · linarith only [h0, h5, h966, h985, h992, hlam]
                    · linarith only [h0, h5, h985, h992, hc23, hlam, hphi, u3elo3]
                  · linarith only [h966, h984, h985, h986, h991, hc23, hlam, hphi, u3elo3]
              · linarith only [h5, h965, h985, h988, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · linarith only [h4, h5, h966, h985, hc12, hlam, hphi, ht23, u3elo3]
        · linarith only [h5, h965, h984, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h999 | h999
    · linarith only [h4, h5, h999, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1001 | h1001
      · linarith only [h1001, h4, h965, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1003 | h1003
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1004 | h1004
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1005 | h1005
            · linarith only [h0, h1005, h5, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1007 | h1007
              · linarith only [h0, h1007, h965, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1009 | h1009
                · linarith only [h1, h1001, h1009, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1011 | h1011
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1012 | h1012
                    · linarith only [h0, h1, h1004, h1012, h5, h999, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h1012, h4, h5, hc23, hlam, hphi, u3elo3]
                  · linarith only [h1003, h1004, h1005, h1011, h999, hc23, hlam, hphi, u3elo3]
          · linarith only [h1004, h4, h5, hc12, hc24, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1017 | h1017
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1018 | h1018
            · linarith only [h0, h1018, h5, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1020 | h1020
              · linarith only [h0, h1020, h965, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1022 | h1022
                · linarith only [h1, h1001, h1022, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1024 | h1024
                  · linarith only [h0, h1003, h1017, h1024, h2, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1026 | h1026
                    · linarith only [h0, h1, h1017, h1026, h5, h999, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h1026, h4, h5, hc23, hlam, hphi, u3elo3]
          · linarith only [h1017, h4, h5, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 7262000 in
set_option maxHeartbeats 7262000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4 h5
  · exact r1l7_20_12_13_15_H_I_L_I_L_0_L_I_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4 h5

end R2N4
