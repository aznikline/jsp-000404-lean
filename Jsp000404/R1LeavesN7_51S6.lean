import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_51S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5346000 in
set_option maxHeartbeats 5346000 in
theorem r1l7_11_13_25_L_I_L_I_H_L_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h560 | h560
  · rcases m.htr 0 2 5 (by decide) (by decide) with h561 | h561
    · rcases m.htr 0 3 4 (by decide) (by decide) with h562 | h562
      · rcases m.htr 0 3 5 (by decide) (by decide) with h563 | h563
        · rcases m.htr 1 2 3 (by decide) (by decide) with h564 | h564
          · linarith only [h0, h4, h560, h564, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h566 | h566
            · rcases m.htr 1 2 5 (by decide) (by decide) with h567 | h567
              · rcases m.htr 1 3 4 (by decide) (by decide) with h568 | h568
                · rcases m.htr 1 3 5 (by decide) (by decide) with h569 | h569
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h570 | h570
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h571 | h571
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h572 | h572
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h573 | h573
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h574 | h574
                            · rcases h1bigk with h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c
                              · have p575_0 := h575c.1
                                have p575_1 := h575c.2.1
                                have p575_2 := h575c.2.2.1
                                have p575_3 := h575c.2.2.2
                                linarith only [hlam, p575_0]
                              · have p575_0 := h575c.1
                                have p575_1 := h575c.2.1
                                have p575_2 := h575c.2.2.1
                                have p575_3 := h575c.2.2.2
                                linarith only [h566, h571, h574, hc01, hc45, hlam, hphi, ht0b, ht5b, p575_1]
                              · have p575_0 := h575c.1
                                have p575_1 := h575c.2.1
                                have p575_2 := h575c.2.2.1
                                have p575_3 := h575c.2.2.2
                                linarith only [h564, h566, h571, h574, hc01, hc45, hlam, hphi, ht0b, ht5b, p575_1]
                              · have p575_0 := h575c.1
                                have p575_1 := h575c.2.1
                                have p575_2 := h575c.2.2.1
                                have p575_3 := h575c.2.2.2
                                rcases p575_3 (m.d 0 1) (by simp) with h579 | h579
                                · rcases p575_3 (m.d 1 2) (by simp) with h580 | h580
                                  · linarith only [h0, h580, hlam]
                                  · linarith only [h566, h580, hlam]
                                · linarith only [h579, hlam, p575_0]
                              · have p575_0 := h575c.1
                                have p575_1 := h575c.2.1
                                have p575_2 := h575c.2.2.1
                                have p575_3 := h575c.2.2.2
                                rcases p575_3 (m.d 0 1) (by simp) with h584 | h584
                                · rcases p575_3 (m.d 1 2) (by simp) with h585 | h585
                                  · linarith only [h0, h585, hlam]
                                  · linarith only [h567, h585, hlam]
                                · linarith only [h584, hlam, p575_0]
                              · have p575_0 := h575c.1
                                have p575_1 := h575c.2.1
                                have p575_2 := h575c.2.2.1
                                have p575_3 := h575c.2.2.2
                                linarith only [h0, hlam, p575_0]
                              · have p575_0 := h575c.1
                                have p575_1 := h575c.2.1
                                have p575_2 := h575c.2.2.1
                                have p575_3 := h575c.2.2.2
                                linarith only [hlam, p575_0]
                              · have p575_0 := h575c.1
                                have p575_1 := h575c.2.1
                                have p575_2 := h575c.2.2.1
                                have p575_3 := h575c.2.2.2
                                linarith only [h564, hlam, p575_0]
                              · have p575_0 := h575c.1
                                have p575_1 := h575c.2.1
                                have p575_2 := h575c.2.2.1
                                have p575_3 := h575c.2.2.2
                                linarith only [h0, h4, h566, h571, h574, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p575_1]
                              · have p575_0 := h575c.1
                                have p575_1 := h575c.2.1
                                have p575_2 := h575c.2.2.1
                                have p575_3 := h575c.2.2.2
                                rcases p575_3 (m.d 0 1) (by simp) with h593 | h593
                                · rcases p575_3 (m.d 1 2) (by simp) with h594 | h594
                                  · rcases p575_3 (m.d 1 3) (by simp) with h595 | h595
                                    · rcases p575_3 (m.d 1 4) (by simp) with h596 | h596
                                      · linarith only [h566, h596, hlam]
                                      · linarith only [h570, h596, hlam]
                                    · linarith only [h569, h595, hlam]
                                  · linarith only [h567, h594, hlam]
                                · linarith only [h3, h593, hlam]
                              · have p575_0 := h575c.1
                                have p575_1 := h575c.2.1
                                have p575_2 := h575c.2.2.1
                                have p575_3 := h575c.2.2.2
                                linarith only [h1, hlam, p575_0]
                              · have p575_0 := h575c.1
                                have p575_1 := h575c.2.1
                                have p575_2 := h575c.2.2.1
                                have p575_3 := h575c.2.2.2
                                linarith only [h1, h566, h571, h574, hc01, hc45, hlam, hphi, ht0b, ht5b, p575_1]
                              · have p575_0 := h575c.1
                                have p575_1 := h575c.2.1
                                have p575_2 := h575c.2.2.1
                                have p575_3 := h575c.2.2.2
                                linarith only [hlam, p575_0]
                              · have p575_0 := h575c.1
                                have p575_1 := h575c.2.1
                                have p575_2 := h575c.2.2.1
                                have p575_3 := h575c.2.2.2
                                linarith only [h1, h566, h571, h574, hc01, hc45, hlam, hphi, ht0b, ht5b, p575_1]
                              · have p575_0 := h575c.1
                                have p575_1 := h575c.2.1
                                have p575_2 := h575c.2.2.1
                                have p575_3 := h575c.2.2.2
                                rcases p575_3 (m.d 0 1) (by simp) with h606 | h606
                                · rcases p575_3 (m.d 1 2) (by simp) with h607 | h607
                                  · linarith only [h564, h607, hlam]
                                  · linarith only [h567, h607, hlam]
                                · linarith only [h3, h606, hlam]
                              · have p575_0 := h575c.1
                                have p575_1 := h575c.2.1
                                have p575_2 := h575c.2.2.1
                                have p575_3 := h575c.2.2.2
                                linarith only [h2, hlam, p575_0]
                              · have p575_0 := h575c.1
                                have p575_1 := h575c.2.1
                                have p575_2 := h575c.2.2.1
                                have p575_3 := h575c.2.2.2
                                linarith only [h566, hlam, p575_1]
                              · have p575_0 := h575c.1
                                have p575_1 := h575c.2.1
                                have p575_2 := h575c.2.2.1
                                have p575_3 := h575c.2.2.2
                                linarith only [h568, hlam, p575_0]
                              · have p575_0 := h575c.1
                                have p575_1 := h575c.2.1
                                have p575_2 := h575c.2.2.1
                                have p575_3 := h575c.2.2.2
                                linarith only [hlam, p575_0]
                              · have p575_0 := h575c.1
                                have p575_1 := h575c.2.1
                                have p575_2 := h575c.2.2.1
                                have p575_3 := h575c.2.2.2
                                rcases p575_3 (m.d 0 1) (by simp) with h615 | h615
                                · rcases p575_3 (m.d 1 2) (by simp) with h616 | h616
                                  · rcases p575_3 (m.d 1 3) (by simp) with h617 | h617
                                    · rcases p575_3 (m.d 1 4) (by simp) with h618 | h618
                                      · rcases p575_3 (m.d 1 5) (by simp) with h619 | h619
                                        · linarith only [h570, h619, hlam]
                                        · rcases h3bigk with h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c
                                          · have p621_0 := h621c.1
                                            have p621_1 := h621c.2.1
                                            have p621_2 := h621c.2.2.1
                                            have p621_3 := h621c.2.2.2
                                            linarith only [hlam, p621_0]
                                          · have p621_0 := h621c.1
                                            have p621_1 := h621c.2.1
                                            have p621_2 := h621c.2.2.1
                                            have p621_3 := h621c.2.2.2
                                            linarith only [h4, h564, h566, h567, h572, h574, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p575_1, p621_1]
                                          · have p621_0 := h621c.1
                                            have p621_1 := h621c.2.1
                                            have p621_2 := h621c.2.2.1
                                            have p621_3 := h621c.2.2.2
                                            linarith only [h4, hlam, p621_1]
                                          · have p621_0 := h621c.1
                                            have p621_1 := h621c.2.1
                                            have p621_2 := h621c.2.2.1
                                            have p621_3 := h621c.2.2.2
                                            rcases p621_3 (m.d 0 3) (by simp) with h625 | h625
                                            · rcases p621_3 (m.d 1 3) (by simp) with h626 | h626
                                              · linarith only [h1, h626, hlam]
                                              · linarith only [h568, h626, hlam]
                                            · linarith only [h625, hlam, p621_0]
                                          · have p621_0 := h621c.1
                                            have p621_1 := h621c.2.1
                                            have p621_2 := h621c.2.2.1
                                            have p621_3 := h621c.2.2.2
                                            rcases p621_3 (m.d 0 3) (by simp) with h630 | h630
                                            · rcases p621_3 (m.d 1 3) (by simp) with h631 | h631
                                              · linarith only [h1, h631, hlam]
                                              · linarith only [h569, h631, hlam]
                                            · linarith only [h630, hlam, p621_0]
                                          · have p621_0 := h621c.1
                                            have p621_1 := h621c.2.1
                                            have p621_2 := h621c.2.2.1
                                            have p621_3 := h621c.2.2.2
                                            linarith only [h1, hlam, p621_0]
                                          · have p621_0 := h621c.1
                                            have p621_1 := h621c.2.1
                                            have p621_2 := h621c.2.2.1
                                            have p621_3 := h621c.2.2.2
                                            linarith only [hlam, p621_0]
                                          · have p621_0 := h621c.1
                                            have p621_1 := h621c.2.1
                                            have p621_2 := h621c.2.2.1
                                            have p621_3 := h621c.2.2.2
                                            linarith only [h564, hlam, p621_1]
                                          · have p621_0 := h621c.1
                                            have p621_1 := h621c.2.1
                                            have p621_2 := h621c.2.2.1
                                            have p621_3 := h621c.2.2.2
                                            linarith only [h1, h574, hc01, hc45, hlam, hphi, ht0b, ht5b, p621_1]
                                          · have p621_0 := h621c.1
                                            have p621_1 := h621c.2.1
                                            have p621_2 := h621c.2.2.1
                                            have p621_3 := h621c.2.2.2
                                            rcases p621_3 (m.d 0 3) (by simp) with h639 | h639
                                            · rcases p621_3 (m.d 1 3) (by simp) with h640 | h640
                                              · rcases p621_3 (m.d 2 3) (by simp) with h641 | h641
                                                · rcases p621_3 (m.d 3 4) (by simp) with h642 | h642
                                                  · linarith only [h568, h642, hlam]
                                                  · linarith only [h574, h642, hlam]
                                                · linarith only [h572, h641, hlam]
                                              · linarith only [h640, hlam, p621_0]
                                            · linarith only [h563, h639, hlam]
                                          · have p621_0 := h621c.1
                                            have p621_1 := h621c.2.1
                                            have p621_2 := h621c.2.2.1
                                            have p621_3 := h621c.2.2.2
                                            linarith only [h0, h4, h566, h567, h572, h574, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p575_1, p621_1]
                                          · have p621_0 := h621c.1
                                            have p621_1 := h621c.2.1
                                            have p621_2 := h621c.2.2.1
                                            have p621_3 := h621c.2.2.2
                                            linarith only [h564, h566, h567, h572, h574, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p575_1, p621_1]
                                          · have p621_0 := h621c.1
                                            have p621_1 := h621c.2.1
                                            have p621_2 := h621c.2.2.1
                                            have p621_3 := h621c.2.2.2
                                            linarith only [hlam, p621_0]
                                          · have p621_0 := h621c.1
                                            have p621_1 := h621c.2.1
                                            have p621_2 := h621c.2.2.1
                                            have p621_3 := h621c.2.2.2
                                            rcases p621_3 (m.d 0 3) (by simp) with h651 | h651
                                            · linarith only [h4, h651, hlam]
                                            · linarith only [h562, h651, hlam]
                                          · have p621_0 := h621c.1
                                            have p621_1 := h621c.2.1
                                            have p621_2 := h621c.2.2.1
                                            have p621_3 := h621c.2.2.2
                                            linarith only [h0, h4, h566, h567, h572, hlam, p575_1, p621_2]
                                          · have p621_0 := h621c.1
                                            have p621_1 := h621c.2.1
                                            have p621_2 := h621c.2.2.1
                                            have p621_3 := h621c.2.2.2
                                            linarith only [h562, hlam, p621_0]
                                          · have p621_0 := h621c.1
                                            have p621_1 := h621c.2.1
                                            have p621_2 := h621c.2.2.1
                                            have p621_3 := h621c.2.2.2
                                            linarith only [h568, hlam, p621_0]
                                          · have p621_0 := h621c.1
                                            have p621_1 := h621c.2.1
                                            have p621_2 := h621c.2.2.1
                                            have p621_3 := h621c.2.2.2
                                            linarith only [h571, hlam, p621_0]
                                          · have p621_0 := h621c.1
                                            have p621_1 := h621c.2.1
                                            have p621_2 := h621c.2.2.1
                                            have p621_3 := h621c.2.2.2
                                            linarith only [hlam, p621_0]
                                          · have p621_0 := h621c.1
                                            have p621_1 := h621c.2.1
                                            have p621_2 := h621c.2.2.1
                                            have p621_3 := h621c.2.2.2
                                            linarith only [h4, h560, h571, h574, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p621_1]
                                          · have p621_0 := h621c.1
                                            have p621_1 := h621c.2.1
                                            have p621_2 := h621c.2.2.1
                                            have p621_3 := h621c.2.2.2
                                            linarith only [h563, hlam, p621_0]
                                          · have p621_0 := h621c.1
                                            have p621_1 := h621c.2.1
                                            have p621_2 := h621c.2.2.1
                                            have p621_3 := h621c.2.2.2
                                            linarith only [h569, hlam, p621_0]
                                          · have p621_0 := h621c.1
                                            have p621_1 := h621c.2.1
                                            have p621_2 := h621c.2.2.1
                                            have p621_3 := h621c.2.2.2
                                            linarith only [h572, hlam, p621_0]
                                          · have p621_0 := h621c.1
                                            have p621_1 := h621c.2.1
                                            have p621_2 := h621c.2.2.1
                                            have p621_3 := h621c.2.2.2
                                            linarith only [h574, hlam, p621_0]
                                          · have p621_0 := h621c.1
                                            have p621_1 := h621c.2.1
                                            have p621_2 := h621c.2.2.1
                                            have p621_3 := h621c.2.2.2
                                            linarith only [hlam, p621_0]
                                      · linarith only [h570, h618, hlam]
                                    · linarith only [h569, h617, hlam]
                                  · linarith only [h567, h616, hlam]
                                · linarith only [h3, h615, hlam]
                              · have p575_0 := h575c.1
                                have p575_1 := h575c.2.1
                                have p575_2 := h575c.2.2.1
                                have p575_3 := h575c.2.2.2
                                linarith only [h3, hlam, p575_0]
                              · have p575_0 := h575c.1
                                have p575_1 := h575c.2.1
                                have p575_2 := h575c.2.2.1
                                have p575_3 := h575c.2.2.2
                                linarith only [h567, hlam, p575_1]
                              · have p575_0 := h575c.1
                                have p575_1 := h575c.2.1
                                have p575_2 := h575c.2.2.1
                                have p575_3 := h575c.2.2.2
                                linarith only [h569, hlam, p575_0]
                              · have p575_0 := h575c.1
                                have p575_1 := h575c.2.1
                                have p575_2 := h575c.2.2.1
                                have p575_3 := h575c.2.2.2
                                linarith only [h570, hlam, p575_0]
                              · have p575_0 := h575c.1
                                have p575_1 := h575c.2.1
                                have p575_2 := h575c.2.2.1
                                have p575_3 := h575c.2.2.2
                                linarith only [hlam, p575_0]
                            · linarith only [h574, hc34, hlam, hphi, ht45, u5elo4]
                          · linarith only [h570, h573, hc24, hlam, hphi, ht45, u5elo1]
                        · linarith only [h4, h572, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h0, h4, h566, h568, h571, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h570, hc14, hlam, hphi, ht45, u5elo4]
                  · linarith only [h569, hc13, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h564, h566, h568, hlam]
              · linarith only [h566, h567, hc24, hlam, hphi, ht45, u5elo2]
            · linarith only [h4, h560, h566, hc12, hc23, hlam, hphi]
        · linarith only [h563, hc03, hlam, hphi, ht34, ht45, u5elo3]
      · linarith only [h4, h560, h562, hlam]
    · linarith only [h561, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h686 | h686
    · rcases m.htr 0 3 4 (by decide) (by decide) with h687 | h687
      · rcases m.htr 0 3 5 (by decide) (by decide) with h688 | h688
        · rcases m.htr 1 2 3 (by decide) (by decide) with h689 | h689
          · linarith only [h0, h4, h689, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h691 | h691
            · linarith only [h0, h560, h691, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h693 | h693
              · rcases m.htr 1 3 4 (by decide) (by decide) with h694 | h694
                · rcases m.htr 1 3 5 (by decide) (by decide) with h695 | h695
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h696 | h696
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h697 | h697
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h698 | h698
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h699 | h699
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h700 | h700
                            · rcases h1bigk with h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c
                              · have p701_0 := h701c.1
                                have p701_1 := h701c.2.1
                                have p701_2 := h701c.2.2.1
                                have p701_3 := h701c.2.2.2
                                linarith only [hlam, p701_0]
                              · have p701_0 := h701c.1
                                have p701_1 := h701c.2.1
                                have p701_2 := h701c.2.2.1
                                have p701_3 := h701c.2.2.2
                                rcases p701_3 (m.d 0 1) (by simp) with h703 | h703
                                · rcases p701_3 (m.d 1 2) (by simp) with h704 | h704
                                  · linarith only [h704, hlam, p701_0]
                                  · rcases p701_3 (m.d 1 3) (by simp) with h706 | h706
                                    · linarith only [h1, h706, hlam]
                                    · linarith only [h689, h706, hlam]
                                · linarith only [h703, hlam, p701_0]
                              · have p701_0 := h701c.1
                                have p701_1 := h701c.2.1
                                have p701_2 := h701c.2.2.1
                                have p701_3 := h701c.2.2.2
                                linarith only [h694, h700, hc01, hc45, hlam, hphi, ht0b, ht5b, p701_1]
                              · have p701_0 := h701c.1
                                have p701_1 := h701c.2.1
                                have p701_2 := h701c.2.2.1
                                have p701_3 := h701c.2.2.2
                                rcases p701_3 (m.d 0 1) (by simp) with h711 | h711
                                · rcases p701_3 (m.d 1 2) (by simp) with h712 | h712
                                  · linarith only [h0, h712, hlam]
                                  · rcases p701_3 (m.d 1 3) (by simp) with h714 | h714
                                    · linarith only [h1, h714, hlam]
                                    · linarith only [h694, h714, hlam]
                                · linarith only [h711, hlam, p701_0]
                              · have p701_0 := h701c.1
                                have p701_1 := h701c.2.1
                                have p701_2 := h701c.2.2.1
                                have p701_3 := h701c.2.2.2
                                rcases p701_3 (m.d 0 1) (by simp) with h718 | h718
                                · rcases p701_3 (m.d 1 2) (by simp) with h719 | h719
                                  · linarith only [h0, h719, hlam]
                                  · linarith only [h693, h719, hlam]
                                · linarith only [h718, hlam, p701_0]
                              · have p701_0 := h701c.1
                                have p701_1 := h701c.2.1
                                have p701_2 := h701c.2.2.1
                                have p701_3 := h701c.2.2.2
                                linarith only [h0, hlam, p701_0]
                              · have p701_0 := h701c.1
                                have p701_1 := h701c.2.1
                                have p701_2 := h701c.2.2.1
                                have p701_3 := h701c.2.2.2
                                linarith only [hlam, p701_0]
                              · have p701_0 := h701c.1
                                have p701_1 := h701c.2.1
                                have p701_2 := h701c.2.2.1
                                have p701_3 := h701c.2.2.2
                                linarith only [h689, hlam, p701_0]
                              · have p701_0 := h701c.1
                                have p701_1 := h701c.2.1
                                have p701_2 := h701c.2.2.1
                                have p701_3 := h701c.2.2.2
                                linarith only [h691, hlam, p701_0]
                              · have p701_0 := h701c.1
                                have p701_1 := h701c.2.1
                                have p701_2 := h701c.2.2.1
                                have p701_3 := h701c.2.2.2
                                rcases p701_3 (m.d 0 1) (by simp) with h727 | h727
                                · rcases p701_3 (m.d 1 2) (by simp) with h728 | h728
                                  · rcases p701_3 (m.d 1 3) (by simp) with h729 | h729
                                    · rcases p701_3 (m.d 1 4) (by simp) with h730 | h730
                                      · rcases p701_3 (m.d 1 5) (by simp) with h731 | h731
                                        · linarith only [h693, h731, hlam]
                                        · rcases h3bigk with h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c
                                          · have p733_0 := h733c.1
                                            have p733_1 := h733c.2.1
                                            have p733_2 := h733c.2.2.1
                                            have p733_3 := h733c.2.2.2
                                            linarith only [hlam, p733_0]
                                          · have p733_0 := h733c.1
                                            have p733_1 := h733c.2.1
                                            have p733_2 := h733c.2.2.1
                                            have p733_3 := h733c.2.2.2
                                            linarith only [h691, h694, hc03, hc15, hlam, hphi, ht0b, ht5b, p701_1, p733_1]
                                          · have p733_0 := h733c.1
                                            have p733_1 := h733c.2.1
                                            have p733_2 := h733c.2.2.1
                                            have p733_3 := h733c.2.2.2
                                            linarith only [h4, hlam, p733_1]
                                          · have p733_0 := h733c.1
                                            have p733_1 := h733c.2.1
                                            have p733_2 := h733c.2.2.1
                                            have p733_3 := h733c.2.2.2
                                            rcases p733_3 (m.d 0 3) (by simp) with h737 | h737
                                            · rcases p733_3 (m.d 1 3) (by simp) with h738 | h738
                                              · linarith only [h1, h738, hlam]
                                              · linarith only [h694, h738, hlam]
                                            · linarith only [h737, hlam, p733_0]
                                          · have p733_0 := h733c.1
                                            have p733_1 := h733c.2.1
                                            have p733_2 := h733c.2.2.1
                                            have p733_3 := h733c.2.2.2
                                            rcases p733_3 (m.d 0 3) (by simp) with h742 | h742
                                            · rcases p733_3 (m.d 1 3) (by simp) with h743 | h743
                                              · linarith only [h1, h743, hlam]
                                              · linarith only [h695, h743, hlam]
                                            · linarith only [h742, hlam, p733_0]
                                          · have p733_0 := h733c.1
                                            have p733_1 := h733c.2.1
                                            have p733_2 := h733c.2.2.1
                                            have p733_3 := h733c.2.2.2
                                            linarith only [h1, hlam, p733_0]
                                          · have p733_0 := h733c.1
                                            have p733_1 := h733c.2.1
                                            have p733_2 := h733c.2.2.1
                                            have p733_3 := h733c.2.2.2
                                            linarith only [hlam, p733_0]
                                          · have p733_0 := h733c.1
                                            have p733_1 := h733c.2.1
                                            have p733_2 := h733c.2.2.1
                                            have p733_3 := h733c.2.2.2
                                            linarith only [h689, hlam, p733_1]
                                          · have p733_0 := h733c.1
                                            have p733_1 := h733c.2.1
                                            have p733_2 := h733c.2.2.1
                                            have p733_3 := h733c.2.2.2
                                            linarith only [h1, h700, hc01, hc45, hlam, hphi, ht0b, ht5b, p733_1]
                                          · have p733_0 := h733c.1
                                            have p733_1 := h733c.2.1
                                            have p733_2 := h733c.2.2.1
                                            have p733_3 := h733c.2.2.2
                                            rcases p733_3 (m.d 0 3) (by simp) with h751 | h751
                                            · rcases p733_3 (m.d 1 3) (by simp) with h752 | h752
                                              · rcases p733_3 (m.d 2 3) (by simp) with h753 | h753
                                                · rcases p733_3 (m.d 3 4) (by simp) with h754 | h754
                                                  · linarith only [h694, h754, hlam]
                                                  · linarith only [h700, h754, hlam]
                                                · linarith only [h698, h753, hlam]
                                              · linarith only [h752, hlam, p733_0]
                                            · linarith only [h688, h751, hlam]
                                          · have p733_0 := h733c.1
                                            have p733_1 := h733c.2.1
                                            have p733_2 := h733c.2.2.1
                                            have p733_3 := h733c.2.2.2
                                            linarith only [h0, h4, h693, h698, h700, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p701_1, p733_1]
                                          · have p733_0 := h733c.1
                                            have p733_1 := h733c.2.1
                                            have p733_2 := h733c.2.2.1
                                            have p733_3 := h733c.2.2.2
                                            linarith only [h689, h693, h698, h700, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p701_1, p733_1]
                                          · have p733_0 := h733c.1
                                            have p733_1 := h733c.2.1
                                            have p733_2 := h733c.2.2.1
                                            have p733_3 := h733c.2.2.2
                                            linarith only [hlam, p733_0]
                                          · have p733_0 := h733c.1
                                            have p733_1 := h733c.2.1
                                            have p733_2 := h733c.2.2.1
                                            have p733_3 := h733c.2.2.2
                                            rcases p733_3 (m.d 0 3) (by simp) with h763 | h763
                                            · linarith only [h4, h763, hlam]
                                            · linarith only [h687, h763, hlam]
                                          · have p733_0 := h733c.1
                                            have p733_1 := h733c.2.1
                                            have p733_2 := h733c.2.2.1
                                            have p733_3 := h733c.2.2.2
                                            linarith only [h0, h4, h693, h698, hlam, p701_1, p733_2]
                                          · have p733_0 := h733c.1
                                            have p733_1 := h733c.2.1
                                            have p733_2 := h733c.2.2.1
                                            have p733_3 := h733c.2.2.2
                                            linarith only [h687, hlam, p733_0]
                                          · have p733_0 := h733c.1
                                            have p733_1 := h733c.2.1
                                            have p733_2 := h733c.2.2.1
                                            have p733_3 := h733c.2.2.2
                                            linarith only [h694, hlam, p733_0]
                                          · have p733_0 := h733c.1
                                            have p733_1 := h733c.2.1
                                            have p733_2 := h733c.2.2.1
                                            have p733_3 := h733c.2.2.2
                                            linarith only [h697, hlam, p733_0]
                                          · have p733_0 := h733c.1
                                            have p733_1 := h733c.2.1
                                            have p733_2 := h733c.2.2.1
                                            have p733_3 := h733c.2.2.2
                                            linarith only [hlam, p733_0]
                                          · have p733_0 := h733c.1
                                            have p733_1 := h733c.2.1
                                            have p733_2 := h733c.2.2.1
                                            have p733_3 := h733c.2.2.2
                                            linarith only [h1, h694, h700, hc01, hc45, hlam, hphi, ht0b, ht5b, p733_1]
                                          · have p733_0 := h733c.1
                                            have p733_1 := h733c.2.1
                                            have p733_2 := h733c.2.2.1
                                            have p733_3 := h733c.2.2.2
                                            linarith only [h688, hlam, p733_0]
                                          · have p733_0 := h733c.1
                                            have p733_1 := h733c.2.1
                                            have p733_2 := h733c.2.2.1
                                            have p733_3 := h733c.2.2.2
                                            linarith only [h695, hlam, p733_0]
                                          · have p733_0 := h733c.1
                                            have p733_1 := h733c.2.1
                                            have p733_2 := h733c.2.2.1
                                            have p733_3 := h733c.2.2.2
                                            linarith only [h698, hlam, p733_0]
                                          · have p733_0 := h733c.1
                                            have p733_1 := h733c.2.1
                                            have p733_2 := h733c.2.2.1
                                            have p733_3 := h733c.2.2.2
                                            linarith only [h700, hlam, p733_0]
                                          · have p733_0 := h733c.1
                                            have p733_1 := h733c.2.1
                                            have p733_2 := h733c.2.2.1
                                            have p733_3 := h733c.2.2.2
                                            linarith only [hlam, p733_0]
                                      · linarith only [h696, h730, hlam]
                                    · linarith only [h695, h729, hlam]
                                  · linarith only [h693, h728, hlam]
                                · linarith only [h3, h727, hlam]
                              · have p701_0 := h701c.1
                                have p701_1 := h701c.2.1
                                have p701_2 := h701c.2.2.1
                                have p701_3 := h701c.2.2.2
                                linarith only [h1, hlam, p701_0]
                              · have p701_0 := h701c.1
                                have p701_1 := h701c.2.1
                                have p701_2 := h701c.2.2.1
                                have p701_3 := h701c.2.2.2
                                linarith only [h1, h693, h698, h700, hc01, hc45, hlam, hphi, ht0b, ht5b, p701_1]
                              · have p701_0 := h701c.1
                                have p701_1 := h701c.2.1
                                have p701_2 := h701c.2.2.1
                                have p701_3 := h701c.2.2.2
                                linarith only [hlam, p701_0]
                              · have p701_0 := h701c.1
                                have p701_1 := h701c.2.1
                                have p701_2 := h701c.2.2.1
                                have p701_3 := h701c.2.2.2
                                linarith only [h1, h691, h693, h698, h700, hc01, hc45, hlam, hphi, ht0b, ht5b, p701_1]
                              · have p701_0 := h701c.1
                                have p701_1 := h701c.2.1
                                have p701_2 := h701c.2.2.1
                                have p701_3 := h701c.2.2.2
                                rcases p701_3 (m.d 0 1) (by simp) with h785 | h785
                                · rcases p701_3 (m.d 1 2) (by simp) with h786 | h786
                                  · linarith only [h689, h786, hlam]
                                  · linarith only [h693, h786, hlam]
                                · linarith only [h3, h785, hlam]
                              · have p701_0 := h701c.1
                                have p701_1 := h701c.2.1
                                have p701_2 := h701c.2.2.1
                                have p701_3 := h701c.2.2.2
                                linarith only [h2, hlam, p701_0]
                              · have p701_0 := h701c.1
                                have p701_1 := h701c.2.1
                                have p701_2 := h701c.2.2.1
                                have p701_3 := h701c.2.2.2
                                linarith only [h2, h693, h698, h700, hc01, hc45, hlam, hphi, ht0b, ht5b, p701_1]
                              · have p701_0 := h701c.1
                                have p701_1 := h701c.2.1
                                have p701_2 := h701c.2.2.1
                                have p701_3 := h701c.2.2.2
                                linarith only [h694, hlam, p701_0]
                              · have p701_0 := h701c.1
                                have p701_1 := h701c.2.1
                                have p701_2 := h701c.2.2.1
                                have p701_3 := h701c.2.2.2
                                linarith only [hlam, p701_0]
                              · have p701_0 := h701c.1
                                have p701_1 := h701c.2.1
                                have p701_2 := h701c.2.2.1
                                have p701_3 := h701c.2.2.2
                                rcases p701_3 (m.d 0 1) (by simp) with h794 | h794
                                · rcases p701_3 (m.d 1 2) (by simp) with h795 | h795
                                  · linarith only [h691, h795, hlam]
                                  · linarith only [h693, h795, hlam]
                                · linarith only [h3, h794, hlam]
                              · have p701_0 := h701c.1
                                have p701_1 := h701c.2.1
                                have p701_2 := h701c.2.2.1
                                have p701_3 := h701c.2.2.2
                                linarith only [h3, hlam, p701_0]
                              · have p701_0 := h701c.1
                                have p701_1 := h701c.2.1
                                have p701_2 := h701c.2.2.1
                                have p701_3 := h701c.2.2.2
                                linarith only [h693, hlam, p701_1]
                              · have p701_0 := h701c.1
                                have p701_1 := h701c.2.1
                                have p701_2 := h701c.2.2.1
                                have p701_3 := h701c.2.2.2
                                linarith only [h695, hlam, p701_0]
                              · have p701_0 := h701c.1
                                have p701_1 := h701c.2.1
                                have p701_2 := h701c.2.2.1
                                have p701_3 := h701c.2.2.2
                                linarith only [h696, hlam, p701_0]
                              · have p701_0 := h701c.1
                                have p701_1 := h701c.2.1
                                have p701_2 := h701c.2.2.1
                                have p701_3 := h701c.2.2.2
                                linarith only [hlam, p701_0]
                            · linarith only [h700, hc34, hlam, hphi, ht45, u5elo4]
                          · linarith only [h560, h699, hc04, hlam, hphi, ht45, u5elo4]
                        · linarith only [h560, h697, h698, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h0, h1, h4, h693, h694, h697, hc03, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h691, h693, h696, hc25, hlam, hphi, u5elo4]
                  · linarith only [h695, hc13, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h810 | h810
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h811 | h811
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h812 | h812
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h813 | h813
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h814 | h814
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h815 | h815
                            · rcases h1bigk with h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c
                              · have p816_0 := h816c.1
                                have p816_1 := h816c.2.1
                                have p816_2 := h816c.2.2.1
                                have p816_3 := h816c.2.2.2
                                linarith only [hlam, p816_0]
                              · have p816_0 := h816c.1
                                have p816_1 := h816c.2.1
                                have p816_2 := h816c.2.2.1
                                have p816_3 := h816c.2.2.2
                                rcases p816_3 (m.d 0 1) (by simp) with h818 | h818
                                · rcases p816_3 (m.d 1 2) (by simp) with h819 | h819
                                  · linarith only [h819, hlam, p816_0]
                                  · rcases p816_3 (m.d 1 3) (by simp) with h821 | h821
                                    · linarith only [h1, h821, hlam]
                                    · linarith only [h689, h821, hlam]
                                · linarith only [h818, hlam, p816_0]
                              · have p816_0 := h816c.1
                                have p816_1 := h816c.2.1
                                have p816_2 := h816c.2.2.1
                                have p816_3 := h816c.2.2.2
                                rcases p816_3 (m.d 0 1) (by simp) with h825 | h825
                                · rcases p816_3 (m.d 1 2) (by simp) with h826 | h826
                                  · linarith only [h0, h826, hlam]
                                  · rcases p816_3 (m.d 1 3) (by simp) with h828 | h828
                                    · linarith only [h828, hlam, p816_0]
                                    · rcases p816_3 (m.d 1 4) (by simp) with h830 | h830
                                      · linarith only [h2, h830, hlam]
                                      · linarith only [h694, h830, hlam]
                                · linarith only [h825, hlam, p816_0]
                              · have p816_0 := h816c.1
                                have p816_1 := h816c.2.1
                                have p816_2 := h816c.2.2.1
                                have p816_3 := h816c.2.2.2
                                rcases p816_3 (m.d 0 1) (by simp) with h834 | h834
                                · rcases p816_3 (m.d 1 2) (by simp) with h835 | h835
                                  · linarith only [h0, h835, hlam]
                                  · rcases p816_3 (m.d 1 3) (by simp) with h837 | h837
                                    · linarith only [h1, h837, hlam]
                                    · rcases p816_3 (m.d 1 4) (by simp) with h839 | h839
                                      · linarith only [h839, hlam, p816_0]
                                      · rcases p816_3 (m.d 1 5) (by simp) with h841 | h841
                                        · linarith only [h3, h841, hlam]
                                        · rcases h3bigk with h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c
                                          · have p843_0 := h843c.1
                                            have p843_1 := h843c.2.1
                                            have p843_2 := h843c.2.2.1
                                            have p843_3 := h843c.2.2.2
                                            linarith only [hlam, p843_0]
                                          · have p843_0 := h843c.1
                                            have p843_1 := h843c.2.1
                                            have p843_2 := h843c.2.2.1
                                            have p843_3 := h843c.2.2.2
                                            rcases p843_3 (m.d 0 3) (by simp) with h845 | h845
                                            · rcases p843_3 (m.d 1 3) (by simp) with h846 | h846
                                              · linarith only [h1, h846, hlam]
                                              · rcases p843_3 (m.d 2 3) (by simp) with h848 | h848
                                                · rcases p843_3 (m.d 3 4) (by simp) with h849 | h849
                                                  · linarith only [h687, h849, hlam]
                                                  · linarith only [h694, h849, hlam]
                                                · linarith only [h689, h848, hlam]
                                            · linarith only [h1, h845, hlam]
                                          · have p843_0 := h843c.1
                                            have p843_1 := h843c.2.1
                                            have p843_2 := h843c.2.2.1
                                            have p843_3 := h843c.2.2.2
                                            linarith only [h4, hlam, p843_1]
                                          · have p843_0 := h843c.1
                                            have p843_1 := h843c.2.1
                                            have p843_2 := h843c.2.2.1
                                            have p843_3 := h843c.2.2.2
                                            linarith only [h4, h689, h693, h694, h813, h815, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p843_1]
                                          · have p843_0 := h843c.1
                                            have p843_1 := h843c.2.1
                                            have p843_2 := h843c.2.2.1
                                            have p843_3 := h843c.2.2.2
                                            linarith only [h687, h689, h693, h694, h813, hlam, p843_2]
                                          · have p843_0 := h843c.1
                                            have p843_1 := h843c.2.1
                                            have p843_2 := h843c.2.2.1
                                            have p843_3 := h843c.2.2.2
                                            linarith only [h1, hlam, p843_0]
                                          · have p843_0 := h843c.1
                                            have p843_1 := h843c.2.1
                                            have p843_2 := h843c.2.2.1
                                            have p843_3 := h843c.2.2.2
                                            linarith only [hlam, p843_0]
                                          · have p843_0 := h843c.1
                                            have p843_1 := h843c.2.1
                                            have p843_2 := h843c.2.2.1
                                            have p843_3 := h843c.2.2.2
                                            linarith only [h689, hlam, p843_1]
                                          · have p843_0 := h843c.1
                                            have p843_1 := h843c.2.1
                                            have p843_2 := h843c.2.2.1
                                            have p843_3 := h843c.2.2.2
                                            linarith only [h694, hlam, p843_0]
                                          · have p843_0 := h843c.1
                                            have p843_1 := h843c.2.1
                                            have p843_2 := h843c.2.2.1
                                            have p843_3 := h843c.2.2.2
                                            linarith only [h687, h694, h815, hc03, hc45, hlam, hphi, ht0b, ht5b, p843_1]
                                          · have p843_0 := h843c.1
                                            have p843_1 := h843c.2.1
                                            have p843_2 := h843c.2.2.1
                                            have p843_3 := h843c.2.2.2
                                            linarith only [h687, h694, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p843_1]
                                          · have p843_0 := h843c.1
                                            have p843_1 := h843c.2.1
                                            have p843_2 := h843c.2.2.1
                                            have p843_3 := h843c.2.2.2
                                            rcases p843_3 (m.d 0 3) (by simp) with h863 | h863
                                            · linarith only [h4, h863, hlam]
                                            · linarith only [h1, h863, hlam]
                                          · have p843_0 := h843c.1
                                            have p843_1 := h843c.2.1
                                            have p843_2 := h843c.2.2.1
                                            have p843_3 := h843c.2.2.2
                                            linarith only [hlam, p843_0]
                                          · have p843_0 := h843c.1
                                            have p843_1 := h843c.2.1
                                            have p843_2 := h843c.2.2.1
                                            have p843_3 := h843c.2.2.2
                                            linarith only [h689, h693, h694, h813, h815, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p843_1]
                                          · have p843_0 := h843c.1
                                            have p843_1 := h843c.2.1
                                            have p843_2 := h843c.2.2.1
                                            have p843_3 := h843c.2.2.2
                                            linarith only [h4, h687, h689, h693, h694, h813, hlam, p843_2]
                                          · have p843_0 := h843c.1
                                            have p843_1 := h843c.2.1
                                            have p843_2 := h843c.2.2.1
                                            have p843_3 := h843c.2.2.2
                                            linarith only [h687, hlam, p843_0]
                                          · have p843_0 := h843c.1
                                            have p843_1 := h843c.2.1
                                            have p843_2 := h843c.2.2.1
                                            have p843_3 := h843c.2.2.2
                                            linarith only [h687, h689, h693, h813, h815, hc03, hc45, hlam, hphi, ht0b, ht5b, p843_1]
                                          · have p843_0 := h843c.1
                                            have p843_1 := h843c.2.1
                                            have p843_2 := h843c.2.2.1
                                            have p843_3 := h843c.2.2.2
                                            linarith only [h812, hlam, p843_0]
                                          · have p843_0 := h843c.1
                                            have p843_1 := h843c.2.1
                                            have p843_2 := h843c.2.2.1
                                            have p843_3 := h843c.2.2.2
                                            linarith only [hlam, p843_0]
                                          · have p843_0 := h843c.1
                                            have p843_1 := h843c.2.1
                                            have p843_2 := h843c.2.2.1
                                            have p843_3 := h843c.2.2.2
                                            rcases p843_3 (m.d 0 3) (by simp) with h873 | h873
                                            · rcases p843_3 (m.d 1 3) (by simp) with h874 | h874
                                              · linarith only [h694, h874, hlam]
                                              · linarith only [h810, h874, hlam]
                                            · linarith only [h688, h873, hlam]
                                          · have p843_0 := h843c.1
                                            have p843_1 := h843c.2.1
                                            have p843_2 := h843c.2.2.1
                                            have p843_3 := h843c.2.2.2
                                            linarith only [h688, hlam, p843_0]
                                          · have p843_0 := h843c.1
                                            have p843_1 := h843c.2.1
                                            have p843_2 := h843c.2.2.1
                                            have p843_3 := h843c.2.2.2
                                            linarith only [h810, hlam, p843_0]
                                          · have p843_0 := h843c.1
                                            have p843_1 := h843c.2.1
                                            have p843_2 := h843c.2.2.1
                                            have p843_3 := h843c.2.2.2
                                            linarith only [h813, hlam, p843_0]
                                          · have p843_0 := h843c.1
                                            have p843_1 := h843c.2.1
                                            have p843_2 := h843c.2.2.1
                                            have p843_3 := h843c.2.2.2
                                            linarith only [h815, hlam, p843_0]
                                          · have p843_0 := h843c.1
                                            have p843_1 := h843c.2.1
                                            have p843_2 := h843c.2.2.1
                                            have p843_3 := h843c.2.2.2
                                            linarith only [hlam, p843_0]
                                · linarith only [h834, hlam, p816_0]
                              · have p816_0 := h816c.1
                                have p816_1 := h816c.2.1
                                have p816_2 := h816c.2.2.1
                                have p816_3 := h816c.2.2.2
                                rcases p816_3 (m.d 0 1) (by simp) with h884 | h884
                                · rcases p816_3 (m.d 1 2) (by simp) with h885 | h885
                                  · linarith only [h0, h885, hlam]
                                  · linarith only [h693, h885, hlam]
                                · linarith only [h884, hlam, p816_0]
                              · have p816_0 := h816c.1
                                have p816_1 := h816c.2.1
                                have p816_2 := h816c.2.2.1
                                have p816_3 := h816c.2.2.2
                                linarith only [h0, hlam, p816_0]
                              · have p816_0 := h816c.1
                                have p816_1 := h816c.2.1
                                have p816_2 := h816c.2.2.1
                                have p816_3 := h816c.2.2.2
                                linarith only [hlam, p816_0]
                              · have p816_0 := h816c.1
                                have p816_1 := h816c.2.1
                                have p816_2 := h816c.2.2.1
                                have p816_3 := h816c.2.2.2
                                linarith only [h689, hlam, p816_0]
                              · have p816_0 := h816c.1
                                have p816_1 := h816c.2.1
                                have p816_2 := h816c.2.2.1
                                have p816_3 := h816c.2.2.2
                                linarith only [h691, hlam, p816_0]
                              · have p816_0 := h816c.1
                                have p816_1 := h816c.2.1
                                have p816_2 := h816c.2.2.1
                                have p816_3 := h816c.2.2.2
                                linarith only [h4, h687, h689, h693, h694, h813, h815, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p816_1]
                              · have p816_0 := h816c.1
                                have p816_1 := h816c.2.1
                                have p816_2 := h816c.2.2.1
                                have p816_3 := h816c.2.2.2
                                linarith only [h1, hlam, p816_0]
                              · have p816_0 := h816c.1
                                have p816_1 := h816c.2.1
                                have p816_2 := h816c.2.2.1
                                have p816_3 := h816c.2.2.2
                                linarith only [h2, h693, h694, h813, h815, hc01, hc45, hlam, hphi, ht0b, ht5b, p816_1]
                              · have p816_0 := h816c.1
                                have p816_1 := h816c.2.1
                                have p816_2 := h816c.2.2.1
                                have p816_3 := h816c.2.2.2
                                linarith only [hlam, p816_0]
                              · have p816_0 := h816c.1
                                have p816_1 := h816c.2.1
                                have p816_2 := h816c.2.2.1
                                have p816_3 := h816c.2.2.2
                                linarith only [h694, hlam, p816_1]
                              · have p816_0 := h816c.1
                                have p816_1 := h816c.2.1
                                have p816_2 := h816c.2.2.1
                                have p816_3 := h816c.2.2.2
                                linarith only [h4, h687, h693, h694, h813, h815, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p816_1]
                              · have p816_0 := h816c.1
                                have p816_1 := h816c.2.1
                                have p816_2 := h816c.2.2.1
                                have p816_3 := h816c.2.2.2
                                linarith only [h2, hlam, p816_0]
                              · have p816_0 := h816c.1
                                have p816_1 := h816c.2.1
                                have p816_2 := h816c.2.2.1
                                have p816_3 := h816c.2.2.2
                                linarith only [h4, h687, h694, hc12, hc23, hlam, hphi, p816_1]
                              · have p816_0 := h816c.1
                                have p816_1 := h816c.2.1
                                have p816_2 := h816c.2.2.1
                                have p816_3 := h816c.2.2.2
                                linarith only [h4, h687, h689, h693, h694, h813, h815, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p816_1]
                              · have p816_0 := h816c.1
                                have p816_1 := h816c.2.1
                                have p816_2 := h816c.2.2.1
                                have p816_3 := h816c.2.2.2
                                linarith only [hlam, p816_0]
                              · have p816_0 := h816c.1
                                have p816_1 := h816c.2.1
                                have p816_2 := h816c.2.2.1
                                have p816_3 := h816c.2.2.2
                                rcases p816_3 (m.d 0 1) (by simp) with h903 | h903
                                · rcases p816_3 (m.d 1 2) (by simp) with h904 | h904
                                  · linarith only [h691, h904, hlam]
                                  · linarith only [h693, h904, hlam]
                                · linarith only [h3, h903, hlam]
                              · have p816_0 := h816c.1
                                have p816_1 := h816c.2.1
                                have p816_2 := h816c.2.2.1
                                have p816_3 := h816c.2.2.2
                                linarith only [h3, hlam, p816_0]
                              · have p816_0 := h816c.1
                                have p816_1 := h816c.2.1
                                have p816_2 := h816c.2.2.1
                                have p816_3 := h816c.2.2.2
                                linarith only [h693, hlam, p816_1]
                              · have p816_0 := h816c.1
                                have p816_1 := h816c.2.1
                                have p816_2 := h816c.2.2.1
                                have p816_3 := h816c.2.2.2
                                linarith only [h810, hlam, p816_0]
                              · have p816_0 := h816c.1
                                have p816_1 := h816c.2.1
                                have p816_2 := h816c.2.2.1
                                have p816_3 := h816c.2.2.2
                                linarith only [h811, hlam, p816_0]
                              · have p816_0 := h816c.1
                                have p816_1 := h816c.2.1
                                have p816_2 := h816c.2.2.1
                                have p816_3 := h816c.2.2.2
                                linarith only [hlam, p816_0]
                            · linarith only [h694, h815, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h560, h687, h689, h693, h694, h811, h814, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h4, h687, h689, h693, h694, h813, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h4, h687, h812, hlam]
                    · linarith only [h811, hc14, hlam, hphi, ht45, u5elo4]
                  · linarith only [h689, h693, h810, hc25, hlam, hphi, u5elo3]
              · linarith only [h693, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h688, hc03, hlam, hphi, ht34, ht45, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h921 | h921
        · rcases m.htr 1 2 3 (by decide) (by decide) with h922 | h922
          · linarith only [h0, h4, h922, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h924 | h924
            · linarith only [h1, h560, h687, h922, h924, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h926 | h926
              · rcases m.htr 1 3 4 (by decide) (by decide) with h927 | h927
                · linarith only [h1, h687, h927, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h929 | h929
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h930 | h930
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h931 | h931
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h932 | h932
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h933 | h933
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h934 | h934
                            · rcases h1bigk with h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c
                              · have p935_0 := h935c.1
                                have p935_1 := h935c.2.1
                                have p935_2 := h935c.2.2.1
                                have p935_3 := h935c.2.2.2
                                linarith only [hlam, p935_0]
                              · have p935_0 := h935c.1
                                have p935_1 := h935c.2.1
                                have p935_2 := h935c.2.2.1
                                have p935_3 := h935c.2.2.2
                                rcases p935_3 (m.d 0 1) (by simp) with h937 | h937
                                · rcases p935_3 (m.d 1 2) (by simp) with h938 | h938
                                  · linarith only [h938, hlam, p935_0]
                                  · rcases p935_3 (m.d 1 3) (by simp) with h940 | h940
                                    · linarith only [h1, h940, hlam]
                                    · linarith only [h922, h940, hlam]
                                · linarith only [h937, hlam, p935_0]
                              · have p935_0 := h935c.1
                                have p935_1 := h935c.2.1
                                have p935_2 := h935c.2.2.1
                                have p935_3 := h935c.2.2.2
                                rcases p935_3 (m.d 0 1) (by simp) with h944 | h944
                                · rcases p935_3 (m.d 1 2) (by simp) with h945 | h945
                                  · linarith only [h0, h945, hlam]
                                  · rcases p935_3 (m.d 1 3) (by simp) with h947 | h947
                                    · linarith only [h947, hlam, p935_0]
                                    · rcases p935_3 (m.d 1 4) (by simp) with h949 | h949
                                      · linarith only [h2, h949, hlam]
                                      · linarith only [h927, h949, hlam]
                                · linarith only [h944, hlam, p935_0]
                              · have p935_0 := h935c.1
                                have p935_1 := h935c.2.1
                                have p935_2 := h935c.2.2.1
                                have p935_3 := h935c.2.2.2
                                rcases p935_3 (m.d 0 1) (by simp) with h953 | h953
                                · rcases p935_3 (m.d 1 2) (by simp) with h954 | h954
                                  · linarith only [h0, h954, hlam]
                                  · rcases p935_3 (m.d 1 3) (by simp) with h956 | h956
                                    · linarith only [h1, h956, hlam]
                                    · rcases p935_3 (m.d 1 4) (by simp) with h958 | h958
                                      · linarith only [h958, hlam, p935_0]
                                      · rcases p935_3 (m.d 1 5) (by simp) with h960 | h960
                                        · linarith only [h3, h960, hlam]
                                        · rcases h3bigk with h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c
                                          · have p962_0 := h962c.1
                                            have p962_1 := h962c.2.1
                                            have p962_2 := h962c.2.2.1
                                            have p962_3 := h962c.2.2.2
                                            linarith only [hlam, p962_0]
                                          · have p962_0 := h962c.1
                                            have p962_1 := h962c.2.1
                                            have p962_2 := h962c.2.2.1
                                            have p962_3 := h962c.2.2.2
                                            linarith only [h687, hc13, hc34, hlam, hphi, p962_1]
                                          · have p962_0 := h962c.1
                                            have p962_1 := h962c.2.1
                                            have p962_2 := h962c.2.2.1
                                            have p962_3 := h962c.2.2.2
                                            linarith only [h4, hlam, p962_1]
                                          · have p962_0 := h962c.1
                                            have p962_1 := h962c.2.1
                                            have p962_2 := h962c.2.2.1
                                            have p962_3 := h962c.2.2.2
                                            linarith only [h687, hlam, p962_0]
                                          · have p962_0 := h962c.1
                                            have p962_1 := h962c.2.1
                                            have p962_2 := h962c.2.2.1
                                            have p962_3 := h962c.2.2.2
                                            linarith only [h687, h931, h934, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p962_1]
                                          · have p962_0 := h962c.1
                                            have p962_1 := h962c.2.1
                                            have p962_2 := h962c.2.2.1
                                            have p962_3 := h962c.2.2.2
                                            linarith only [h1, hlam, p962_0]
                                          · have p962_0 := h962c.1
                                            have p962_1 := h962c.2.1
                                            have p962_2 := h962c.2.2.1
                                            have p962_3 := h962c.2.2.2
                                            linarith only [hlam, p962_0]
                                          · have p962_0 := h962c.1
                                            have p962_1 := h962c.2.1
                                            have p962_2 := h962c.2.2.1
                                            have p962_3 := h962c.2.2.2
                                            linarith only [h922, hlam, p962_1]
                                          · have p962_0 := h962c.1
                                            have p962_1 := h962c.2.1
                                            have p962_2 := h962c.2.2.1
                                            have p962_3 := h962c.2.2.2
                                            linarith only [h927, hlam, p962_0]
                                          · have p962_0 := h962c.1
                                            have p962_1 := h962c.2.1
                                            have p962_2 := h962c.2.2.1
                                            have p962_3 := h962c.2.2.2
                                            linarith only [h927, h934, hc01, hc45, hlam, hphi, ht0b, ht5b, p935_1, p962_1]
                                          · have p962_0 := h962c.1
                                            have p962_1 := h962c.2.1
                                            have p962_2 := h962c.2.2.1
                                            have p962_3 := h962c.2.2.2
                                            rcases p962_3 (m.d 0 3) (by simp) with h973 | h973
                                            · linarith only [h4, h973, hlam]
                                            · rcases p962_3 (m.d 1 3) (by simp) with h975 | h975
                                              · linarith only [h922, h975, hlam]
                                              · rcases p962_3 (m.d 2 3) (by simp) with h977 | h977
                                                · rcases p962_3 (m.d 3 4) (by simp) with h978 | h978
                                                  · linarith only [h931, h978, hlam]
                                                  · linarith only [h687, h978, hlam]
                                                · linarith only [h4, h977, hlam]
                                          · have p962_0 := h962c.1
                                            have p962_1 := h962c.2.1
                                            have p962_2 := h962c.2.2.1
                                            have p962_3 := h962c.2.2.2
                                            rcases p962_3 (m.d 0 3) (by simp) with h982 | h982
                                            · linarith only [h4, h982, hlam]
                                            · linarith only [h1, h982, hlam]
                                          · have p962_0 := h962c.1
                                            have p962_1 := h962c.2.1
                                            have p962_2 := h962c.2.2.1
                                            have p962_3 := h962c.2.2.2
                                            linarith only [hlam, p962_0]
                                          · have p962_0 := h962c.1
                                            have p962_1 := h962c.2.1
                                            have p962_2 := h962c.2.2.1
                                            have p962_3 := h962c.2.2.2
                                            linarith only [h4, h687, hc02, hc23, hlam, hphi, p962_1]
                                          · have p962_0 := h962c.1
                                            have p962_1 := h962c.2.1
                                            have p962_2 := h962c.2.2.1
                                            have p962_3 := h962c.2.2.2
                                            linarith only [h0, h4, h687, h926, h931, h932, hlam, p962_2]
                                          · have p962_0 := h962c.1
                                            have p962_1 := h962c.2.1
                                            have p962_2 := h962c.2.2.1
                                            have p962_3 := h962c.2.2.2
                                            linarith only [h0, h4, h926, h931, h932, h934, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p962_1]
                                          · have p962_0 := h962c.1
                                            have p962_1 := h962c.2.1
                                            have p962_2 := h962c.2.2.1
                                            have p962_3 := h962c.2.2.2
                                            linarith only [h922, h926, h931, h932, h934, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p962_1]
                                          · have p962_0 := h962c.1
                                            have p962_1 := h962c.2.1
                                            have p962_2 := h962c.2.2.1
                                            have p962_3 := h962c.2.2.2
                                            linarith only [h931, hlam, p962_0]
                                          · have p962_0 := h962c.1
                                            have p962_1 := h962c.2.1
                                            have p962_2 := h962c.2.2.1
                                            have p962_3 := h962c.2.2.2
                                            linarith only [hlam, p962_0]
                                          · have p962_0 := h962c.1
                                            have p962_1 := h962c.2.1
                                            have p962_2 := h962c.2.2.1
                                            have p962_3 := h962c.2.2.2
                                            rcases p962_3 (m.d 0 3) (by simp) with h992 | h992
                                            · linarith only [h687, h992, hlam]
                                            · linarith only [h921, h992, hlam]
                                          · have p962_0 := h962c.1
                                            have p962_1 := h962c.2.1
                                            have p962_2 := h962c.2.2.1
                                            have p962_3 := h962c.2.2.2
                                            linarith only [h921, hlam, p962_0]
                                          · have p962_0 := h962c.1
                                            have p962_1 := h962c.2.1
                                            have p962_2 := h962c.2.2.1
                                            have p962_3 := h962c.2.2.2
                                            linarith only [h929, hlam, p962_0]
                                          · have p962_0 := h962c.1
                                            have p962_1 := h962c.2.1
                                            have p962_2 := h962c.2.2.1
                                            have p962_3 := h962c.2.2.2
                                            linarith only [h932, hlam, p962_0]
                                          · have p962_0 := h962c.1
                                            have p962_1 := h962c.2.1
                                            have p962_2 := h962c.2.2.1
                                            have p962_3 := h962c.2.2.2
                                            linarith only [h934, hlam, p962_0]
                                          · have p962_0 := h962c.1
                                            have p962_1 := h962c.2.1
                                            have p962_2 := h962c.2.2.1
                                            have p962_3 := h962c.2.2.2
                                            linarith only [hlam, p962_0]
                                · linarith only [h953, hlam, p935_0]
                              · have p935_0 := h935c.1
                                have p935_1 := h935c.2.1
                                have p935_2 := h935c.2.2.1
                                have p935_3 := h935c.2.2.2
                                rcases p935_3 (m.d 0 1) (by simp) with h1001 | h1001
                                · rcases p935_3 (m.d 1 2) (by simp) with h1002 | h1002
                                  · linarith only [h0, h1002, hlam]
                                  · linarith only [h1002, h926, hlam]
                                · linarith only [h1001, hlam, p935_0]
                              · have p935_0 := h935c.1
                                have p935_1 := h935c.2.1
                                have p935_2 := h935c.2.2.1
                                have p935_3 := h935c.2.2.2
                                linarith only [h0, hlam, p935_0]
                              · have p935_0 := h935c.1
                                have p935_1 := h935c.2.1
                                have p935_2 := h935c.2.2.1
                                have p935_3 := h935c.2.2.2
                                linarith only [hlam, p935_0]
                              · have p935_0 := h935c.1
                                have p935_1 := h935c.2.1
                                have p935_2 := h935c.2.2.1
                                have p935_3 := h935c.2.2.2
                                linarith only [h922, hlam, p935_0]
                              · have p935_0 := h935c.1
                                have p935_1 := h935c.2.1
                                have p935_2 := h935c.2.2.1
                                have p935_3 := h935c.2.2.2
                                linarith only [h924, hlam, p935_0]
                              · have p935_0 := h935c.1
                                have p935_1 := h935c.2.1
                                have p935_2 := h935c.2.2.1
                                have p935_3 := h935c.2.2.2
                                linarith only [h0, h4, h687, h931, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p935_1]
                              · have p935_0 := h935c.1
                                have p935_1 := h935c.2.1
                                have p935_2 := h935c.2.2.1
                                have p935_3 := h935c.2.2.2
                                linarith only [h1, hlam, p935_0]
                              · have p935_0 := h935c.1
                                have p935_1 := h935c.2.1
                                have p935_2 := h935c.2.2.1
                                have p935_3 := h935c.2.2.2
                                linarith only [h1, h687, h931, hc12, hc23, hlam, hphi, p935_1]
                              · have p935_0 := h935c.1
                                have p935_1 := h935c.2.1
                                have p935_2 := h935c.2.2.1
                                have p935_3 := h935c.2.2.2
                                linarith only [hlam, p935_0]
                              · have p935_0 := h935c.1
                                have p935_1 := h935c.2.1
                                have p935_2 := h935c.2.2.1
                                have p935_3 := h935c.2.2.2
                                linarith only [h927, hlam, p935_1]
                              · have p935_0 := h935c.1
                                have p935_1 := h935c.2.1
                                have p935_2 := h935c.2.2.1
                                have p935_3 := h935c.2.2.2
                                linarith only [h1, h687, h926, h931, h932, h934, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p935_1]
                              · have p935_0 := h935c.1
                                have p935_1 := h935c.2.1
                                have p935_2 := h935c.2.2.1
                                have p935_3 := h935c.2.2.2
                                linarith only [h2, hlam, p935_0]
                              · have p935_0 := h935c.1
                                have p935_1 := h935c.2.1
                                have p935_2 := h935c.2.2.1
                                have p935_3 := h935c.2.2.2
                                linarith only [h2, h926, h932, h934, hc01, hc45, hlam, hphi, ht0b, ht5b, p935_1]
                              · have p935_0 := h935c.1
                                have p935_1 := h935c.2.1
                                have p935_2 := h935c.2.2.1
                                have p935_3 := h935c.2.2.2
                                linarith only [h2, h687, h922, h926, h931, h932, h934, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p935_1]
                              · have p935_0 := h935c.1
                                have p935_1 := h935c.2.1
                                have p935_2 := h935c.2.2.1
                                have p935_3 := h935c.2.2.2
                                linarith only [hlam, p935_0]
                              · have p935_0 := h935c.1
                                have p935_1 := h935c.2.1
                                have p935_2 := h935c.2.2.1
                                have p935_3 := h935c.2.2.2
                                rcases p935_3 (m.d 0 1) (by simp) with h1020 | h1020
                                · rcases p935_3 (m.d 1 2) (by simp) with h1021 | h1021
                                  · linarith only [h1021, h924, hlam]
                                  · linarith only [h1021, h926, hlam]
                                · linarith only [h1020, h3, hlam]
                              · have p935_0 := h935c.1
                                have p935_1 := h935c.2.1
                                have p935_2 := h935c.2.2.1
                                have p935_3 := h935c.2.2.2
                                linarith only [h3, hlam, p935_0]
                              · have p935_0 := h935c.1
                                have p935_1 := h935c.2.1
                                have p935_2 := h935c.2.2.1
                                have p935_3 := h935c.2.2.2
                                linarith only [h926, hlam, p935_1]
                              · have p935_0 := h935c.1
                                have p935_1 := h935c.2.1
                                have p935_2 := h935c.2.2.1
                                have p935_3 := h935c.2.2.2
                                linarith only [h929, hlam, p935_0]
                              · have p935_0 := h935c.1
                                have p935_1 := h935c.2.1
                                have p935_2 := h935c.2.2.1
                                have p935_3 := h935c.2.2.2
                                linarith only [h930, hlam, p935_0]
                              · have p935_0 := h935c.1
                                have p935_1 := h935c.2.1
                                have p935_2 := h935c.2.2.1
                                have p935_3 := h935c.2.2.2
                                linarith only [hlam, p935_0]
                            · linarith only [h687, h934, hc03, hlam, hphi, ht34, ht45, u5elo4]
                          · linarith only [h3, h687, h930, h931, h933, hc03, hlam, hphi, ht34, ht45, u5elo0]
                        · linarith only [h1, h687, h922, h926, h931, h932, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1033 | h1033
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1034 | h1034
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1035 | h1035
                            · rcases h1bigk with h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c
                              · have p1036_0 := h1036c.1
                                have p1036_1 := h1036c.2.1
                                have p1036_2 := h1036c.2.2.1
                                have p1036_3 := h1036c.2.2.2
                                linarith only [hlam, p1036_0]
                              · have p1036_0 := h1036c.1
                                have p1036_1 := h1036c.2.1
                                have p1036_2 := h1036c.2.2.1
                                have p1036_3 := h1036c.2.2.2
                                rcases p1036_3 (m.d 0 1) (by simp) with h1038 | h1038
                                · rcases p1036_3 (m.d 1 2) (by simp) with h1039 | h1039
                                  · linarith only [h1039, hlam, p1036_0]
                                  · rcases p1036_3 (m.d 1 3) (by simp) with h1041 | h1041
                                    · linarith only [h1, h1041, hlam]
                                    · linarith only [h1041, h922, hlam]
                                · linarith only [h1038, hlam, p1036_0]
                              · have p1036_0 := h1036c.1
                                have p1036_1 := h1036c.2.1
                                have p1036_2 := h1036c.2.2.1
                                have p1036_3 := h1036c.2.2.2
                                rcases p1036_3 (m.d 0 1) (by simp) with h1045 | h1045
                                · rcases p1036_3 (m.d 1 2) (by simp) with h1046 | h1046
                                  · linarith only [h0, h1046, hlam]
                                  · rcases p1036_3 (m.d 1 3) (by simp) with h1048 | h1048
                                    · linarith only [h1048, hlam, p1036_0]
                                    · rcases p1036_3 (m.d 1 4) (by simp) with h1050 | h1050
                                      · linarith only [h1050, h2, hlam]
                                      · linarith only [h1050, h927, hlam]
                                · linarith only [h1045, hlam, p1036_0]
                              · have p1036_0 := h1036c.1
                                have p1036_1 := h1036c.2.1
                                have p1036_2 := h1036c.2.2.1
                                have p1036_3 := h1036c.2.2.2
                                rcases p1036_3 (m.d 0 1) (by simp) with h1054 | h1054
                                · rcases p1036_3 (m.d 1 2) (by simp) with h1055 | h1055
                                  · linarith only [h0, h1055, hlam]
                                  · rcases p1036_3 (m.d 1 3) (by simp) with h1057 | h1057
                                    · linarith only [h1, h1057, hlam]
                                    · rcases p1036_3 (m.d 1 4) (by simp) with h1059 | h1059
                                      · linarith only [h1059, hlam, p1036_0]
                                      · rcases p1036_3 (m.d 1 5) (by simp) with h1061 | h1061
                                        · linarith only [h1061, h3, hlam]
                                        · rcases h3bigk with h1063c | h1063c | h1063c | h1063c | h1063c | h1063c | h1063c | h1063c | h1063c | h1063c | h1063c | h1063c | h1063c | h1063c | h1063c | h1063c | h1063c | h1063c | h1063c | h1063c | h1063c | h1063c | h1063c | h1063c | h1063c
                                          · have p1063_0 := h1063c.1
                                            have p1063_1 := h1063c.2.1
                                            have p1063_2 := h1063c.2.2.1
                                            have p1063_3 := h1063c.2.2.2
                                            linarith only [hlam, p1063_0]
                                          · have p1063_0 := h1063c.1
                                            have p1063_1 := h1063c.2.1
                                            have p1063_2 := h1063c.2.2.1
                                            have p1063_3 := h1063c.2.2.2
                                            linarith only [h1033, h1035, h4, h922, h926, h931, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1063_1]
                                          · have p1063_0 := h1063c.1
                                            have p1063_1 := h1063c.2.1
                                            have p1063_2 := h1063c.2.2.1
                                            have p1063_3 := h1063c.2.2.2
                                            linarith only [h4, hlam, p1063_1]
                                          · have p1063_0 := h1063c.1
                                            have p1063_1 := h1063c.2.1
                                            have p1063_2 := h1063c.2.2.1
                                            have p1063_3 := h1063c.2.2.2
                                            linarith only [h687, hlam, p1063_0]
                                          · have p1063_0 := h1063c.1
                                            have p1063_1 := h1063c.2.1
                                            have p1063_2 := h1063c.2.2.1
                                            have p1063_3 := h1063c.2.2.2
                                            rcases p1063_3 (m.d 0 3) (by simp) with h1068 | h1068
                                            · rcases p1063_3 (m.d 1 3) (by simp) with h1069 | h1069
                                              · linarith only [h1, h1069, hlam]
                                              · linarith only [h1069, h929, hlam]
                                            · linarith only [h1068, hlam, p1063_0]
                                          · have p1063_0 := h1063c.1
                                            have p1063_1 := h1063c.2.1
                                            have p1063_2 := h1063c.2.2.1
                                            have p1063_3 := h1063c.2.2.2
                                            linarith only [h1, hlam, p1063_0]
                                          · have p1063_0 := h1063c.1
                                            have p1063_1 := h1063c.2.1
                                            have p1063_2 := h1063c.2.2.1
                                            have p1063_3 := h1063c.2.2.2
                                            linarith only [hlam, p1063_0]
                                          · have p1063_0 := h1063c.1
                                            have p1063_1 := h1063c.2.1
                                            have p1063_2 := h1063c.2.2.1
                                            have p1063_3 := h1063c.2.2.2
                                            linarith only [h922, hlam, p1063_1]
                                          · have p1063_0 := h1063c.1
                                            have p1063_1 := h1063c.2.1
                                            have p1063_2 := h1063c.2.2.1
                                            have p1063_3 := h1063c.2.2.2
                                            linarith only [h927, hlam, p1063_0]
                                          · have p1063_0 := h1063c.1
                                            have p1063_1 := h1063c.2.1
                                            have p1063_2 := h1063c.2.2.1
                                            have p1063_3 := h1063c.2.2.2
                                            linarith only [h1035, h927, hc01, hc45, hlam, hphi, ht0b, ht5b, p1036_1, p1063_1]
                                          · have p1063_0 := h1063c.1
                                            have p1063_1 := h1063c.2.1
                                            have p1063_2 := h1063c.2.2.1
                                            have p1063_3 := h1063c.2.2.2
                                            linarith only [h931, hc03, hc34, hlam, hphi, p1063_1]
                                          · have p1063_0 := h1063c.1
                                            have p1063_1 := h1063c.2.1
                                            have p1063_2 := h1063c.2.2.1
                                            have p1063_3 := h1063c.2.2.2
                                            linarith only [h931, hc13, hc34, hlam, hphi, p1063_1]
                                          · have p1063_0 := h1063c.1
                                            have p1063_1 := h1063c.2.1
                                            have p1063_2 := h1063c.2.2.1
                                            have p1063_3 := h1063c.2.2.2
                                            linarith only [hlam, p1063_0]
                                          · have p1063_0 := h1063c.1
                                            have p1063_1 := h1063c.2.1
                                            have p1063_2 := h1063c.2.2.1
                                            have p1063_3 := h1063c.2.2.2
                                            linarith only [h931, hlam, p1063_0]
                                          · have p1063_0 := h1063c.1
                                            have p1063_1 := h1063c.2.1
                                            have p1063_2 := h1063c.2.2.1
                                            have p1063_3 := h1063c.2.2.2
                                            rcases p1063_3 (m.d 0 3) (by simp) with h1082 | h1082
                                            · linarith only [h1082, h4, hlam]
                                            · linarith only [h1082, h921, hlam]
                                          · have p1063_0 := h1063c.1
                                            have p1063_1 := h1063c.2.1
                                            have p1063_2 := h1063c.2.2.1
                                            have p1063_3 := h1063c.2.2.2
                                            rcases p1063_3 (m.d 0 3) (by simp) with h1085 | h1085
                                            · linarith only [h1085, hlam, p1063_0]
                                            · rcases p1063_3 (m.d 1 3) (by simp) with h1087 | h1087
                                              · linarith only [h1087, h927, hlam]
                                              · rcases p1063_3 (m.d 2 3) (by simp) with h1089 | h1089
                                                · linarith only [h1089, h931, hlam]
                                                · linarith only [h1089, h4, hlam]
                                          · have p1063_0 := h1063c.1
                                            have p1063_1 := h1063c.2.1
                                            have p1063_2 := h1063c.2.2.1
                                            have p1063_3 := h1063c.2.2.2
                                            rcases p1063_3 (m.d 0 3) (by simp) with h1092 | h1092
                                            · linarith only [h1092, h687, hlam]
                                            · linarith only [h1, h1092, hlam]
                                          · have p1063_0 := h1063c.1
                                            have p1063_1 := h1063c.2.1
                                            have p1063_2 := h1063c.2.2.1
                                            have p1063_3 := h1063c.2.2.2
                                            linarith only [h0, h1033, h1035, h4, h926, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1063_1]
                                          · have p1063_0 := h1063c.1
                                            have p1063_1 := h1063c.2.1
                                            have p1063_2 := h1063c.2.2.1
                                            have p1063_3 := h1063c.2.2.2
                                            linarith only [hlam, p1063_0]
                                          · have p1063_0 := h1063c.1
                                            have p1063_1 := h1063c.2.1
                                            have p1063_2 := h1063c.2.2.1
                                            have p1063_3 := h1063c.2.2.2
                                            linarith only [h0, h1033, h4, h926, h931, hlam, p1063_2]
                                          · have p1063_0 := h1063c.1
                                            have p1063_1 := h1063c.2.1
                                            have p1063_2 := h1063c.2.2.1
                                            have p1063_3 := h1063c.2.2.2
                                            linarith only [h921, hlam, p1063_0]
                                          · have p1063_0 := h1063c.1
                                            have p1063_1 := h1063c.2.1
                                            have p1063_2 := h1063c.2.2.1
                                            have p1063_3 := h1063c.2.2.2
                                            linarith only [h929, hlam, p1063_0]
                                          · have p1063_0 := h1063c.1
                                            have p1063_1 := h1063c.2.1
                                            have p1063_2 := h1063c.2.2.1
                                            have p1063_3 := h1063c.2.2.2
                                            linarith only [h1033, hlam, p1063_0]
                                          · have p1063_0 := h1063c.1
                                            have p1063_1 := h1063c.2.1
                                            have p1063_2 := h1063c.2.2.1
                                            have p1063_3 := h1063c.2.2.2
                                            linarith only [h1035, hlam, p1063_0]
                                          · have p1063_0 := h1063c.1
                                            have p1063_1 := h1063c.2.1
                                            have p1063_2 := h1063c.2.2.1
                                            have p1063_3 := h1063c.2.2.2
                                            linarith only [hlam, p1063_0]
                                · linarith only [h1054, hlam, p1036_0]
                              · have p1036_0 := h1036c.1
                                have p1036_1 := h1036c.2.1
                                have p1036_2 := h1036c.2.2.1
                                have p1036_3 := h1036c.2.2.2
                                rcases p1036_3 (m.d 0 1) (by simp) with h1104 | h1104
                                · rcases p1036_3 (m.d 1 2) (by simp) with h1105 | h1105
                                  · linarith only [h0, h1105, hlam]
                                  · linarith only [h1105, h926, hlam]
                                · linarith only [h1104, hlam, p1036_0]
                              · have p1036_0 := h1036c.1
                                have p1036_1 := h1036c.2.1
                                have p1036_2 := h1036c.2.2.1
                                have p1036_3 := h1036c.2.2.2
                                linarith only [h0, hlam, p1036_0]
                              · have p1036_0 := h1036c.1
                                have p1036_1 := h1036c.2.1
                                have p1036_2 := h1036c.2.2.1
                                have p1036_3 := h1036c.2.2.2
                                linarith only [hlam, p1036_0]
                              · have p1036_0 := h1036c.1
                                have p1036_1 := h1036c.2.1
                                have p1036_2 := h1036c.2.2.1
                                have p1036_3 := h1036c.2.2.2
                                linarith only [h922, hlam, p1036_0]
                              · have p1036_0 := h1036c.1
                                have p1036_1 := h1036c.2.1
                                have p1036_2 := h1036c.2.2.1
                                have p1036_3 := h1036c.2.2.2
                                linarith only [h924, hlam, p1036_0]
                              · have p1036_0 := h1036c.1
                                have p1036_1 := h1036c.2.1
                                have p1036_2 := h1036c.2.2.1
                                have p1036_3 := h1036c.2.2.2
                                linarith only [h0, h4, h931, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1036_1]
                              · have p1036_0 := h1036c.1
                                have p1036_1 := h1036c.2.1
                                have p1036_2 := h1036c.2.2.1
                                have p1036_3 := h1036c.2.2.2
                                linarith only [h1, hlam, p1036_0]
                              · have p1036_0 := h1036c.1
                                have p1036_1 := h1036c.2.1
                                have p1036_2 := h1036c.2.2.1
                                have p1036_3 := h1036c.2.2.2
                                linarith only [h1, h926, hc01, hc25, hlam, hphi, ht0b, ht5b, p1036_1]
                              · have p1036_0 := h1036c.1
                                have p1036_1 := h1036c.2.1
                                have p1036_2 := h1036c.2.2.1
                                have p1036_3 := h1036c.2.2.2
                                linarith only [hlam, p1036_0]
                              · have p1036_0 := h1036c.1
                                have p1036_1 := h1036c.2.1
                                have p1036_2 := h1036c.2.2.1
                                have p1036_3 := h1036c.2.2.2
                                linarith only [h927, hlam, p1036_1]
                              · have p1036_0 := h1036c.1
                                have p1036_1 := h1036c.2.1
                                have p1036_2 := h1036c.2.2.1
                                have p1036_3 := h1036c.2.2.2
                                rcases p1036_3 (m.d 0 1) (by simp) with h1118 | h1118
                                · rcases p1036_3 (m.d 1 2) (by simp) with h1119 | h1119
                                  · linarith only [h1119, h922, hlam]
                                  · linarith only [h1119, h926, hlam]
                                · linarith only [h1118, h3, hlam]
                              · have p1036_0 := h1036c.1
                                have p1036_1 := h1036c.2.1
                                have p1036_2 := h1036c.2.2.1
                                have p1036_3 := h1036c.2.2.2
                                linarith only [h2, hlam, p1036_0]
                              · have p1036_0 := h1036c.1
                                have p1036_1 := h1036c.2.1
                                have p1036_2 := h1036c.2.2.1
                                have p1036_3 := h1036c.2.2.2
                                linarith only [h1033, h1035, h2, h926, hc01, hc45, hlam, hphi, ht0b, ht5b, p1036_1]
                              · have p1036_0 := h1036c.1
                                have p1036_1 := h1036c.2.1
                                have p1036_2 := h1036c.2.2.1
                                have p1036_3 := h1036c.2.2.2
                                linarith only [h1033, h1035, h2, h922, h926, hc01, hc45, hlam, hphi, ht0b, ht5b, p1036_1]
                              · have p1036_0 := h1036c.1
                                have p1036_1 := h1036c.2.1
                                have p1036_2 := h1036c.2.2.1
                                have p1036_3 := h1036c.2.2.2
                                linarith only [hlam, p1036_0]
                              · have p1036_0 := h1036c.1
                                have p1036_1 := h1036c.2.1
                                have p1036_2 := h1036c.2.2.1
                                have p1036_3 := h1036c.2.2.2
                                rcases p1036_3 (m.d 0 1) (by simp) with h1127 | h1127
                                · rcases p1036_3 (m.d 1 2) (by simp) with h1128 | h1128
                                  · linarith only [h1128, h924, hlam]
                                  · linarith only [h1128, h926, hlam]
                                · linarith only [h1127, h3, hlam]
                              · have p1036_0 := h1036c.1
                                have p1036_1 := h1036c.2.1
                                have p1036_2 := h1036c.2.2.1
                                have p1036_3 := h1036c.2.2.2
                                linarith only [h3, hlam, p1036_0]
                              · have p1036_0 := h1036c.1
                                have p1036_1 := h1036c.2.1
                                have p1036_2 := h1036c.2.2.1
                                have p1036_3 := h1036c.2.2.2
                                linarith only [h926, hlam, p1036_1]
                              · have p1036_0 := h1036c.1
                                have p1036_1 := h1036c.2.1
                                have p1036_2 := h1036c.2.2.1
                                have p1036_3 := h1036c.2.2.2
                                linarith only [h929, hlam, p1036_0]
                              · have p1036_0 := h1036c.1
                                have p1036_1 := h1036c.2.1
                                have p1036_2 := h1036c.2.2.1
                                have p1036_3 := h1036c.2.2.2
                                linarith only [h930, hlam, p1036_0]
                              · have p1036_0 := h1036c.1
                                have p1036_1 := h1036c.2.1
                                have p1036_2 := h1036c.2.2.1
                                have p1036_3 := h1036c.2.2.2
                                linarith only [hlam, p1036_0]
                            · linarith only [h0, h1033, h1035, h4, h926, h931, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h1034, h560, hc04, hlam, hphi, ht45, u5elo4]
                        · linarith only [h1033, h4, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · linarith only [h922, h926, h927, h930, hc25, hlam, hphi, u5elo4]
                  · linarith only [h922, h926, h929, hc25, hlam, hphi, u5elo3]
              · linarith only [h926, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h4, h686, h921, hc25, hlam, hphi, u5elo3]
    · linarith only [h686, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]

set_option maxHeartbeats 5346000 in
set_option maxHeartbeats 5346000 in
theorem r1l7_11_13_25_L_I_L_I_H_L_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_11_13_25_L_I_L_I_H_L_x0_x0_x0_x0_x0 m hb1 hb3 hb5 h0 h1 h2 h3 h4
  · exact r1l7_11_13_25_L_I_L_I_H_L_x0_x0_x0_x0_x1 m hb1 hb3 hb5 h0 h1 h2 h3 h4

set_option maxHeartbeats 5346000 in
set_option maxHeartbeats 5346000 in
theorem r1l7_11_13_25_L_I_L_I_H_L_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [h3, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

set_option maxHeartbeats 5346000 in
set_option maxHeartbeats 5346000 in
theorem r1l7_11_13_25_L_I_L_I_H_L_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_11_13_25_L_I_L_I_H_L_x0_x0_x0_x0 m hb1 hb3 hb5 h0 h1 h2 h3
  · exact r1l7_11_13_25_L_I_L_I_H_L_x0_x0_x0_x1 m hb1 hb3 hb5 h0 h1 h2 h3

set_option maxHeartbeats 5346000 in
set_option maxHeartbeats 5346000 in
theorem r1l7_11_13_25_L_I_L_I_H_L_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1146 | h1146
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1147 | h1147
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1148 | h1148
      · linarith only [h0, h1148, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1150 | h1150
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1151 | h1151
          · linarith only [h1, h1151, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1153 | h1153
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1154 | h1154
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1155 | h1155
                · linarith only [h0, h1148, h1155, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1157 | h1157
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1158 | h1158
                    · linarith only [h1, h1151, h1158, h2, hlam]
                    · linarith only [h0, h1154, h1158, h2, hc23, hc34, hlam, hphi]
                  · linarith only [h1154, h1157, hc23, hlam, hphi, ht34, ht45, u5elo2]
              · linarith only [h1147, h1148, h1154, hc12, hc24, hlam, hphi]
            · linarith only [h1153, hc03, hlam, hphi, ht34, ht45, u5elo3]
        · linarith only [h1150, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1165 | h1165
      · linarith only [h0, h1165, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1167 | h1167
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1168 | h1168
          · linarith only [h1, h1168, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1170 | h1170
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1171 | h1171
              · linarith only [h0, h1147, h1171, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1173 | h1173
                · linarith only [h0, h1165, h1173, h2, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1175 | h1175
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1176 | h1176
                    · linarith only [h1, h1168, h1176, h2, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1178 | h1178
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1179 | h1179
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1180 | h1180
                          · linarith only [h1, h1171, h1176, h1180, h2, hc12, hc23, hlam, hphi]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1182 | h1182
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1183 | h1183
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1184 | h1184
                                · rcases h1bigk with h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c
                                  · have p1185_0 := h1185c.1
                                    have p1185_1 := h1185c.2.1
                                    have p1185_2 := h1185c.2.2.1
                                    have p1185_3 := h1185c.2.2.2
                                    linarith only [hlam, p1185_0]
                                  · have p1185_0 := h1185c.1
                                    have p1185_1 := h1185c.2.1
                                    have p1185_2 := h1185c.2.2.1
                                    have p1185_3 := h1185c.2.2.2
                                    linarith only [h1173, h1175, h1180, h1182, h1184, h2, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1185_1]
                                  · have p1185_0 := h1185c.1
                                    have p1185_1 := h1185c.2.1
                                    have p1185_2 := h1185c.2.2.1
                                    have p1185_3 := h1185c.2.2.2
                                    linarith only [h1171, h1173, h1175, h1180, h1182, h1184, h2, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1185_1]
                                  · have p1185_0 := h1185c.1
                                    have p1185_1 := h1185c.2.1
                                    have p1185_2 := h1185c.2.2.1
                                    have p1185_3 := h1185c.2.2.2
                                    linarith only [h2, hlam, p1185_0]
                                  · have p1185_0 := h1185c.1
                                    have p1185_1 := h1185c.2.1
                                    have p1185_2 := h1185c.2.2.1
                                    have p1185_3 := h1185c.2.2.2
                                    rcases p1185_3 (m.d 0 1) (by simp) with h1190 | h1190
                                    · rcases p1185_3 (m.d 1 2) (by simp) with h1191 | h1191
                                      · linarith only [h0, h1191, hlam]
                                      · linarith only [h1175, h1191, hlam]
                                    · linarith only [h1190, hlam, p1185_0]
                                  · have p1185_0 := h1185c.1
                                    have p1185_1 := h1185c.2.1
                                    have p1185_2 := h1185c.2.2.1
                                    have p1185_3 := h1185c.2.2.2
                                    linarith only [h0, hlam, p1185_0]
                                  · have p1185_0 := h1185c.1
                                    have p1185_1 := h1185c.2.1
                                    have p1185_2 := h1185c.2.2.1
                                    have p1185_3 := h1185c.2.2.2
                                    linarith only [hlam, p1185_0]
                                  · have p1185_0 := h1185c.1
                                    have p1185_1 := h1185c.2.1
                                    have p1185_2 := h1185c.2.2.1
                                    have p1185_3 := h1185c.2.2.2
                                    linarith only [h1171, hlam, p1185_0]
                                  · have p1185_0 := h1185c.1
                                    have p1185_1 := h1185c.2.1
                                    have p1185_2 := h1185c.2.2.1
                                    have p1185_3 := h1185c.2.2.2
                                    linarith only [h1173, hlam, p1185_0]
                                  · have p1185_0 := h1185c.1
                                    have p1185_1 := h1185c.2.1
                                    have p1185_2 := h1185c.2.2.1
                                    have p1185_3 := h1185c.2.2.2
                                    linarith only [h0, h1173, h1180, h2, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1185_1]
                                  · have p1185_0 := h1185c.1
                                    have p1185_1 := h1185c.2.1
                                    have p1185_2 := h1185c.2.2.1
                                    have p1185_3 := h1185c.2.2.2
                                    linarith only [h1, hlam, p1185_0]
                                  · have p1185_0 := h1185c.1
                                    have p1185_1 := h1185c.2.1
                                    have p1185_2 := h1185c.2.2.1
                                    have p1185_3 := h1185c.2.2.2
                                    linarith only [h1, h1173, h1180, h2, hc12, hc34, hlam, hphi, ht23, p1185_1]
                                  · have p1185_0 := h1185c.1
                                    have p1185_1 := h1185c.2.1
                                    have p1185_2 := h1185c.2.2.1
                                    have p1185_3 := h1185c.2.2.2
                                    linarith only [hlam, p1185_0]
                                  · have p1185_0 := h1185c.1
                                    have p1185_1 := h1185c.2.1
                                    have p1185_2 := h1185c.2.2.1
                                    have p1185_3 := h1185c.2.2.2
                                    linarith only [h1176, hlam, p1185_1]
                                  · have p1185_0 := h1185c.1
                                    have p1185_1 := h1185c.2.1
                                    have p1185_2 := h1185c.2.2.1
                                    have p1185_3 := h1185c.2.2.2
                                    linarith only [h1, h1173, h1175, h1180, h1182, h1184, h2, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1185_1]
                                  · have p1185_0 := h1185c.1
                                    have p1185_1 := h1185c.2.1
                                    have p1185_2 := h1185c.2.2.1
                                    have p1185_3 := h1185c.2.2.2
                                    linarith only [h1, h1173, h1180, hc13, hc34, hlam, hphi, p1185_1]
                                  · have p1185_0 := h1185c.1
                                    have p1185_1 := h1185c.2.1
                                    have p1185_2 := h1185c.2.2.1
                                    have p1185_3 := h1185c.2.2.2
                                    rcases p1185_3 (m.d 0 1) (by simp) with h1206 | h1206
                                    · linarith only [h1206, h2, hlam]
                                    · linarith only [h0, h1206, hlam]
                                  · have p1185_0 := h1185c.1
                                    have p1185_1 := h1185c.2.1
                                    have p1185_2 := h1185c.2.2.1
                                    have p1185_3 := h1185c.2.2.2
                                    rcases p1185_3 (m.d 0 1) (by simp) with h1209 | h1209
                                    · linarith only [h1209, h2, hlam]
                                    · linarith only [h1, h1209, hlam]
                                  · have p1185_0 := h1185c.1
                                    have p1185_1 := h1185c.2.1
                                    have p1185_2 := h1185c.2.2.1
                                    have p1185_3 := h1185c.2.2.2
                                    linarith only [hlam, p1185_0]
                                  · have p1185_0 := h1185c.1
                                    have p1185_1 := h1185c.2.1
                                    have p1185_2 := h1185c.2.2.1
                                    have p1185_3 := h1185c.2.2.2
                                    rcases p1185_3 (m.d 0 1) (by simp) with h1213 | h1213
                                    · linarith only [h1213, h2, hlam]
                                    · linarith only [h1146, h1213, hlam]
                                  · have p1185_0 := h1185c.1
                                    have p1185_1 := h1185c.2.1
                                    have p1185_2 := h1185c.2.2.1
                                    have p1185_3 := h1185c.2.2.2
                                    linarith only [h1146, hlam, p1185_0]
                                  · have p1185_0 := h1185c.1
                                    have p1185_1 := h1185c.2.1
                                    have p1185_2 := h1185c.2.2.1
                                    have p1185_3 := h1185c.2.2.2
                                    linarith only [h1175, hlam, p1185_1]
                                  · have p1185_0 := h1185c.1
                                    have p1185_1 := h1185c.2.1
                                    have p1185_2 := h1185c.2.2.1
                                    have p1185_3 := h1185c.2.2.2
                                    linarith only [h1178, hlam, p1185_0]
                                  · have p1185_0 := h1185c.1
                                    have p1185_1 := h1185c.2.1
                                    have p1185_2 := h1185c.2.2.1
                                    have p1185_3 := h1185c.2.2.2
                                    linarith only [h1179, hlam, p1185_0]
                                  · have p1185_0 := h1185c.1
                                    have p1185_1 := h1185c.2.1
                                    have p1185_2 := h1185c.2.2.1
                                    have p1185_3 := h1185c.2.2.2
                                    linarith only [hlam, p1185_0]
                                · linarith only [h1180, h1184, hc23, hlam, hphi, ht34, ht45, u5elo4]
                              · linarith only [h1, h1171, h1173, h1175, h1179, h1183, h2, hc15, hc25, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h1147, h1182, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                        · linarith only [h1, h1171, h1175, h1179, h2, hc25, hlam, hphi, u5elo4]
                      · linarith only [h1171, h1175, h1178, hc25, hlam, hphi, u5elo3]
                  · linarith only [h1175, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h1147, h1167, h1170, hc25, hlam, hphi, u5elo3]
        · linarith only [h1167, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
  · linarith only [h1146, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

set_option maxHeartbeats 5346000 in
set_option maxHeartbeats 5346000 in
theorem r1l7_11_13_25_L_I_L_I_H_L_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_11_13_25_L_I_L_I_H_L_x0_x0_x0 m hb1 hb3 hb5 h0 h1 h2
  · exact r1l7_11_13_25_L_I_L_I_H_L_x0_x0_x1 m hb1 hb3 hb5 h0 h1 h2

end R2N4
