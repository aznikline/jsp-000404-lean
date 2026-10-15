import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_72S4

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h7 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h0ehi := hb0.1
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 1 2 4 (by decide) (by decide) with h574 | h574
  · rcases m.htr 1 3 4 (by decide) (by decide) with h575 | h575
    · rcases m.htr 1 3 5 (by decide) (by decide) with h576 | h576
      · rcases m.htr 1 4 5 (by decide) (by decide) with h577 | h577
        · rcases m.htr 2 3 4 (by decide) (by decide) with h578 | h578
          · rcases m.htr 2 3 5 (by decide) (by decide) with h579 | h579
            · rcases m.htr 2 4 5 (by decide) (by decide) with h580 | h580
              · linarith only [h0, h3, h574, h580, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h3, h574, h577, h580, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h574, h576, h577, h579, h8, hc13, hlam, hphi, u1ehi4]
          · linarith only [h574, h577, h578, h8, hc34, hlam, hphi, ht12, ht23, u1ehi4]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h585 | h585
          · rcases m.htr 2 3 5 (by decide) (by decide) with h586 | h586
            · rcases m.htr 2 4 5 (by decide) (by decide) with h587 | h587
              · linarith only [h0, h3, h574, h587, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h589 | h589
                · linarith only [h0, h3, h574, h577, h585, h589, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                · rcases h3bigk with h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c
                  · have p591_0 := h591c.1
                    have p591_1 := h591c.2.1
                    have p591_2 := h591c.2.2.1
                    have p591_3 := h591c.2.2.2
                    linarith only [hlam, p591_0]
                  · have p591_0 := h591c.1
                    have p591_1 := h591c.2.1
                    have p591_2 := h591c.2.2.1
                    have p591_3 := h591c.2.2.2
                    rcases p591_3 (m.d 0 3) (by simp) with h593 | h593
                    · rcases p591_3 (m.d 1 3) (by simp) with h594 | h594
                      · linarith only [h1, h594, hlam]
                      · rcases p591_3 (m.d 2 3) (by simp) with h596 | h596
                        · linarith only [h3, h596, hlam]
                        · linarith only [h596, h8, hlam]
                    · linarith only [h1, h593, hlam]
                  · have p591_0 := h591c.1
                    have p591_1 := h591c.2.1
                    have p591_2 := h591c.2.2.1
                    have p591_3 := h591c.2.2.2
                    linarith only [h0, h3, h574, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p591_1]
                  · have p591_0 := h591c.1
                    have p591_1 := h591c.2.1
                    have p591_2 := h591c.2.2.1
                    have p591_3 := h591c.2.2.2
                    rcases p591_3 (m.d 0 3) (by simp) with h601 | h601
                    · rcases p591_3 (m.d 1 3) (by simp) with h602 | h602
                      · linarith only [h1, h602, hlam]
                      · linarith only [h575, h602, hlam]
                    · linarith only [h601, hlam, p591_0]
                  · have p591_0 := h591c.1
                    have p591_1 := h591c.2.1
                    have p591_2 := h591c.2.2.1
                    have p591_3 := h591c.2.2.2
                    rcases p591_3 (m.d 0 3) (by simp) with h606 | h606
                    · rcases p591_3 (m.d 1 3) (by simp) with h607 | h607
                      · linarith only [h1, h607, hlam]
                      · linarith only [h576, h607, hlam]
                    · linarith only [h606, hlam, p591_0]
                  · have p591_0 := h591c.1
                    have p591_1 := h591c.2.1
                    have p591_2 := h591c.2.2.1
                    have p591_3 := h591c.2.2.2
                    linarith only [h1, hlam, p591_0]
                  · have p591_0 := h591c.1
                    have p591_1 := h591c.2.1
                    have p591_2 := h591c.2.2.1
                    have p591_3 := h591c.2.2.2
                    linarith only [hlam, p591_0]
                  · have p591_0 := h591c.1
                    have p591_1 := h591c.2.1
                    have p591_2 := h591c.2.2.1
                    have p591_3 := h591c.2.2.2
                    linarith only [h8, hlam, p591_1]
                  · have p591_0 := h591c.1
                    have p591_1 := h591c.2.1
                    have p591_2 := h591c.2.2.1
                    have p591_3 := h591c.2.2.2
                    rcases p591_3 (m.d 0 3) (by simp) with h614 | h614
                    · rcases p591_3 (m.d 1 3) (by simp) with h615 | h615
                      · rcases p591_3 (m.d 2 3) (by simp) with h616 | h616
                        · rcases p591_3 (m.d 3 4) (by simp) with h617 | h617
                          · linarith only [h617, hlam, p591_0]
                          · rcases p591_3 (m.d 3 5) (by simp) with h619 | h619
                            · linarith only [h576, h619, hlam]
                            · linarith only [h589, h619, hlam]
                        · linarith only [h585, h616, hlam]
                      · linarith only [h615, hlam, p591_0]
                    · linarith only [h5, h614, hlam]
                  · have p591_0 := h591c.1
                    have p591_1 := h591c.2.1
                    have p591_2 := h591c.2.2.1
                    have p591_3 := h591c.2.2.2
                    rcases p591_3 (m.d 0 3) (by simp) with h625 | h625
                    · rcases p591_3 (m.d 1 3) (by simp) with h626 | h626
                      · rcases p591_3 (m.d 2 3) (by simp) with h627 | h627
                        · rcases p591_3 (m.d 3 4) (by simp) with h628 | h628
                          · linarith only [h575, h628, hlam]
                          · rcases p591_3 (m.d 3 5) (by simp) with h630 | h630
                            · linarith only [h630, hlam, p591_0]
                            · rcases h4bigk with h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c
                              · have p632_0 := h632c.1
                                have p632_1 := h632c.2.1
                                have p632_2 := h632c.2.2.1
                                have p632_3 := h632c.2.2.2
                                linarith only [hlam, p632_0]
                              · have p632_0 := h632c.1
                                have p632_1 := h632c.2.1
                                have p632_2 := h632c.2.2.1
                                have p632_3 := h632c.2.2.2
                                rcases p632_3 (m.d 0 4) (by simp) with h634 | h634
                                · rcases p632_3 (m.d 1 4) (by simp) with h635 | h635
                                  · linarith only [h2, h635, hlam]
                                  · rcases p632_3 (m.d 2 4) (by simp) with h637 | h637
                                    · linarith only [h4, h637, hlam]
                                    · rcases p632_3 (m.d 3 4) (by simp) with h639 | h639
                                      · linarith only [h5, h639, hlam]
                                      · rcases p632_3 (m.d 4 5) (by simp) with h641 | h641
                                        · linarith only [h641, h7, hlam]
                                        · linarith only [h577, h641, hlam]
                                · linarith only [h2, h634, hlam]
                              · have p632_0 := h632c.1
                                have p632_1 := h632c.2.1
                                have p632_2 := h632c.2.2.1
                                have p632_3 := h632c.2.2.2
                                rcases p632_3 (m.d 0 4) (by simp) with h645 | h645
                                · rcases p632_3 (m.d 1 4) (by simp) with h646 | h646
                                  · linarith only [h2, h646, hlam]
                                  · linarith only [h574, h646, hlam]
                                · linarith only [h4, h645, hlam]
                              · have p632_0 := h632c.1
                                have p632_1 := h632c.2.1
                                have p632_2 := h632c.2.2.1
                                have p632_3 := h632c.2.2.2
                                rcases p632_3 (m.d 0 4) (by simp) with h650 | h650
                                · rcases p632_3 (m.d 1 4) (by simp) with h651 | h651
                                  · linarith only [h2, h651, hlam]
                                  · linarith only [h575, h651, hlam]
                                · linarith only [h5, h650, hlam]
                              · have p632_0 := h632c.1
                                have p632_1 := h632c.2.1
                                have p632_2 := h632c.2.2.1
                                have p632_3 := h632c.2.2.2
                                linarith only [h5, h577, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p632_1, u1ehi3]
                              · have p632_0 := h632c.1
                                have p632_1 := h632c.2.1
                                have p632_2 := h632c.2.2.1
                                have p632_3 := h632c.2.2.2
                                linarith only [h2, hlam, p632_1]
                              · have p632_0 := h632c.1
                                have p632_1 := h632c.2.1
                                have p632_2 := h632c.2.2.1
                                have p632_3 := h632c.2.2.2
                                linarith only [hlam, p632_0]
                              · have p632_0 := h632c.1
                                have p632_1 := h632c.2.1
                                have p632_2 := h632c.2.2.1
                                have p632_3 := h632c.2.2.2
                                linarith only [h577, hc24, hc45, hlam, hphi, p632_1]
                              · have p632_0 := h632c.1
                                have p632_1 := h632c.2.1
                                have p632_2 := h632c.2.2.1
                                have p632_3 := h632c.2.2.2
                                linarith only [h0, h3, h5, h577, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p632_1]
                              · have p632_0 := h632c.1
                                have p632_1 := h632c.2.1
                                have p632_2 := h632c.2.2.1
                                have p632_3 := h632c.2.2.2
                                linarith only [h577, hlam, p632_0]
                              · have p632_0 := h632c.1
                                have p632_1 := h632c.2.1
                                have p632_2 := h632c.2.2.1
                                have p632_3 := h632c.2.2.2
                                linarith only [h4, hlam, p632_1]
                              · have p632_0 := h632c.1
                                have p632_1 := h632c.2.1
                                have p632_2 := h632c.2.2.1
                                have p632_3 := h632c.2.2.2
                                linarith only [h574, hlam, p632_1]
                              · have p632_0 := h632c.1
                                have p632_1 := h632c.2.1
                                have p632_2 := h632c.2.2.1
                                have p632_3 := h632c.2.2.2
                                linarith only [hlam, p632_0]
                              · have p632_0 := h632c.1
                                have p632_1 := h632c.2.1
                                have p632_2 := h632c.2.2.1
                                have p632_3 := h632c.2.2.2
                                linarith only [h0, h3, h574, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p632_1]
                              · have p632_0 := h632c.1
                                have p632_1 := h632c.2.1
                                have p632_2 := h632c.2.2.1
                                have p632_3 := h632c.2.2.2
                                linarith only [h587, hlam, p632_0]
                              · have p632_0 := h632c.1
                                have p632_1 := h632c.2.1
                                have p632_2 := h632c.2.2.1
                                have p632_3 := h632c.2.2.2
                                linarith only [h5, hlam, p632_1]
                              · have p632_0 := h632c.1
                                have p632_1 := h632c.2.1
                                have p632_2 := h632c.2.2.1
                                have p632_3 := h632c.2.2.2
                                linarith only [h575, hlam, p632_0]
                              · have p632_0 := h632c.1
                                have p632_1 := h632c.2.1
                                have p632_2 := h632c.2.2.1
                                have p632_3 := h632c.2.2.2
                                linarith only [h585, hlam, p632_0]
                              · have p632_0 := h632c.1
                                have p632_1 := h632c.2.1
                                have p632_2 := h632c.2.2.1
                                have p632_3 := h632c.2.2.2
                                linarith only [hlam, p632_0]
                              · have p632_0 := h632c.1
                                have p632_1 := h632c.2.1
                                have p632_2 := h632c.2.2.1
                                have p632_3 := h632c.2.2.2
                                linarith only [h589, hlam, p632_0]
                              · have p632_0 := h632c.1
                                have p632_1 := h632c.2.1
                                have p632_2 := h632c.2.2.1
                                have p632_3 := h632c.2.2.2
                                linarith only [h7, hlam, p632_0]
                              · have p632_0 := h632c.1
                                have p632_1 := h632c.2.1
                                have p632_2 := h632c.2.2.1
                                have p632_3 := h632c.2.2.2
                                linarith only [h0, h3, h5, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p632_1, u1ehi3]
                              · have p632_0 := h632c.1
                                have p632_1 := h632c.2.1
                                have p632_2 := h632c.2.2.1
                                have p632_3 := h632c.2.2.2
                                rcases p632_3 (m.d 0 4) (by simp) with h673 | h673
                                · rcases p632_3 (m.d 1 4) (by simp) with h674 | h674
                                  · linarith only [h577, h674, hlam]
                                  · linarith only [h574, h674, hlam]
                                · linarith only [h4, h673, hlam]
                              · have p632_0 := h632c.1
                                have p632_1 := h632c.2.1
                                have p632_2 := h632c.2.2.1
                                have p632_3 := h632c.2.2.2
                                rcases p632_3 (m.d 0 4) (by simp) with h678 | h678
                                · rcases p632_3 (m.d 1 4) (by simp) with h679 | h679
                                  · linarith only [h577, h679, hlam]
                                  · linarith only [h575, h679, hlam]
                                · linarith only [h5, h678, hlam]
                              · have p632_0 := h632c.1
                                have p632_1 := h632c.2.1
                                have p632_2 := h632c.2.2.1
                                have p632_3 := h632c.2.2.2
                                linarith only [hlam, p632_0]
                        · linarith only [h586, h627, hlam]
                      · linarith only [h626, hlam, p591_0]
                    · linarith only [h6, h625, hlam]
                  · have p591_0 := h591c.1
                    have p591_1 := h591c.2.1
                    have p591_2 := h591c.2.2.1
                    have p591_3 := h591c.2.2.2
                    linarith only [h3, hlam, p591_0]
                  · have p591_0 := h591c.1
                    have p591_1 := h591c.2.1
                    have p591_2 := h591c.2.2.1
                    have p591_3 := h591c.2.2.2
                    linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p591_1, u1ehi2]
                  · have p591_0 := h591c.1
                    have p591_1 := h591c.2.1
                    have p591_2 := h591c.2.2.1
                    have p591_3 := h591c.2.2.2
                    linarith only [hlam, p591_0]
                  · have p591_0 := h591c.1
                    have p591_1 := h591c.2.1
                    have p591_2 := h591c.2.2.1
                    have p591_3 := h591c.2.2.2
                    rcases p591_3 (m.d 0 3) (by simp) with h690 | h690
                    · rcases p591_3 (m.d 1 3) (by simp) with h691 | h691
                      · linarith only [h691, h8, hlam]
                      · linarith only [h575, h691, hlam]
                    · linarith only [h5, h690, hlam]
                  · have p591_0 := h591c.1
                    have p591_1 := h591c.2.1
                    have p591_2 := h591c.2.2.1
                    have p591_3 := h591c.2.2.2
                    rcases p591_3 (m.d 0 3) (by simp) with h695 | h695
                    · rcases p591_3 (m.d 1 3) (by simp) with h696 | h696
                      · linarith only [h696, h8, hlam]
                      · linarith only [h576, h696, hlam]
                    · linarith only [h6, h695, hlam]
                  · have p591_0 := h591c.1
                    have p591_1 := h591c.2.1
                    have p591_2 := h591c.2.2.1
                    have p591_3 := h591c.2.2.2
                    linarith only [h5, hlam, p591_0]
                  · have p591_0 := h591c.1
                    have p591_1 := h591c.2.1
                    have p591_2 := h591c.2.2.1
                    have p591_3 := h591c.2.2.2
                    linarith only [h575, hlam, p591_0]
                  · have p591_0 := h591c.1
                    have p591_1 := h591c.2.1
                    have p591_2 := h591c.2.2.1
                    have p591_3 := h591c.2.2.2
                    linarith only [h585, hlam, p591_0]
                  · have p591_0 := h591c.1
                    have p591_1 := h591c.2.1
                    have p591_2 := h591c.2.2.1
                    have p591_3 := h591c.2.2.2
                    linarith only [hlam, p591_0]
                  · have p591_0 := h591c.1
                    have p591_1 := h591c.2.1
                    have p591_2 := h591c.2.2.1
                    have p591_3 := h591c.2.2.2
                    linarith only [h589, hlam, p591_1]
                  · have p591_0 := h591c.1
                    have p591_1 := h591c.2.1
                    have p591_2 := h591c.2.2.1
                    have p591_3 := h591c.2.2.2
                    linarith only [h6, hlam, p591_0]
                  · have p591_0 := h591c.1
                    have p591_1 := h591c.2.1
                    have p591_2 := h591c.2.2.1
                    have p591_3 := h591c.2.2.2
                    linarith only [h576, hlam, p591_0]
                  · have p591_0 := h591c.1
                    have p591_1 := h591c.2.1
                    have p591_2 := h591c.2.2.1
                    have p591_3 := h591c.2.2.2
                    linarith only [h586, hlam, p591_0]
                  · have p591_0 := h591c.1
                    have p591_1 := h591c.2.1
                    have p591_2 := h591c.2.2.1
                    have p591_3 := h591c.2.2.2
                    linarith only [h1, h576, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p591_1]
                  · have p591_0 := h591c.1
                    have p591_1 := h591c.2.1
                    have p591_2 := h591c.2.2.1
                    have p591_3 := h591c.2.2.2
                    linarith only [hlam, p591_0]
            · linarith only [h576, h586, h8, hlam]
          · linarith only [h0, h3, h5, h574, h585, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h712 | h712
        · linarith only [h574, h576, h712, h8, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h714 | h714
          · rcases m.htr 2 3 5 (by decide) (by decide) with h715 | h715
            · linarith only [h0, h3, h574, h576, h715, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
            · linarith only [h0, h3, h574, h6, h715, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
          · linarith only [h574, h714, h8, hc34, hlam, hphi, ht12, ht23, u1ehi3]
    · linarith only [h574, h575, h8, hlam]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h720 | h720
    · rcases m.htr 1 3 5 (by decide) (by decide) with h721 | h721
      · rcases m.htr 1 4 5 (by decide) (by decide) with h722 | h722
        · rcases m.htr 2 3 4 (by decide) (by decide) with h723 | h723
          · rcases m.htr 2 3 5 (by decide) (by decide) with h724 | h724
            · rcases m.htr 2 4 5 (by decide) (by decide) with h725 | h725
              · rcases m.htr 3 4 5 (by decide) (by decide) with h726 | h726
                · rcases h3bigk with h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [hlam, p727_0]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h0, h3, h720, h726, hc01, hc45, hlam, hphi, ht0b, ht5b, p727_1]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h0, h3, h574, h723, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p727_1, u1ehi1]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    rcases p727_3 (m.d 0 3) (by simp) with h731 | h731
                    · rcases p727_3 (m.d 1 3) (by simp) with h732 | h732
                      · linarith only [h1, h732, hlam]
                      · linarith only [h720, h732, hlam]
                    · linarith only [h731, hlam, p727_0]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    rcases p727_3 (m.d 0 3) (by simp) with h736 | h736
                    · rcases p727_3 (m.d 1 3) (by simp) with h737 | h737
                      · linarith only [h1, h737, hlam]
                      · linarith only [h721, h737, hlam]
                    · linarith only [h736, hlam, p727_0]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h1, hlam, p727_0]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [hlam, p727_0]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h8, hlam, p727_1]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h1, h726, hc01, hc45, hlam, hphi, ht0b, ht5b, p727_1]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    rcases p727_3 (m.d 0 3) (by simp) with h745 | h745
                    · rcases p727_3 (m.d 1 3) (by simp) with h746 | h746
                      · rcases p727_3 (m.d 2 3) (by simp) with h747 | h747
                        · rcases p727_3 (m.d 3 4) (by simp) with h748 | h748
                          · linarith only [h720, h748, hlam]
                          · linarith only [h726, h748, hlam]
                        · linarith only [h724, h747, hlam]
                      · linarith only [h746, hlam, p727_0]
                    · linarith only [h6, h745, hlam]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h3, hlam, p727_0]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p727_1, u1ehi2]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [hlam, p727_0]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h0, h3, h726, hc01, hc45, hlam, hphi, ht0b, ht5b, p727_1]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    rcases p727_3 (m.d 0 3) (by simp) with h758 | h758
                    · rcases p727_3 (m.d 1 3) (by simp) with h759 | h759
                      · linarith only [h759, h8, hlam]
                      · linarith only [h721, h759, hlam]
                    · linarith only [h6, h758, hlam]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h5, hlam, p727_0]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h720, hlam, p727_0]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h723, hlam, p727_0]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [hlam, p727_0]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h1, h720, h726, hc01, hc45, hlam, hphi, ht0b, ht5b, p727_1]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h6, hlam, p727_0]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h721, hlam, p727_0]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h724, hlam, p727_0]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h726, hlam, p727_0]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [hlam, p727_0]
                · rcases h3bigk with h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c
                  · have p773_0 := h773c.1
                    have p773_1 := h773c.2.1
                    have p773_2 := h773c.2.2.1
                    have p773_3 := h773c.2.2.2
                    linarith only [hlam, p773_0]
                  · have p773_0 := h773c.1
                    have p773_1 := h773c.2.1
                    have p773_2 := h773c.2.2.1
                    have p773_3 := h773c.2.2.2
                    linarith only [h0, h3, h720, h722, h726, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p773_1]
                  · have p773_0 := h773c.1
                    have p773_1 := h773c.2.1
                    have p773_2 := h773c.2.2.1
                    have p773_3 := h773c.2.2.2
                    linarith only [h0, h3, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p773_1, u1ehi1]
                  · have p773_0 := h773c.1
                    have p773_1 := h773c.2.1
                    have p773_2 := h773c.2.2.1
                    have p773_3 := h773c.2.2.2
                    rcases p773_3 (m.d 0 3) (by simp) with h777 | h777
                    · rcases p773_3 (m.d 1 3) (by simp) with h778 | h778
                      · linarith only [h1, h778, hlam]
                      · linarith only [h720, h778, hlam]
                    · linarith only [h777, hlam, p773_0]
                  · have p773_0 := h773c.1
                    have p773_1 := h773c.2.1
                    have p773_2 := h773c.2.2.1
                    have p773_3 := h773c.2.2.2
                    rcases p773_3 (m.d 0 3) (by simp) with h782 | h782
                    · rcases p773_3 (m.d 1 3) (by simp) with h783 | h783
                      · linarith only [h1, h783, hlam]
                      · linarith only [h721, h783, hlam]
                    · linarith only [h782, hlam, p773_0]
                  · have p773_0 := h773c.1
                    have p773_1 := h773c.2.1
                    have p773_2 := h773c.2.2.1
                    have p773_3 := h773c.2.2.2
                    linarith only [h1, hlam, p773_0]
                  · have p773_0 := h773c.1
                    have p773_1 := h773c.2.1
                    have p773_2 := h773c.2.2.1
                    have p773_3 := h773c.2.2.2
                    linarith only [hlam, p773_0]
                  · have p773_0 := h773c.1
                    have p773_1 := h773c.2.1
                    have p773_2 := h773c.2.2.1
                    have p773_3 := h773c.2.2.2
                    linarith only [h8, hlam, p773_1]
                  · have p773_0 := h773c.1
                    have p773_1 := h773c.2.1
                    have p773_2 := h773c.2.2.1
                    have p773_3 := h773c.2.2.2
                    rcases p773_3 (m.d 0 3) (by simp) with h790 | h790
                    · rcases p773_3 (m.d 1 3) (by simp) with h791 | h791
                      · rcases p773_3 (m.d 2 3) (by simp) with h792 | h792
                        · rcases p773_3 (m.d 3 4) (by simp) with h793 | h793
                          · linarith only [h793, hlam, p773_0]
                          · rcases p773_3 (m.d 3 5) (by simp) with h795 | h795
                            · linarith only [h721, h795, hlam]
                            · linarith only [h726, h795, hlam]
                        · linarith only [h723, h792, hlam]
                      · linarith only [h791, hlam, p773_0]
                    · linarith only [h5, h790, hlam]
                  · have p773_0 := h773c.1
                    have p773_1 := h773c.2.1
                    have p773_2 := h773c.2.2.1
                    have p773_3 := h773c.2.2.2
                    rcases p773_3 (m.d 0 3) (by simp) with h801 | h801
                    · rcases p773_3 (m.d 1 3) (by simp) with h802 | h802
                      · rcases p773_3 (m.d 2 3) (by simp) with h803 | h803
                        · rcases p773_3 (m.d 3 4) (by simp) with h804 | h804
                          · linarith only [h720, h804, hlam]
                          · rcases p773_3 (m.d 3 5) (by simp) with h806 | h806
                            · linarith only [h806, hlam, p773_0]
                            · rcases h4bigk with h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c
                              · have p808_0 := h808c.1
                                have p808_1 := h808c.2.1
                                have p808_2 := h808c.2.2.1
                                have p808_3 := h808c.2.2.2
                                linarith only [hlam, p808_0]
                              · have p808_0 := h808c.1
                                have p808_1 := h808c.2.1
                                have p808_2 := h808c.2.2.1
                                have p808_3 := h808c.2.2.2
                                linarith only [h5, h722, h726, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p808_1]
                              · have p808_0 := h808c.1
                                have p808_1 := h808c.2.1
                                have p808_2 := h808c.2.2.1
                                have p808_3 := h808c.2.2.2
                                linarith only [h0, h3, h5, h574, h722, h726, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p808_1]
                              · have p808_0 := h808c.1
                                have p808_1 := h808c.2.1
                                have p808_2 := h808c.2.2.1
                                have p808_3 := h808c.2.2.2
                                rcases p808_3 (m.d 0 4) (by simp) with h812 | h812
                                · rcases p808_3 (m.d 1 4) (by simp) with h813 | h813
                                  · linarith only [h2, h813, hlam]
                                  · linarith only [h720, h813, hlam]
                                · linarith only [h5, h812, hlam]
                              · have p808_0 := h808c.1
                                have p808_1 := h808c.2.1
                                have p808_2 := h808c.2.2.1
                                have p808_3 := h808c.2.2.2
                                rcases p808_3 (m.d 0 4) (by simp) with h817 | h817
                                · rcases p808_3 (m.d 1 4) (by simp) with h818 | h818
                                  · linarith only [h2, h818, hlam]
                                  · linarith only [h722, h818, hlam]
                                · linarith only [h817, hlam, p808_0]
                              · have p808_0 := h808c.1
                                have p808_1 := h808c.2.1
                                have p808_2 := h808c.2.2.1
                                have p808_3 := h808c.2.2.2
                                linarith only [h2, hlam, p808_1]
                              · have p808_0 := h808c.1
                                have p808_1 := h808c.2.1
                                have p808_2 := h808c.2.2.1
                                have p808_3 := h808c.2.2.2
                                linarith only [hlam, p808_0]
                              · have p808_0 := h808c.1
                                have p808_1 := h808c.2.1
                                have p808_2 := h808c.2.2.1
                                have p808_3 := h808c.2.2.2
                                linarith only [h574, hlam, p808_0]
                              · have p808_0 := h808c.1
                                have p808_1 := h808c.2.1
                                have p808_2 := h808c.2.2.1
                                have p808_3 := h808c.2.2.2
                                rcases p808_3 (m.d 0 4) (by simp) with h825 | h825
                                · rcases p808_3 (m.d 1 4) (by simp) with h826 | h826
                                  · rcases p808_3 (m.d 2 4) (by simp) with h827 | h827
                                    · rcases p808_3 (m.d 3 4) (by simp) with h828 | h828
                                      · linarith only [h720, h828, hlam]
                                      · rcases p808_3 (m.d 4 5) (by simp) with h830 | h830
                                        · linarith only [h722, h830, hlam]
                                        · linarith only [h726, h830, hlam]
                                    · linarith only [h723, h827, hlam]
                                  · linarith only [h720, h826, hlam]
                                · linarith only [h5, h825, hlam]
                              · have p808_0 := h808c.1
                                have p808_1 := h808c.2.1
                                have p808_2 := h808c.2.2.1
                                have p808_3 := h808c.2.2.2
                                linarith only [h1, h720, h726, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p808_1]
                              · have p808_0 := h808c.1
                                have p808_1 := h808c.2.1
                                have p808_2 := h808c.2.2.1
                                have p808_3 := h808c.2.2.2
                                linarith only [h4, hlam, p808_1]
                              · have p808_0 := h808c.1
                                have p808_1 := h808c.2.1
                                have p808_2 := h808c.2.2.1
                                have p808_3 := h808c.2.2.2
                                linarith only [hc24, hlam, hphi, ht12, p808_1, u1ehi3]
                              · have p808_0 := h808c.1
                                have p808_1 := h808c.2.1
                                have p808_2 := h808c.2.2.1
                                have p808_3 := h808c.2.2.2
                                linarith only [hlam, p808_0]
                              · have p808_0 := h808c.1
                                have p808_1 := h808c.2.1
                                have p808_2 := h808c.2.2.1
                                have p808_3 := h808c.2.2.2
                                rcases p808_3 (m.d 0 4) (by simp) with h840 | h840
                                · rcases p808_3 (m.d 1 4) (by simp) with h841 | h841
                                  · linarith only [h574, h841, hlam]
                                  · linarith only [h720, h841, hlam]
                                · linarith only [h5, h840, hlam]
                              · have p808_0 := h808c.1
                                have p808_1 := h808c.2.1
                                have p808_2 := h808c.2.2.1
                                have p808_3 := h808c.2.2.2
                                linarith only [h0, h3, h723, h726, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p808_1]
                              · have p808_0 := h808c.1
                                have p808_1 := h808c.2.1
                                have p808_2 := h808c.2.2.1
                                have p808_3 := h808c.2.2.2
                                linarith only [h5, hlam, p808_1]
                              · have p808_0 := h808c.1
                                have p808_1 := h808c.2.1
                                have p808_2 := h808c.2.2.1
                                have p808_3 := h808c.2.2.2
                                linarith only [h720, hlam, p808_0]
                              · have p808_0 := h808c.1
                                have p808_1 := h808c.2.1
                                have p808_2 := h808c.2.2.1
                                have p808_3 := h808c.2.2.2
                                linarith only [h723, hlam, p808_0]
                              · have p808_0 := h808c.1
                                have p808_1 := h808c.2.1
                                have p808_2 := h808c.2.2.1
                                have p808_3 := h808c.2.2.2
                                linarith only [hlam, p808_0]
                              · have p808_0 := h808c.1
                                have p808_1 := h808c.2.1
                                have p808_2 := h808c.2.2.1
                                have p808_3 := h808c.2.2.2
                                linarith only [h726, hlam, p808_0]
                              · have p808_0 := h808c.1
                                have p808_1 := h808c.2.1
                                have p808_2 := h808c.2.2.1
                                have p808_3 := h808c.2.2.2
                                linarith only [h7, hlam, p808_0]
                              · have p808_0 := h808c.1
                                have p808_1 := h808c.2.1
                                have p808_2 := h808c.2.2.1
                                have p808_3 := h808c.2.2.2
                                linarith only [h722, hlam, p808_0]
                              · have p808_0 := h808c.1
                                have p808_1 := h808c.2.1
                                have p808_2 := h808c.2.2.1
                                have p808_3 := h808c.2.2.2
                                linarith only [h725, hlam, p808_0]
                              · have p808_0 := h808c.1
                                have p808_1 := h808c.2.1
                                have p808_2 := h808c.2.2.1
                                have p808_3 := h808c.2.2.2
                                linarith only [h2, h722, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p808_1]
                              · have p808_0 := h808c.1
                                have p808_1 := h808c.2.1
                                have p808_2 := h808c.2.2.1
                                have p808_3 := h808c.2.2.2
                                linarith only [hlam, p808_0]
                        · linarith only [h724, h803, hlam]
                      · linarith only [h802, hlam, p773_0]
                    · linarith only [h6, h801, hlam]
                  · have p773_0 := h773c.1
                    have p773_1 := h773c.2.1
                    have p773_2 := h773c.2.2.1
                    have p773_3 := h773c.2.2.2
                    linarith only [h3, hlam, p773_0]
                  · have p773_0 := h773c.1
                    have p773_1 := h773c.2.1
                    have p773_2 := h773c.2.2.1
                    have p773_3 := h773c.2.2.2
                    linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p773_1, u1ehi2]
                  · have p773_0 := h773c.1
                    have p773_1 := h773c.2.1
                    have p773_2 := h773c.2.2.1
                    have p773_3 := h773c.2.2.2
                    linarith only [hlam, p773_0]
                  · have p773_0 := h773c.1
                    have p773_1 := h773c.2.1
                    have p773_2 := h773c.2.2.1
                    have p773_3 := h773c.2.2.2
                    rcases p773_3 (m.d 0 3) (by simp) with h862 | h862
                    · rcases p773_3 (m.d 1 3) (by simp) with h863 | h863
                      · linarith only [h8, h863, hlam]
                      · linarith only [h720, h863, hlam]
                    · linarith only [h5, h862, hlam]
                  · have p773_0 := h773c.1
                    have p773_1 := h773c.2.1
                    have p773_2 := h773c.2.2.1
                    have p773_3 := h773c.2.2.2
                    rcases p773_3 (m.d 0 3) (by simp) with h867 | h867
                    · rcases p773_3 (m.d 1 3) (by simp) with h868 | h868
                      · linarith only [h8, h868, hlam]
                      · linarith only [h721, h868, hlam]
                    · linarith only [h6, h867, hlam]
                  · have p773_0 := h773c.1
                    have p773_1 := h773c.2.1
                    have p773_2 := h773c.2.2.1
                    have p773_3 := h773c.2.2.2
                    linarith only [h5, hlam, p773_0]
                  · have p773_0 := h773c.1
                    have p773_1 := h773c.2.1
                    have p773_2 := h773c.2.2.1
                    have p773_3 := h773c.2.2.2
                    linarith only [h720, hlam, p773_0]
                  · have p773_0 := h773c.1
                    have p773_1 := h773c.2.1
                    have p773_2 := h773c.2.2.1
                    have p773_3 := h773c.2.2.2
                    linarith only [h723, hlam, p773_0]
                  · have p773_0 := h773c.1
                    have p773_1 := h773c.2.1
                    have p773_2 := h773c.2.2.1
                    have p773_3 := h773c.2.2.2
                    linarith only [hlam, p773_0]
                  · have p773_0 := h773c.1
                    have p773_1 := h773c.2.1
                    have p773_2 := h773c.2.2.1
                    have p773_3 := h773c.2.2.2
                    linarith only [h726, hlam, p773_1]
                  · have p773_0 := h773c.1
                    have p773_1 := h773c.2.1
                    have p773_2 := h773c.2.2.1
                    have p773_3 := h773c.2.2.2
                    linarith only [h6, hlam, p773_0]
                  · have p773_0 := h773c.1
                    have p773_1 := h773c.2.1
                    have p773_2 := h773c.2.2.1
                    have p773_3 := h773c.2.2.2
                    linarith only [h721, hlam, p773_0]
                  · have p773_0 := h773c.1
                    have p773_1 := h773c.2.1
                    have p773_2 := h773c.2.2.1
                    have p773_3 := h773c.2.2.2
                    linarith only [h724, hlam, p773_0]
                  · have p773_0 := h773c.1
                    have p773_1 := h773c.2.1
                    have p773_2 := h773c.2.2.1
                    have p773_3 := h773c.2.2.2
                    linarith only [h1, h721, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p773_1]
                  · have p773_0 := h773c.1
                    have p773_1 := h773c.2.1
                    have p773_2 := h773c.2.2.1
                    have p773_3 := h773c.2.2.2
                    linarith only [hlam, p773_0]
              · linarith only [h574, h722, h725, hlam]
            · linarith only [h721, h724, h8, hlam]
          · linarith only [h0, h3, h5, h723, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h885 | h885
          · rcases m.htr 2 3 5 (by decide) (by decide) with h886 | h886
            · rcases m.htr 2 4 5 (by decide) (by decide) with h887 | h887
              · linarith only [h722, h885, h887, hc23, hlam, hphi, ht12, u1ehi3]
              · linarith only [h0, h3, h5, h574, h7, h887, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
            · linarith only [h721, h8, h886, hc13, hlam, hphi, u1ehi1]
          · linarith only [h720, h8, h885, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h892 | h892
        · linarith only [h720, h721, h892, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h894 | h894
          · rcases m.htr 2 3 5 (by decide) (by decide) with h895 | h895
            · linarith only [h574, h720, h721, h895, hc23, hlam, hphi, ht12, u1ehi1]
            · linarith only [h0, h3, h6, h8, h895, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
          · linarith only [h720, h8, h894, hc13, hlam, hphi, u1ehi1]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h899 | h899
      · rcases m.htr 1 4 5 (by decide) (by decide) with h900 | h900
        · rcases m.htr 2 3 4 (by decide) (by decide) with h901 | h901
          · linarith only [h0, h3, h720, h899, h901, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · linarith only [h8, h901, hc34, hlam, hphi, ht12, ht23, u1ehi1]
        · linarith only [h720, h899, h900, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h905 | h905
        · rcases m.htr 2 3 4 (by decide) (by decide) with h906 | h906
          · linarith only [h720, h906, hc23, hlam, hphi, ht12, u1ehi2]
          · linarith only [h8, h906, hc34, hlam, hphi, ht12, ht23, u1ehi1]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h909 | h909
          · linarith only [h720, h8, h909, hc23, hlam, hphi, ht12, u1ehi1]
          · linarith only [h0, h3, h5, h8, h909, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]

theorem r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h7 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h0ehi := hb0.1
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
  · exact r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb1 hb3 hb4 h0 h1 h2 h3 h4 h5 h6 h7 h8
  · exact r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb1 hb3 hb4 h0 h1 h2 h3 h4 h5 h6 h7 h8

theorem r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h7 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h0ehi := hb0.1
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  linarith only [h7, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]

theorem r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h0ehi := hb0.1
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
  · exact r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb1 hb3 hb4 h0 h1 h2 h3 h4 h5 h6 h7
  · exact r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb1 hb3 hb4 h0 h1 h2 h3 h4 h5 h6 h7

theorem r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h0ehi := hb0.1
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  linarith only [h6, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]

theorem r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0ehi := hb0.1
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
  · exact r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0 m hb0 hb1 hb3 hb4 h0 h1 h2 h3 h4 h5 h6
  · exact r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x1 m hb0 hb1 hb3 hb4 h0 h1 h2 h3 h4 h5 h6

theorem r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h0ehi := hb0.1
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  linarith only [h5, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]

theorem r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h0ehi := hb0.1
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x0_x0_x0_x0_x0_x0 m hb0 hb1 hb3 hb4 h0 h1 h2 h3 h4 h5
  · exact r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x0_x0_x0_x0_x0_x1 m hb0 hb1 hb3 hb4 h0 h1 h2 h3 h4 h5

theorem r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h0ehi := hb0.1
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  linarith only [h3, h4, hc24, hlam, hphi, ht01, ht12, u0ehi2]

theorem r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0ehi := hb0.1
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
  · exact r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x0_x0_x0_x0_x0 m hb0 hb1 hb3 hb4 h0 h1 h2 h3 h4
  · exact r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x0_x0_x0_x0_x1 m hb0 hb1 hb3 hb4 h0 h1 h2 h3 h4

theorem r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h0ehi := hb0.1
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  linarith only [h3, hc23, hlam, hphi, ht01, ht12, u0ehi1]

theorem r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0ehi := hb0.1
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
  · exact r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x0_x0_x0_x0 m hb0 hb1 hb3 hb4 h0 h1 h2 h3
  · exact r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x0_x0_x0_x1 m hb0 hb1 hb3 hb4 h0 h1 h2 h3

theorem r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0ehi := hb0.1
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  linarith only [h2, hc14, hlam, hphi, ht01, u0ehi0]

theorem r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0ehi := hb0.1
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x0_x0_x0 m hb0 hb1 hb3 hb4 h0 h1 h2
  · exact r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x0_x0_x1 m hb0 hb1 hb3 hb4 h0 h1 h2

theorem r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h0ehi := hb0.1
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  linarith only [h0, h1, hc13, hlam, hphi, ht01, u0ehi1]

theorem r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h0ehi := hb0.1
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x0_x0 m hb0 hb1 hb3 hb4 h0 h1
  · exact r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x0_x1 m hb0 hb1 hb3 hb4 h0 h1

theorem r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0ehi := hb0.1
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem r1l7_20_11_13_14_H_R_L_R_L_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0ehi := hb0.1
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x0 m hb0 hb1 hb3 hb4 h0
  · exact r1l7_20_11_13_14_H_R_L_R_L_I_L_I_x1 m hb0 hb1 hb3 hb4 h0

end R2N4
