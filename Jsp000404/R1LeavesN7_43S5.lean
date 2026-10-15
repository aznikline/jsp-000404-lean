import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_43S4

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6266000 in
set_option maxHeartbeats 6266000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h570 | h570
  · rcases m.htr 0 2 5 (by decide) (by decide) with h571 | h571
    · rcases m.htr 0 3 4 (by decide) (by decide) with h572 | h572
      · rcases m.htr 0 4 5 (by decide) (by decide) with h573 | h573
        · rcases m.htr 1 2 3 (by decide) (by decide) with h574 | h574
          · linarith only [h0, h4, h570, h574, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h576 | h576
            · rcases m.htr 1 2 5 (by decide) (by decide) with h577 | h577
              · rcases m.htr 1 3 4 (by decide) (by decide) with h578 | h578
                · rcases m.htr 1 3 5 (by decide) (by decide) with h579 | h579
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h580 | h580
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h581 | h581
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h582 | h582
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h583 | h583
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h584 | h584
                            · rcases h1bigk with h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c | h585c
                              · have p585_0 := h585c.1
                                have p585_1 := h585c.2.1
                                have p585_2 := h585c.2.2.1
                                have p585_3 := h585c.2.2.2
                                linarith only [hlam, p585_0]
                              · have p585_0 := h585c.1
                                have p585_1 := h585c.2.1
                                have p585_2 := h585c.2.2.1
                                have p585_3 := h585c.2.2.2
                                linarith only [h576, h581, h584, hc01, hc45, hlam, hphi, ht0b, ht5b, p585_1]
                              · have p585_0 := h585c.1
                                have p585_1 := h585c.2.1
                                have p585_2 := h585c.2.2.1
                                have p585_3 := h585c.2.2.2
                                linarith only [h574, h576, h581, h584, hc01, hc45, hlam, hphi, ht0b, ht5b, p585_1]
                              · have p585_0 := h585c.1
                                have p585_1 := h585c.2.1
                                have p585_2 := h585c.2.2.1
                                have p585_3 := h585c.2.2.2
                                rcases p585_3 (m.d 0 1) (by simp) with h589 | h589
                                · rcases p585_3 (m.d 1 2) (by simp) with h590 | h590
                                  · linarith only [h0, h590, hlam]
                                  · linarith only [h576, h590, hlam]
                                · linarith only [h589, hlam, p585_0]
                              · have p585_0 := h585c.1
                                have p585_1 := h585c.2.1
                                have p585_2 := h585c.2.2.1
                                have p585_3 := h585c.2.2.2
                                rcases p585_3 (m.d 0 1) (by simp) with h594 | h594
                                · rcases p585_3 (m.d 1 2) (by simp) with h595 | h595
                                  · linarith only [h0, h595, hlam]
                                  · linarith only [h577, h595, hlam]
                                · linarith only [h594, hlam, p585_0]
                              · have p585_0 := h585c.1
                                have p585_1 := h585c.2.1
                                have p585_2 := h585c.2.2.1
                                have p585_3 := h585c.2.2.2
                                linarith only [h0, hlam, p585_0]
                              · have p585_0 := h585c.1
                                have p585_1 := h585c.2.1
                                have p585_2 := h585c.2.2.1
                                have p585_3 := h585c.2.2.2
                                linarith only [hlam, p585_0]
                              · have p585_0 := h585c.1
                                have p585_1 := h585c.2.1
                                have p585_2 := h585c.2.2.1
                                have p585_3 := h585c.2.2.2
                                linarith only [h574, hlam, p585_1]
                              · have p585_0 := h585c.1
                                have p585_1 := h585c.2.1
                                have p585_2 := h585c.2.2.1
                                have p585_3 := h585c.2.2.2
                                linarith only [h0, h4, h576, h581, h584, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p585_1]
                              · have p585_0 := h585c.1
                                have p585_1 := h585c.2.1
                                have p585_2 := h585c.2.2.1
                                have p585_3 := h585c.2.2.2
                                rcases p585_3 (m.d 0 1) (by simp) with h603 | h603
                                · rcases p585_3 (m.d 1 2) (by simp) with h604 | h604
                                  · rcases p585_3 (m.d 1 3) (by simp) with h605 | h605
                                    · rcases p585_3 (m.d 1 4) (by simp) with h606 | h606
                                      · linarith only [h576, h606, hlam]
                                      · linarith only [h580, h606, hlam]
                                    · linarith only [h579, h605, hlam]
                                  · linarith only [h577, h604, hlam]
                                · linarith only [h3, h603, hlam]
                              · have p585_0 := h585c.1
                                have p585_1 := h585c.2.1
                                have p585_2 := h585c.2.2.1
                                have p585_3 := h585c.2.2.2
                                linarith only [h1, hlam, p585_0]
                              · have p585_0 := h585c.1
                                have p585_1 := h585c.2.1
                                have p585_2 := h585c.2.2.1
                                have p585_3 := h585c.2.2.2
                                linarith only [h1, h576, h581, h584, hc01, hc45, hlam, hphi, ht0b, ht5b, p585_1]
                              · have p585_0 := h585c.1
                                have p585_1 := h585c.2.1
                                have p585_2 := h585c.2.2.1
                                have p585_3 := h585c.2.2.2
                                linarith only [hlam, p585_0]
                              · have p585_0 := h585c.1
                                have p585_1 := h585c.2.1
                                have p585_2 := h585c.2.2.1
                                have p585_3 := h585c.2.2.2
                                linarith only [h1, h576, h581, h584, hc01, hc45, hlam, hphi, ht0b, ht5b, p585_1]
                              · have p585_0 := h585c.1
                                have p585_1 := h585c.2.1
                                have p585_2 := h585c.2.2.1
                                have p585_3 := h585c.2.2.2
                                rcases p585_3 (m.d 0 1) (by simp) with h616 | h616
                                · rcases p585_3 (m.d 1 2) (by simp) with h617 | h617
                                  · linarith only [h574, h617, hlam]
                                  · linarith only [h577, h617, hlam]
                                · linarith only [h3, h616, hlam]
                              · have p585_0 := h585c.1
                                have p585_1 := h585c.2.1
                                have p585_2 := h585c.2.2.1
                                have p585_3 := h585c.2.2.2
                                linarith only [h2, hlam, p585_0]
                              · have p585_0 := h585c.1
                                have p585_1 := h585c.2.1
                                have p585_2 := h585c.2.2.1
                                have p585_3 := h585c.2.2.2
                                linarith only [h576, hlam, p585_0]
                              · have p585_0 := h585c.1
                                have p585_1 := h585c.2.1
                                have p585_2 := h585c.2.2.1
                                have p585_3 := h585c.2.2.2
                                linarith only [h578, hlam, p585_1]
                              · have p585_0 := h585c.1
                                have p585_1 := h585c.2.1
                                have p585_2 := h585c.2.2.1
                                have p585_3 := h585c.2.2.2
                                linarith only [hlam, p585_0]
                              · have p585_0 := h585c.1
                                have p585_1 := h585c.2.1
                                have p585_2 := h585c.2.2.1
                                have p585_3 := h585c.2.2.2
                                rcases p585_3 (m.d 0 1) (by simp) with h625 | h625
                                · rcases p585_3 (m.d 1 2) (by simp) with h626 | h626
                                  · rcases p585_3 (m.d 1 3) (by simp) with h627 | h627
                                    · rcases p585_3 (m.d 1 4) (by simp) with h628 | h628
                                      · rcases p585_3 (m.d 1 5) (by simp) with h629 | h629
                                        · linarith only [h580, h629, hlam]
                                        · rcases h2bigk with h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c
                                          · have p631_0 := h631c.1
                                            have p631_1 := h631c.2.1
                                            have p631_2 := h631c.2.2.1
                                            have p631_3 := h631c.2.2.2
                                            linarith only [hlam, p631_0]
                                          · have p631_0 := h631c.1
                                            have p631_1 := h631c.2.1
                                            have p631_2 := h631c.2.2.1
                                            have p631_3 := h631c.2.2.2
                                            linarith only [h4, h576, h577, h582, h584, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p585_1, p631_1]
                                          · have p631_0 := h631c.1
                                            have p631_1 := h631c.2.1
                                            have p631_2 := h631c.2.2.1
                                            have p631_3 := h631c.2.2.2
                                            linarith only [h4, hlam, p631_0]
                                          · have p631_0 := h631c.1
                                            have p631_1 := h631c.2.1
                                            have p631_2 := h631c.2.2.1
                                            have p631_3 := h631c.2.2.2
                                            linarith only [h4, h581, h584, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p631_1]
                                          · have p631_0 := h631c.1
                                            have p631_1 := h631c.2.1
                                            have p631_2 := h631c.2.2.1
                                            have p631_3 := h631c.2.2.2
                                            rcases p631_3 (m.d 0 2) (by simp) with h636 | h636
                                            · rcases p631_3 (m.d 1 2) (by simp) with h637 | h637
                                              · linarith only [h0, h637, hlam]
                                              · linarith only [h577, h637, hlam]
                                            · linarith only [h636, hlam, p631_0]
                                          · have p631_0 := h631c.1
                                            have p631_1 := h631c.2.1
                                            have p631_2 := h631c.2.2.1
                                            have p631_3 := h631c.2.2.2
                                            linarith only [h0, hlam, p631_1]
                                          · have p631_0 := h631c.1
                                            have p631_1 := h631c.2.1
                                            have p631_2 := h631c.2.2.1
                                            have p631_3 := h631c.2.2.2
                                            linarith only [hlam, p631_0]
                                          · have p631_0 := h631c.1
                                            have p631_1 := h631c.2.1
                                            have p631_2 := h631c.2.2.1
                                            have p631_3 := h631c.2.2.2
                                            linarith only [h574, hlam, p631_0]
                                          · have p631_0 := h631c.1
                                            have p631_1 := h631c.2.1
                                            have p631_2 := h631c.2.2.1
                                            have p631_3 := h631c.2.2.2
                                            linarith only [h0, h581, h584, hc01, hc45, hlam, hphi, ht0b, ht5b, p631_1]
                                          · have p631_0 := h631c.1
                                            have p631_1 := h631c.2.1
                                            have p631_2 := h631c.2.2.1
                                            have p631_3 := h631c.2.2.2
                                            rcases p631_3 (m.d 0 2) (by simp) with h645 | h645
                                            · rcases p631_3 (m.d 1 2) (by simp) with h646 | h646
                                              · rcases p631_3 (m.d 2 3) (by simp) with h647 | h647
                                                · rcases p631_3 (m.d 2 4) (by simp) with h648 | h648
                                                  · linarith only [h576, h648, hlam]
                                                  · linarith only [h583, h648, hlam]
                                                · linarith only [h582, h647, hlam]
                                              · linarith only [h646, hlam, p631_0]
                                            · linarith only [h571, h645, hlam]
                                          · have p631_0 := h631c.1
                                            have p631_1 := h631c.2.1
                                            have p631_2 := h631c.2.2.1
                                            have p631_3 := h631c.2.2.2
                                            linarith only [h570, h581, h584, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p631_1]
                                          · have p631_0 := h631c.1
                                            have p631_1 := h631c.2.1
                                            have p631_2 := h631c.2.2.1
                                            have p631_3 := h631c.2.2.2
                                            linarith only [h576, h581, h584, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p631_1]
                                          · have p631_0 := h631c.1
                                            have p631_1 := h631c.2.1
                                            have p631_2 := h631c.2.2.1
                                            have p631_3 := h631c.2.2.2
                                            linarith only [hlam, p631_0]
                                          · have p631_0 := h631c.1
                                            have p631_1 := h631c.2.1
                                            have p631_2 := h631c.2.2.1
                                            have p631_3 := h631c.2.2.2
                                            rcases p631_3 (m.d 0 2) (by simp) with h657 | h657
                                            · linarith only [h4, h657, hlam]
                                            · linarith only [h570, h657, hlam]
                                          · have p631_0 := h631c.1
                                            have p631_1 := h631c.2.1
                                            have p631_2 := h631c.2.2.1
                                            have p631_3 := h631c.2.2.2
                                            linarith only [h2, h4, h570, h577, hlam, p585_1, p631_2]
                                          · have p631_0 := h631c.1
                                            have p631_1 := h631c.2.1
                                            have p631_2 := h631c.2.2.1
                                            have p631_3 := h631c.2.2.2
                                            linarith only [h570, hlam, p631_0]
                                          · have p631_0 := h631c.1
                                            have p631_1 := h631c.2.1
                                            have p631_2 := h631c.2.2.1
                                            have p631_3 := h631c.2.2.2
                                            linarith only [h576, hlam, p631_0]
                                          · have p631_0 := h631c.1
                                            have p631_1 := h631c.2.1
                                            have p631_2 := h631c.2.2.1
                                            have p631_3 := h631c.2.2.2
                                            linarith only [h581, hlam, p631_0]
                                          · have p631_0 := h631c.1
                                            have p631_1 := h631c.2.1
                                            have p631_2 := h631c.2.2.1
                                            have p631_3 := h631c.2.2.2
                                            linarith only [hlam, p631_0]
                                          · have p631_0 := h631c.1
                                            have p631_1 := h631c.2.1
                                            have p631_2 := h631c.2.2.1
                                            have p631_3 := h631c.2.2.2
                                            linarith only [h4, h570, h582, h584, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p631_1]
                                          · have p631_0 := h631c.1
                                            have p631_1 := h631c.2.1
                                            have p631_2 := h631c.2.2.1
                                            have p631_3 := h631c.2.2.2
                                            linarith only [h571, hlam, p631_0]
                                          · have p631_0 := h631c.1
                                            have p631_1 := h631c.2.1
                                            have p631_2 := h631c.2.2.1
                                            have p631_3 := h631c.2.2.2
                                            linarith only [h577, hlam, p631_0]
                                          · have p631_0 := h631c.1
                                            have p631_1 := h631c.2.1
                                            have p631_2 := h631c.2.2.1
                                            have p631_3 := h631c.2.2.2
                                            linarith only [h582, hlam, p631_0]
                                          · have p631_0 := h631c.1
                                            have p631_1 := h631c.2.1
                                            have p631_2 := h631c.2.2.1
                                            have p631_3 := h631c.2.2.2
                                            linarith only [h583, hlam, p631_1]
                                          · have p631_0 := h631c.1
                                            have p631_1 := h631c.2.1
                                            have p631_2 := h631c.2.2.1
                                            have p631_3 := h631c.2.2.2
                                            linarith only [hlam, p631_0]
                                      · linarith only [h580, h628, hlam]
                                    · linarith only [h579, h627, hlam]
                                  · linarith only [h577, h626, hlam]
                                · linarith only [h3, h625, hlam]
                              · have p585_0 := h585c.1
                                have p585_1 := h585c.2.1
                                have p585_2 := h585c.2.2.1
                                have p585_3 := h585c.2.2.2
                                linarith only [h3, hlam, p585_0]
                              · have p585_0 := h585c.1
                                have p585_1 := h585c.2.1
                                have p585_2 := h585c.2.2.1
                                have p585_3 := h585c.2.2.2
                                linarith only [h577, hlam, p585_0]
                              · have p585_0 := h585c.1
                                have p585_1 := h585c.2.1
                                have p585_2 := h585c.2.2.1
                                have p585_3 := h585c.2.2.2
                                linarith only [h579, hlam, p585_0]
                              · have p585_0 := h585c.1
                                have p585_1 := h585c.2.1
                                have p585_2 := h585c.2.2.1
                                have p585_3 := h585c.2.2.2
                                linarith only [h580, hlam, p585_0]
                              · have p585_0 := h585c.1
                                have p585_1 := h585c.2.1
                                have p585_2 := h585c.2.2.1
                                have p585_3 := h585c.2.2.2
                                linarith only [hlam, p585_0]
                            · linarith only [h584, hc34, hlam, hphi, ht45, u5elo4]
                          · linarith only [h580, h583, hc24, hlam, hphi, ht45, u5elo1]
                        · linarith only [h4, h582, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h4, h572, h581, hlam]
                    · linarith only [h580, hc14, hlam, hphi, ht45, u5elo4]
                  · linarith only [h579, hc13, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h574, h576, h578, hlam]
              · linarith only [h576, h577, hc24, hlam, hphi, ht45, u5elo2]
            · linarith only [h4, h570, h576, hc12, hc23, hlam, hphi]
        · linarith only [h573, hc04, hlam, hphi, ht45, u5elo4]
      · linarith only [h4, h570, h572, hlam]
    · linarith only [h571, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h692 | h692
    · rcases m.htr 0 3 4 (by decide) (by decide) with h693 | h693
      · rcases m.htr 0 4 5 (by decide) (by decide) with h694 | h694
        · rcases m.htr 1 2 3 (by decide) (by decide) with h695 | h695
          · linarith only [h0, h4, h695, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h697 | h697
            · linarith only [h0, h570, h697, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h699 | h699
              · rcases m.htr 1 3 4 (by decide) (by decide) with h700 | h700
                · rcases m.htr 1 3 5 (by decide) (by decide) with h701 | h701
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h702 | h702
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h703 | h703
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h704 | h704
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h705 | h705
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h706 | h706
                            · rcases h1bigk with h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c
                              · have p707_0 := h707c.1
                                have p707_1 := h707c.2.1
                                have p707_2 := h707c.2.2.1
                                have p707_3 := h707c.2.2.2
                                linarith only [hlam, p707_0]
                              · have p707_0 := h707c.1
                                have p707_1 := h707c.2.1
                                have p707_2 := h707c.2.2.1
                                have p707_3 := h707c.2.2.2
                                rcases p707_3 (m.d 0 1) (by simp) with h709 | h709
                                · rcases p707_3 (m.d 1 2) (by simp) with h710 | h710
                                  · linarith only [h710, hlam, p707_0]
                                  · rcases p707_3 (m.d 1 3) (by simp) with h712 | h712
                                    · linarith only [h1, h712, hlam]
                                    · linarith only [h695, h712, hlam]
                                · linarith only [h709, hlam, p707_0]
                              · have p707_0 := h707c.1
                                have p707_1 := h707c.2.1
                                have p707_2 := h707c.2.2.1
                                have p707_3 := h707c.2.2.2
                                linarith only [h700, h706, hc01, hc45, hlam, hphi, ht0b, ht5b, p707_1]
                              · have p707_0 := h707c.1
                                have p707_1 := h707c.2.1
                                have p707_2 := h707c.2.2.1
                                have p707_3 := h707c.2.2.2
                                rcases p707_3 (m.d 0 1) (by simp) with h717 | h717
                                · rcases p707_3 (m.d 1 2) (by simp) with h718 | h718
                                  · linarith only [h0, h718, hlam]
                                  · rcases p707_3 (m.d 1 3) (by simp) with h720 | h720
                                    · linarith only [h1, h720, hlam]
                                    · linarith only [h700, h720, hlam]
                                · linarith only [h717, hlam, p707_0]
                              · have p707_0 := h707c.1
                                have p707_1 := h707c.2.1
                                have p707_2 := h707c.2.2.1
                                have p707_3 := h707c.2.2.2
                                rcases p707_3 (m.d 0 1) (by simp) with h724 | h724
                                · rcases p707_3 (m.d 1 2) (by simp) with h725 | h725
                                  · linarith only [h0, h725, hlam]
                                  · linarith only [h699, h725, hlam]
                                · linarith only [h724, hlam, p707_0]
                              · have p707_0 := h707c.1
                                have p707_1 := h707c.2.1
                                have p707_2 := h707c.2.2.1
                                have p707_3 := h707c.2.2.2
                                linarith only [h0, hlam, p707_0]
                              · have p707_0 := h707c.1
                                have p707_1 := h707c.2.1
                                have p707_2 := h707c.2.2.1
                                have p707_3 := h707c.2.2.2
                                linarith only [hlam, p707_0]
                              · have p707_0 := h707c.1
                                have p707_1 := h707c.2.1
                                have p707_2 := h707c.2.2.1
                                have p707_3 := h707c.2.2.2
                                linarith only [h695, hlam, p707_1]
                              · have p707_0 := h707c.1
                                have p707_1 := h707c.2.1
                                have p707_2 := h707c.2.2.1
                                have p707_3 := h707c.2.2.2
                                linarith only [h697, hlam, p707_1]
                              · have p707_0 := h707c.1
                                have p707_1 := h707c.2.1
                                have p707_2 := h707c.2.2.1
                                have p707_3 := h707c.2.2.2
                                rcases p707_3 (m.d 0 1) (by simp) with h733 | h733
                                · rcases p707_3 (m.d 1 2) (by simp) with h734 | h734
                                  · rcases p707_3 (m.d 1 3) (by simp) with h735 | h735
                                    · rcases p707_3 (m.d 1 4) (by simp) with h736 | h736
                                      · rcases p707_3 (m.d 1 5) (by simp) with h737 | h737
                                        · linarith only [h699, h737, hlam]
                                        · rcases h2bigk with h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c
                                          · have p739_0 := h739c.1
                                            have p739_1 := h739c.2.1
                                            have p739_2 := h739c.2.2.1
                                            have p739_3 := h739c.2.2.2
                                            linarith only [hlam, p739_0]
                                          · have p739_0 := h739c.1
                                            have p739_1 := h739c.2.1
                                            have p739_2 := h739c.2.2.1
                                            have p739_3 := h739c.2.2.2
                                            linarith only [h699, h704, h706, hc02, hc45, hlam, hphi, ht0b, ht5b, p707_1, p739_1]
                                          · have p739_0 := h739c.1
                                            have p739_1 := h739c.2.1
                                            have p739_2 := h739c.2.2.1
                                            have p739_3 := h739c.2.2.2
                                            linarith only [h4, hlam, p739_0]
                                          · have p739_0 := h739c.1
                                            have p739_1 := h739c.2.1
                                            have p739_2 := h739c.2.2.1
                                            have p739_3 := h739c.2.2.2
                                            linarith only [h570, hlam, p739_0]
                                          · have p739_0 := h739c.1
                                            have p739_1 := h739c.2.1
                                            have p739_2 := h739c.2.2.1
                                            have p739_3 := h739c.2.2.2
                                            rcases p739_3 (m.d 0 2) (by simp) with h744 | h744
                                            · rcases p739_3 (m.d 1 2) (by simp) with h745 | h745
                                              · linarith only [h0, h745, hlam]
                                              · linarith only [h699, h745, hlam]
                                            · linarith only [h744, hlam, p739_0]
                                          · have p739_0 := h739c.1
                                            have p739_1 := h739c.2.1
                                            have p739_2 := h739c.2.2.1
                                            have p739_3 := h739c.2.2.2
                                            linarith only [h0, hlam, p739_1]
                                          · have p739_0 := h739c.1
                                            have p739_1 := h739c.2.1
                                            have p739_2 := h739c.2.2.1
                                            have p739_3 := h739c.2.2.2
                                            linarith only [hlam, p739_0]
                                          · have p739_0 := h739c.1
                                            have p739_1 := h739c.2.1
                                            have p739_2 := h739c.2.2.1
                                            have p739_3 := h739c.2.2.2
                                            linarith only [h695, hlam, p739_0]
                                          · have p739_0 := h739c.1
                                            have p739_1 := h739c.2.1
                                            have p739_2 := h739c.2.2.1
                                            have p739_3 := h739c.2.2.2
                                            linarith only [h697, hlam, p739_0]
                                          · have p739_0 := h739c.1
                                            have p739_1 := h739c.2.1
                                            have p739_2 := h739c.2.2.1
                                            have p739_3 := h739c.2.2.2
                                            rcases p739_3 (m.d 0 2) (by simp) with h753 | h753
                                            · rcases p739_3 (m.d 1 2) (by simp) with h754 | h754
                                              · rcases p739_3 (m.d 2 3) (by simp) with h755 | h755
                                                · rcases p739_3 (m.d 2 4) (by simp) with h756 | h756
                                                  · rcases p739_3 (m.d 2 5) (by simp) with h757 | h757
                                                    · linarith only [h757, hlam, p739_0]
                                                    · rcases h4bigk with h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c
                                                      · have p759_0 := h759c.1
                                                        have p759_1 := h759c.2.1
                                                        have p759_2 := h759c.2.2.1
                                                        have p759_3 := h759c.2.2.2
                                                        linarith only [hlam, p759_0]
                                                      · have p759_0 := h759c.1
                                                        have p759_1 := h759c.2.1
                                                        have p759_2 := h759c.2.2.1
                                                        have p759_3 := h759c.2.2.2
                                                        linarith only [h4, h693, h697, h699, h704, h706, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p707_1, p759_1]
                                                      · have p759_0 := h759c.1
                                                        have p759_1 := h759c.2.1
                                                        have p759_2 := h759c.2.2.1
                                                        have p759_3 := h759c.2.2.2
                                                        linarith only [h570, hlam, p759_1]
                                                      · have p759_0 := h759c.1
                                                        have p759_1 := h759c.2.1
                                                        have p759_2 := h759c.2.2.1
                                                        have p759_3 := h759c.2.2.2
                                                        rcases p759_3 (m.d 0 4) (by simp) with h763 | h763
                                                        · rcases p759_3 (m.d 1 4) (by simp) with h764 | h764
                                                          · linarith only [h2, h764, hlam]
                                                          · linarith only [h700, h764, hlam]
                                                        · linarith only [h693, h763, hlam]
                                                      · have p759_0 := h759c.1
                                                        have p759_1 := h759c.2.1
                                                        have p759_2 := h759c.2.2.1
                                                        have p759_3 := h759c.2.2.2
                                                        rcases p759_3 (m.d 0 4) (by simp) with h768 | h768
                                                        · rcases p759_3 (m.d 1 4) (by simp) with h769 | h769
                                                          · linarith only [h2, h769, hlam]
                                                          · linarith only [h702, h769, hlam]
                                                        · linarith only [h768, hlam, p759_0]
                                                      · have p759_0 := h759c.1
                                                        have p759_1 := h759c.2.1
                                                        have p759_2 := h759c.2.2.1
                                                        have p759_3 := h759c.2.2.2
                                                        linarith only [h2, hlam, p759_0]
                                                      · have p759_0 := h759c.1
                                                        have p759_1 := h759c.2.1
                                                        have p759_2 := h759c.2.2.1
                                                        have p759_3 := h759c.2.2.2
                                                        linarith only [hlam, p759_0]
                                                      · have p759_0 := h759c.1
                                                        have p759_1 := h759c.2.1
                                                        have p759_2 := h759c.2.2.1
                                                        have p759_3 := h759c.2.2.2
                                                        linarith only [h697, hlam, p759_1]
                                                      · have p759_0 := h759c.1
                                                        have p759_1 := h759c.2.1
                                                        have p759_2 := h759c.2.2.1
                                                        have p759_3 := h759c.2.2.2
                                                        linarith only [h1, h700, h706, hc01, hc45, hlam, hphi, ht0b, ht5b, p759_1]
                                                      · have p759_0 := h759c.1
                                                        have p759_1 := h759c.2.1
                                                        have p759_2 := h759c.2.2.1
                                                        have p759_3 := h759c.2.2.2
                                                        rcases p759_3 (m.d 0 4) (by simp) with h777 | h777
                                                        · rcases p759_3 (m.d 1 4) (by simp) with h778 | h778
                                                          · rcases p759_3 (m.d 2 4) (by simp) with h779 | h779
                                                            · rcases p759_3 (m.d 3 4) (by simp) with h780 | h780
                                                              · linarith only [h700, h780, hlam]
                                                              · linarith only [h706, h780, hlam]
                                                            · linarith only [h705, h779, hlam]
                                                          · linarith only [h778, hlam, p759_0]
                                                        · linarith only [h694, h777, hlam]
                                                      · have p759_0 := h759c.1
                                                        have p759_1 := h759c.2.1
                                                        have p759_2 := h759c.2.2.1
                                                        have p759_3 := h759c.2.2.2
                                                        linarith only [h0, h570, h699, h703, h704, h706, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p707_1, p759_1]
                                                      · have p759_0 := h759c.1
                                                        have p759_1 := h759c.2.1
                                                        have p759_2 := h759c.2.2.1
                                                        have p759_3 := h759c.2.2.2
                                                        linarith only [h697, h699, h703, h704, h706, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p707_1, p759_1]
                                                      · have p759_0 := h759c.1
                                                        have p759_1 := h759c.2.1
                                                        have p759_2 := h759c.2.2.1
                                                        have p759_3 := h759c.2.2.2
                                                        linarith only [hlam, p759_0]
                                                      · have p759_0 := h759c.1
                                                        have p759_1 := h759c.2.1
                                                        have p759_2 := h759c.2.2.1
                                                        have p759_3 := h759c.2.2.2
                                                        rcases p759_3 (m.d 0 4) (by simp) with h789 | h789
                                                        · linarith only [h570, h789, hlam]
                                                        · linarith only [h693, h789, hlam]
                                                      · have p759_0 := h759c.1
                                                        have p759_1 := h759c.2.1
                                                        have p759_2 := h759c.2.2.1
                                                        have p759_3 := h759c.2.2.2
                                                        linarith only [h0, h570, h699, h704, h706, hlam, p707_1, p759_2]
                                                      · have p759_0 := h759c.1
                                                        have p759_1 := h759c.2.1
                                                        have p759_2 := h759c.2.2.1
                                                        have p759_3 := h759c.2.2.2
                                                        linarith only [h693, hlam, p759_0]
                                                      · have p759_0 := h759c.1
                                                        have p759_1 := h759c.2.1
                                                        have p759_2 := h759c.2.2.1
                                                        have p759_3 := h759c.2.2.2
                                                        linarith only [h700, hlam, p759_0]
                                                      · have p759_0 := h759c.1
                                                        have p759_1 := h759c.2.1
                                                        have p759_2 := h759c.2.2.1
                                                        have p759_3 := h759c.2.2.2
                                                        linarith only [h703, hlam, p759_0]
                                                      · have p759_0 := h759c.1
                                                        have p759_1 := h759c.2.1
                                                        have p759_2 := h759c.2.2.1
                                                        have p759_3 := h759c.2.2.2
                                                        linarith only [hlam, p759_0]
                                                      · have p759_0 := h759c.1
                                                        have p759_1 := h759c.2.1
                                                        have p759_2 := h759c.2.2.1
                                                        have p759_3 := h759c.2.2.2
                                                        linarith only [h1, h700, hc01, hc45, hlam, hphi, ht0b, ht5b, p759_1]
                                                      · have p759_0 := h759c.1
                                                        have p759_1 := h759c.2.1
                                                        have p759_2 := h759c.2.2.1
                                                        have p759_3 := h759c.2.2.2
                                                        linarith only [h694, hlam, p759_0]
                                                      · have p759_0 := h759c.1
                                                        have p759_1 := h759c.2.1
                                                        have p759_2 := h759c.2.2.1
                                                        have p759_3 := h759c.2.2.2
                                                        linarith only [h702, hlam, p759_0]
                                                      · have p759_0 := h759c.1
                                                        have p759_1 := h759c.2.1
                                                        have p759_2 := h759c.2.2.1
                                                        have p759_3 := h759c.2.2.2
                                                        linarith only [h705, hlam, p759_0]
                                                      · have p759_0 := h759c.1
                                                        have p759_1 := h759c.2.1
                                                        have p759_2 := h759c.2.2.1
                                                        have p759_3 := h759c.2.2.2
                                                        linarith only [h706, hlam, p759_0]
                                                      · have p759_0 := h759c.1
                                                        have p759_1 := h759c.2.1
                                                        have p759_2 := h759c.2.2.1
                                                        have p759_3 := h759c.2.2.2
                                                        linarith only [hlam, p759_0]
                                                  · linarith only [h705, h756, hlam]
                                                · linarith only [h704, h755, hlam]
                                              · linarith only [h754, hlam, p739_0]
                                            · linarith only [h692, h753, hlam]
                                          · have p739_0 := h739c.1
                                            have p739_1 := h739c.2.1
                                            have p739_2 := h739c.2.2.1
                                            have p739_3 := h739c.2.2.2
                                            linarith only [h0, h699, h704, h706, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p707_1, p739_1]
                                          · have p739_0 := h739c.1
                                            have p739_1 := h739c.2.1
                                            have p739_2 := h739c.2.2.1
                                            have p739_3 := h739c.2.2.2
                                            linarith only [h699, h704, h706, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p707_1, p739_1]
                                          · have p739_0 := h739c.1
                                            have p739_1 := h739c.2.1
                                            have p739_2 := h739c.2.2.1
                                            have p739_3 := h739c.2.2.2
                                            linarith only [hlam, p739_0]
                                          · have p739_0 := h739c.1
                                            have p739_1 := h739c.2.1
                                            have p739_2 := h739c.2.2.1
                                            have p739_3 := h739c.2.2.2
                                            linarith only [h0, h570, h699, h704, h706, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p707_1, p739_1]
                                          · have p739_0 := h739c.1
                                            have p739_1 := h739c.2.1
                                            have p739_2 := h739c.2.2.1
                                            have p739_3 := h739c.2.2.2
                                            linarith only [h0, h4, h699, hlam, p707_1, p739_2]
                                          · have p739_0 := h739c.1
                                            have p739_1 := h739c.2.1
                                            have p739_2 := h739c.2.2.1
                                            have p739_3 := h739c.2.2.2
                                            linarith only [h0, h699, h704, h706, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p707_1, p739_1]
                                          · have p739_0 := h739c.1
                                            have p739_1 := h739c.2.1
                                            have p739_2 := h739c.2.2.1
                                            have p739_3 := h739c.2.2.2
                                            linarith only [h699, h704, h706, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p707_1, p739_1]
                                          · have p739_0 := h739c.1
                                            have p739_1 := h739c.2.1
                                            have p739_2 := h739c.2.2.1
                                            have p739_3 := h739c.2.2.2
                                            linarith only [h703, hlam, p739_0]
                                          · have p739_0 := h739c.1
                                            have p739_1 := h739c.2.1
                                            have p739_2 := h739c.2.2.1
                                            have p739_3 := h739c.2.2.2
                                            linarith only [hlam, p739_0]
                                          · have p739_0 := h739c.1
                                            have p739_1 := h739c.2.1
                                            have p739_2 := h739c.2.2.1
                                            have p739_3 := h739c.2.2.2
                                            linarith only [h0, h570, h699, hlam, p707_1, p739_2]
                                          · have p739_0 := h739c.1
                                            have p739_1 := h739c.2.1
                                            have p739_2 := h739c.2.2.1
                                            have p739_3 := h739c.2.2.2
                                            linarith only [h692, hlam, p739_0]
                                          · have p739_0 := h739c.1
                                            have p739_1 := h739c.2.1
                                            have p739_2 := h739c.2.2.1
                                            have p739_3 := h739c.2.2.2
                                            linarith only [h699, hlam, p739_0]
                                          · have p739_0 := h739c.1
                                            have p739_1 := h739c.2.1
                                            have p739_2 := h739c.2.2.1
                                            have p739_3 := h739c.2.2.2
                                            linarith only [h704, hlam, p739_0]
                                          · have p739_0 := h739c.1
                                            have p739_1 := h739c.2.1
                                            have p739_2 := h739c.2.2.1
                                            have p739_3 := h739c.2.2.2
                                            linarith only [h705, hlam, p739_1]
                                          · have p739_0 := h739c.1
                                            have p739_1 := h739c.2.1
                                            have p739_2 := h739c.2.2.1
                                            have p739_3 := h739c.2.2.2
                                            linarith only [hlam, p739_0]
                                      · linarith only [h702, h736, hlam]
                                    · linarith only [h701, h735, hlam]
                                  · linarith only [h699, h734, hlam]
                                · linarith only [h3, h733, hlam]
                              · have p707_0 := h707c.1
                                have p707_1 := h707c.2.1
                                have p707_2 := h707c.2.2.1
                                have p707_3 := h707c.2.2.2
                                linarith only [h1, hlam, p707_0]
                              · have p707_0 := h707c.1
                                have p707_1 := h707c.2.1
                                have p707_2 := h707c.2.2.1
                                have p707_3 := h707c.2.2.2
                                linarith only [h1, h699, h704, h706, hc01, hc45, hlam, hphi, ht0b, ht5b, p707_1]
                              · have p707_0 := h707c.1
                                have p707_1 := h707c.2.1
                                have p707_2 := h707c.2.2.1
                                have p707_3 := h707c.2.2.2
                                linarith only [hlam, p707_0]
                              · have p707_0 := h707c.1
                                have p707_1 := h707c.2.1
                                have p707_2 := h707c.2.2.1
                                have p707_3 := h707c.2.2.2
                                linarith only [h1, h697, h699, h704, h706, hc01, hc45, hlam, hphi, ht0b, ht5b, p707_1]
                              · have p707_0 := h707c.1
                                have p707_1 := h707c.2.1
                                have p707_2 := h707c.2.2.1
                                have p707_3 := h707c.2.2.2
                                rcases p707_3 (m.d 0 1) (by simp) with h830 | h830
                                · rcases p707_3 (m.d 1 2) (by simp) with h831 | h831
                                  · linarith only [h695, h831, hlam]
                                  · linarith only [h699, h831, hlam]
                                · linarith only [h3, h830, hlam]
                              · have p707_0 := h707c.1
                                have p707_1 := h707c.2.1
                                have p707_2 := h707c.2.2.1
                                have p707_3 := h707c.2.2.2
                                linarith only [h2, hlam, p707_0]
                              · have p707_0 := h707c.1
                                have p707_1 := h707c.2.1
                                have p707_2 := h707c.2.2.1
                                have p707_3 := h707c.2.2.2
                                linarith only [h2, h699, h704, h706, hc01, hc45, hlam, hphi, ht0b, ht5b, p707_1]
                              · have p707_0 := h707c.1
                                have p707_1 := h707c.2.1
                                have p707_2 := h707c.2.2.1
                                have p707_3 := h707c.2.2.2
                                linarith only [h700, hlam, p707_1]
                              · have p707_0 := h707c.1
                                have p707_1 := h707c.2.1
                                have p707_2 := h707c.2.2.1
                                have p707_3 := h707c.2.2.2
                                linarith only [hlam, p707_0]
                              · have p707_0 := h707c.1
                                have p707_1 := h707c.2.1
                                have p707_2 := h707c.2.2.1
                                have p707_3 := h707c.2.2.2
                                rcases p707_3 (m.d 0 1) (by simp) with h839 | h839
                                · rcases p707_3 (m.d 1 2) (by simp) with h840 | h840
                                  · linarith only [h697, h840, hlam]
                                  · linarith only [h699, h840, hlam]
                                · linarith only [h3, h839, hlam]
                              · have p707_0 := h707c.1
                                have p707_1 := h707c.2.1
                                have p707_2 := h707c.2.2.1
                                have p707_3 := h707c.2.2.2
                                linarith only [h3, hlam, p707_0]
                              · have p707_0 := h707c.1
                                have p707_1 := h707c.2.1
                                have p707_2 := h707c.2.2.1
                                have p707_3 := h707c.2.2.2
                                linarith only [h699, hlam, p707_0]
                              · have p707_0 := h707c.1
                                have p707_1 := h707c.2.1
                                have p707_2 := h707c.2.2.1
                                have p707_3 := h707c.2.2.2
                                linarith only [h701, hlam, p707_0]
                              · have p707_0 := h707c.1
                                have p707_1 := h707c.2.1
                                have p707_2 := h707c.2.2.1
                                have p707_3 := h707c.2.2.2
                                linarith only [h702, hlam, p707_0]
                              · have p707_0 := h707c.1
                                have p707_1 := h707c.2.1
                                have p707_2 := h707c.2.2.1
                                have p707_3 := h707c.2.2.2
                                linarith only [hlam, p707_0]
                            · linarith only [h706, hc34, hlam, hphi, ht45, u5elo4]
                          · linarith only [h570, h705, hc04, hlam, hphi, ht45, u5elo4]
                        · linarith only [h4, h704, hc03, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h0, h4, h693, h699, h703, hc03, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h697, h699, h702, hc25, hlam, hphi, u5elo4]
                  · linarith only [h697, h699, h700, h701, hc25, hlam, hphi, u5elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h855 | h855
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h856 | h856
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h857 | h857
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h858 | h858
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h859 | h859
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h860 | h860
                            · rcases h1bigk with h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c
                              · have p861_0 := h861c.1
                                have p861_1 := h861c.2.1
                                have p861_2 := h861c.2.2.1
                                have p861_3 := h861c.2.2.2
                                linarith only [hlam, p861_0]
                              · have p861_0 := h861c.1
                                have p861_1 := h861c.2.1
                                have p861_2 := h861c.2.2.1
                                have p861_3 := h861c.2.2.2
                                rcases p861_3 (m.d 0 1) (by simp) with h863 | h863
                                · rcases p861_3 (m.d 1 2) (by simp) with h864 | h864
                                  · linarith only [h864, hlam, p861_0]
                                  · rcases p861_3 (m.d 1 3) (by simp) with h866 | h866
                                    · linarith only [h1, h866, hlam]
                                    · linarith only [h695, h866, hlam]
                                · linarith only [h863, hlam, p861_0]
                              · have p861_0 := h861c.1
                                have p861_1 := h861c.2.1
                                have p861_2 := h861c.2.2.1
                                have p861_3 := h861c.2.2.2
                                rcases p861_3 (m.d 0 1) (by simp) with h870 | h870
                                · rcases p861_3 (m.d 1 2) (by simp) with h871 | h871
                                  · linarith only [h0, h871, hlam]
                                  · rcases p861_3 (m.d 1 3) (by simp) with h873 | h873
                                    · linarith only [h873, hlam, p861_0]
                                    · rcases p861_3 (m.d 1 4) (by simp) with h875 | h875
                                      · linarith only [h2, h875, hlam]
                                      · linarith only [h700, h875, hlam]
                                · linarith only [h870, hlam, p861_0]
                              · have p861_0 := h861c.1
                                have p861_1 := h861c.2.1
                                have p861_2 := h861c.2.2.1
                                have p861_3 := h861c.2.2.2
                                rcases p861_3 (m.d 0 1) (by simp) with h879 | h879
                                · rcases p861_3 (m.d 1 2) (by simp) with h880 | h880
                                  · linarith only [h0, h880, hlam]
                                  · rcases p861_3 (m.d 1 3) (by simp) with h882 | h882
                                    · linarith only [h1, h882, hlam]
                                    · rcases p861_3 (m.d 1 4) (by simp) with h884 | h884
                                      · linarith only [h884, hlam, p861_0]
                                      · rcases p861_3 (m.d 1 5) (by simp) with h886 | h886
                                        · linarith only [h3, h886, hlam]
                                        · rcases h2bigk with h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c
                                          · have p888_0 := h888c.1
                                            have p888_1 := h888c.2.1
                                            have p888_2 := h888c.2.2.1
                                            have p888_3 := h888c.2.2.2
                                            linarith only [hlam, p888_0]
                                          · have p888_0 := h888c.1
                                            have p888_1 := h888c.2.1
                                            have p888_2 := h888c.2.2.1
                                            have p888_3 := h888c.2.2.2
                                            linarith only [h4, h699, h858, h860, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p888_1]
                                          · have p888_0 := h888c.1
                                            have p888_1 := h888c.2.1
                                            have p888_2 := h888c.2.2.1
                                            have p888_3 := h888c.2.2.2
                                            linarith only [h4, hlam, p888_0]
                                          · have p888_0 := h888c.1
                                            have p888_1 := h888c.2.1
                                            have p888_2 := h888c.2.2.1
                                            have p888_3 := h888c.2.2.2
                                            linarith only [h570, hlam, p888_0]
                                          · have p888_0 := h888c.1
                                            have p888_1 := h888c.2.1
                                            have p888_2 := h888c.2.2.1
                                            have p888_3 := h888c.2.2.2
                                            rcases p888_3 (m.d 0 2) (by simp) with h893 | h893
                                            · rcases p888_3 (m.d 1 2) (by simp) with h894 | h894
                                              · linarith only [h0, h894, hlam]
                                              · linarith only [h699, h894, hlam]
                                            · linarith only [h893, hlam, p888_0]
                                          · have p888_0 := h888c.1
                                            have p888_1 := h888c.2.1
                                            have p888_2 := h888c.2.2.1
                                            have p888_3 := h888c.2.2.2
                                            linarith only [h0, hlam, p888_1]
                                          · have p888_0 := h888c.1
                                            have p888_1 := h888c.2.1
                                            have p888_2 := h888c.2.2.1
                                            have p888_3 := h888c.2.2.2
                                            linarith only [hlam, p888_0]
                                          · have p888_0 := h888c.1
                                            have p888_1 := h888c.2.1
                                            have p888_2 := h888c.2.2.1
                                            have p888_3 := h888c.2.2.2
                                            linarith only [h695, hlam, p888_0]
                                          · have p888_0 := h888c.1
                                            have p888_1 := h888c.2.1
                                            have p888_2 := h888c.2.2.1
                                            have p888_3 := h888c.2.2.2
                                            linarith only [h697, hlam, p888_0]
                                          · have p888_0 := h888c.1
                                            have p888_1 := h888c.2.1
                                            have p888_2 := h888c.2.2.1
                                            have p888_3 := h888c.2.2.2
                                            linarith only [h695, h700, h858, h860, hc01, hc45, hlam, hphi, ht0b, ht5b, p861_1, p888_1]
                                          · have p888_0 := h888c.1
                                            have p888_1 := h888c.2.1
                                            have p888_2 := h888c.2.2.1
                                            have p888_3 := h888c.2.2.2
                                            rcases p888_3 (m.d 0 2) (by simp) with h903 | h903
                                            · linarith only [h903, hlam, p888_0]
                                            · rcases p888_3 (m.d 1 2) (by simp) with h905 | h905
                                              · linarith only [h695, h905, hlam]
                                              · rcases p888_3 (m.d 2 3) (by simp) with h907 | h907
                                                · rcases p888_3 (m.d 2 4) (by simp) with h908 | h908
                                                  · linarith only [h857, h908, hlam]
                                                  · linarith only [h570, h908, hlam]
                                                · linarith only [h907, hlam, p888_0]
                                          · have p888_0 := h888c.1
                                            have p888_1 := h888c.2.1
                                            have p888_2 := h888c.2.2.1
                                            have p888_3 := h888c.2.2.2
                                            rcases p888_3 (m.d 0 2) (by simp) with h912 | h912
                                            · linarith only [h4, h912, hlam]
                                            · linarith only [h0, h912, hlam]
                                          · have p888_0 := h888c.1
                                            have p888_1 := h888c.2.1
                                            have p888_2 := h888c.2.2.1
                                            have p888_3 := h888c.2.2.2
                                            linarith only [hlam, p888_0]
                                          · have p888_0 := h888c.1
                                            have p888_1 := h888c.2.1
                                            have p888_2 := h888c.2.2.1
                                            have p888_3 := h888c.2.2.2
                                            linarith only [h570, hc02, hc23, hlam, hphi, p888_1]
                                          · have p888_0 := h888c.1
                                            have p888_1 := h888c.2.1
                                            have p888_2 := h888c.2.2.1
                                            have p888_3 := h888c.2.2.2
                                            linarith only [h4, h693, h695, h699, h700, hlam, p888_2]
                                          · have p888_0 := h888c.1
                                            have p888_1 := h888c.2.1
                                            have p888_2 := h888c.2.2.1
                                            have p888_3 := h888c.2.2.2
                                            rcases p888_3 (m.d 0 2) (by simp) with h918 | h918
                                            · linarith only [h918, hlam, p888_0]
                                            · rcases p888_3 (m.d 1 2) (by simp) with h920 | h920
                                              · linarith only [h697, h920, hlam]
                                              · rcases p888_3 (m.d 2 3) (by simp) with h922 | h922
                                                · rcases p888_3 (m.d 2 4) (by simp) with h923 | h923
                                                  · rcases p888_3 (m.d 2 5) (by simp) with h924 | h924
                                                    · linarith only [h859, h924, hlam]
                                                    · rcases h4bigk with h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c
                                                      · have p926_0 := h926c.1
                                                        have p926_1 := h926c.2.1
                                                        have p926_2 := h926c.2.2.1
                                                        have p926_3 := h926c.2.2.2
                                                        linarith only [hlam, p926_0]
                                                      · have p926_0 := h926c.1
                                                        have p926_1 := h926c.2.1
                                                        have p926_2 := h926c.2.2.1
                                                        have p926_3 := h926c.2.2.2
                                                        rcases p926_3 (m.d 0 4) (by simp) with h928 | h928
                                                        · rcases p926_3 (m.d 1 4) (by simp) with h929 | h929
                                                          · linarith only [h2, h929, hlam]
                                                          · rcases p926_3 (m.d 2 4) (by simp) with h931 | h931
                                                            · rcases p926_3 (m.d 3 4) (by simp) with h932 | h932
                                                              · linarith only [h693, h932, hlam]
                                                              · linarith only [h700, h932, hlam]
                                                            · linarith only [h697, h931, hlam]
                                                        · linarith only [h2, h928, hlam]
                                                      · have p926_0 := h926c.1
                                                        have p926_1 := h926c.2.1
                                                        have p926_2 := h926c.2.2.1
                                                        have p926_3 := h926c.2.2.2
                                                        linarith only [h570, hlam, p926_1]
                                                      · have p926_0 := h926c.1
                                                        have p926_1 := h926c.2.1
                                                        have p926_2 := h926c.2.2.1
                                                        have p926_3 := h926c.2.2.2
                                                        linarith only [h570, h695, h700, h857, hc12, hc23, hlam, hphi, p926_1]
                                                      · have p926_0 := h926c.1
                                                        have p926_1 := h926c.2.1
                                                        have p926_2 := h926c.2.2.1
                                                        have p926_3 := h926c.2.2.2
                                                        rcases p926_3 (m.d 0 4) (by simp) with h939 | h939
                                                        · rcases p926_3 (m.d 1 4) (by simp) with h940 | h940
                                                          · linarith only [h2, h940, hlam]
                                                          · linarith only [h856, h940, hlam]
                                                        · linarith only [h939, hlam, p926_0]
                                                      · have p926_0 := h926c.1
                                                        have p926_1 := h926c.2.1
                                                        have p926_2 := h926c.2.2.1
                                                        have p926_3 := h926c.2.2.2
                                                        linarith only [h2, hlam, p926_0]
                                                      · have p926_0 := h926c.1
                                                        have p926_1 := h926c.2.1
                                                        have p926_2 := h926c.2.2.1
                                                        have p926_3 := h926c.2.2.2
                                                        linarith only [hlam, p926_0]
                                                      · have p926_0 := h926c.1
                                                        have p926_1 := h926c.2.1
                                                        have p926_2 := h926c.2.2.1
                                                        have p926_3 := h926c.2.2.2
                                                        linarith only [h697, hlam, p926_1]
                                                      · have p926_0 := h926c.1
                                                        have p926_1 := h926c.2.1
                                                        have p926_2 := h926c.2.2.1
                                                        have p926_3 := h926c.2.2.2
                                                        linarith only [h700, hlam, p926_1]
                                                      · have p926_0 := h926c.1
                                                        have p926_1 := h926c.2.1
                                                        have p926_2 := h926c.2.2.1
                                                        have p926_3 := h926c.2.2.2
                                                        linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p861_1, p926_1]
                                                      · have p926_0 := h926c.1
                                                        have p926_1 := h926c.2.1
                                                        have p926_2 := h926c.2.2.1
                                                        have p926_3 := h926c.2.2.2
                                                        linarith only [h693, h695, h700, h857, hc12, hc23, hlam, hphi, p926_1]
                                                      · have p926_0 := h926c.1
                                                        have p926_1 := h926c.2.1
                                                        have p926_2 := h926c.2.2.1
                                                        have p926_3 := h926c.2.2.2
                                                        rcases p926_3 (m.d 0 4) (by simp) with h950 | h950
                                                        · linarith only [h570, h950, hlam]
                                                        · linarith only [h2, h950, hlam]
                                                      · have p926_0 := h926c.1
                                                        have p926_1 := h926c.2.1
                                                        have p926_2 := h926c.2.2.1
                                                        have p926_3 := h926c.2.2.2
                                                        linarith only [hlam, p926_0]
                                                      · have p926_0 := h926c.1
                                                        have p926_1 := h926c.2.1
                                                        have p926_2 := h926c.2.2.1
                                                        have p926_3 := h926c.2.2.2
                                                        linarith only [h695, h699, h700, h857, h858, h860, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p926_1]
                                                      · have p926_0 := h926c.1
                                                        have p926_1 := h926c.2.1
                                                        have p926_2 := h926c.2.2.1
                                                        have p926_3 := h926c.2.2.2
                                                        linarith only [h0, h699, h858, h860, hlam, p888_1, p926_2]
                                                      · have p926_0 := h926c.1
                                                        have p926_1 := h926c.2.1
                                                        have p926_2 := h926c.2.2.1
                                                        have p926_3 := h926c.2.2.2
                                                        linarith only [h693, hlam, p926_0]
                                                      · have p926_0 := h926c.1
                                                        have p926_1 := h926c.2.1
                                                        have p926_2 := h926c.2.2.1
                                                        have p926_3 := h926c.2.2.2
                                                        linarith only [h1, h693, hlam, p861_2, p926_1]
                                                      · have p926_0 := h926c.1
                                                        have p926_1 := h926c.2.1
                                                        have p926_2 := h926c.2.2.1
                                                        have p926_3 := h926c.2.2.2
                                                        linarith only [h857, hlam, p926_0]
                                                      · have p926_0 := h926c.1
                                                        have p926_1 := h926c.2.1
                                                        have p926_2 := h926c.2.2.1
                                                        have p926_3 := h926c.2.2.2
                                                        linarith only [hlam, p926_0]
                                                      · have p926_0 := h926c.1
                                                        have p926_1 := h926c.2.1
                                                        have p926_2 := h926c.2.2.1
                                                        have p926_3 := h926c.2.2.2
                                                        rcases p926_3 (m.d 0 4) (by simp) with h960 | h960
                                                        · rcases p926_3 (m.d 1 4) (by simp) with h961 | h961
                                                          · linarith only [h700, h961, hlam]
                                                          · linarith only [h856, h961, hlam]
                                                        · linarith only [h694, h960, hlam]
                                                      · have p926_0 := h926c.1
                                                        have p926_1 := h926c.2.1
                                                        have p926_2 := h926c.2.2.1
                                                        have p926_3 := h926c.2.2.2
                                                        linarith only [h694, hlam, p926_0]
                                                      · have p926_0 := h926c.1
                                                        have p926_1 := h926c.2.1
                                                        have p926_2 := h926c.2.2.1
                                                        have p926_3 := h926c.2.2.2
                                                        linarith only [h856, hlam, p926_0]
                                                      · have p926_0 := h926c.1
                                                        have p926_1 := h926c.2.1
                                                        have p926_2 := h926c.2.2.1
                                                        have p926_3 := h926c.2.2.2
                                                        linarith only [h859, hlam, p926_0]
                                                      · have p926_0 := h926c.1
                                                        have p926_1 := h926c.2.1
                                                        have p926_2 := h926c.2.2.1
                                                        have p926_3 := h926c.2.2.2
                                                        linarith only [h860, hlam, p926_0]
                                                      · have p926_0 := h926c.1
                                                        have p926_1 := h926c.2.1
                                                        have p926_2 := h926c.2.2.1
                                                        have p926_3 := h926c.2.2.2
                                                        linarith only [hlam, p926_0]
                                                  · linarith only [h923, hlam, p888_0]
                                                · linarith only [h4, h922, hlam]
                                          · have p888_0 := h888c.1
                                            have p888_1 := h888c.2.1
                                            have p888_2 := h888c.2.2.1
                                            have p888_3 := h888c.2.2.2
                                            rcases p888_3 (m.d 0 2) (by simp) with h972 | h972
                                            · linarith only [h570, h972, hlam]
                                            · linarith only [h0, h972, hlam]
                                          · have p888_0 := h888c.1
                                            have p888_1 := h888c.2.1
                                            have p888_2 := h888c.2.2.1
                                            have p888_3 := h888c.2.2.2
                                            linarith only [h857, hlam, p888_0]
                                          · have p888_0 := h888c.1
                                            have p888_1 := h888c.2.1
                                            have p888_2 := h888c.2.2.1
                                            have p888_3 := h888c.2.2.2
                                            linarith only [hlam, p888_0]
                                          · have p888_0 := h888c.1
                                            have p888_1 := h888c.2.1
                                            have p888_2 := h888c.2.2.1
                                            have p888_3 := h888c.2.2.2
                                            rcases p888_3 (m.d 0 2) (by simp) with h977 | h977
                                            · linarith only [h570, h977, hlam]
                                            · linarith only [h692, h977, hlam]
                                          · have p888_0 := h888c.1
                                            have p888_1 := h888c.2.1
                                            have p888_2 := h888c.2.2.1
                                            have p888_3 := h888c.2.2.2
                                            linarith only [h692, hlam, p888_0]
                                          · have p888_0 := h888c.1
                                            have p888_1 := h888c.2.1
                                            have p888_2 := h888c.2.2.1
                                            have p888_3 := h888c.2.2.2
                                            linarith only [h699, hlam, p888_0]
                                          · have p888_0 := h888c.1
                                            have p888_1 := h888c.2.1
                                            have p888_2 := h888c.2.2.1
                                            have p888_3 := h888c.2.2.2
                                            linarith only [h858, hlam, p888_0]
                                          · have p888_0 := h888c.1
                                            have p888_1 := h888c.2.1
                                            have p888_2 := h888c.2.2.1
                                            have p888_3 := h888c.2.2.2
                                            linarith only [h859, hlam, p888_1]
                                          · have p888_0 := h888c.1
                                            have p888_1 := h888c.2.1
                                            have p888_2 := h888c.2.2.1
                                            have p888_3 := h888c.2.2.2
                                            linarith only [hlam, p888_0]
                                · linarith only [h879, hlam, p861_0]
                              · have p861_0 := h861c.1
                                have p861_1 := h861c.2.1
                                have p861_2 := h861c.2.2.1
                                have p861_3 := h861c.2.2.2
                                rcases p861_3 (m.d 0 1) (by simp) with h986 | h986
                                · rcases p861_3 (m.d 1 2) (by simp) with h987 | h987
                                  · linarith only [h0, h987, hlam]
                                  · linarith only [h699, h987, hlam]
                                · linarith only [h986, hlam, p861_0]
                              · have p861_0 := h861c.1
                                have p861_1 := h861c.2.1
                                have p861_2 := h861c.2.2.1
                                have p861_3 := h861c.2.2.2
                                linarith only [h0, hlam, p861_0]
                              · have p861_0 := h861c.1
                                have p861_1 := h861c.2.1
                                have p861_2 := h861c.2.2.1
                                have p861_3 := h861c.2.2.2
                                linarith only [hlam, p861_0]
                              · have p861_0 := h861c.1
                                have p861_1 := h861c.2.1
                                have p861_2 := h861c.2.2.1
                                have p861_3 := h861c.2.2.2
                                linarith only [h695, hlam, p861_1]
                              · have p861_0 := h861c.1
                                have p861_1 := h861c.2.1
                                have p861_2 := h861c.2.2.1
                                have p861_3 := h861c.2.2.2
                                linarith only [h697, hlam, p861_1]
                              · have p861_0 := h861c.1
                                have p861_1 := h861c.2.1
                                have p861_2 := h861c.2.2.1
                                have p861_3 := h861c.2.2.2
                                linarith only [h1, h693, h695, h700, hc01, hc15, hlam, hphi, ht0b, ht5b, p861_1]
                              · have p861_0 := h861c.1
                                have p861_1 := h861c.2.1
                                have p861_2 := h861c.2.2.1
                                have p861_3 := h861c.2.2.2
                                linarith only [h1, hlam, p861_0]
                              · have p861_0 := h861c.1
                                have p861_1 := h861c.2.1
                                have p861_2 := h861c.2.2.1
                                have p861_3 := h861c.2.2.2
                                linarith only [h1, h693, h700, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p861_1]
                              · have p861_0 := h861c.1
                                have p861_1 := h861c.2.1
                                have p861_2 := h861c.2.2.1
                                have p861_3 := h861c.2.2.2
                                linarith only [hlam, p861_0]
                              · have p861_0 := h861c.1
                                have p861_1 := h861c.2.1
                                have p861_2 := h861c.2.2.1
                                have p861_3 := h861c.2.2.2
                                linarith only [h700, hlam, p861_0]
                              · have p861_0 := h861c.1
                                have p861_1 := h861c.2.1
                                have p861_2 := h861c.2.2.1
                                have p861_3 := h861c.2.2.2
                                linarith only [h4, h693, h699, h700, h858, h860, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p861_1]
                              · have p861_0 := h861c.1
                                have p861_1 := h861c.2.1
                                have p861_2 := h861c.2.2.1
                                have p861_3 := h861c.2.2.2
                                linarith only [h2, hlam, p861_0]
                              · have p861_0 := h861c.1
                                have p861_1 := h861c.2.1
                                have p861_2 := h861c.2.2.1
                                have p861_3 := h861c.2.2.2
                                linarith only [h2, h699, h858, h860, hc01, hc45, hlam, hphi, ht0b, ht5b, p861_1]
                              · have p861_0 := h861c.1
                                have p861_1 := h861c.2.1
                                have p861_2 := h861c.2.2.1
                                have p861_3 := h861c.2.2.2
                                linarith only [h4, h693, h695, h699, h700, h858, h860, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p861_1]
                              · have p861_0 := h861c.1
                                have p861_1 := h861c.2.1
                                have p861_2 := h861c.2.2.1
                                have p861_3 := h861c.2.2.2
                                linarith only [hlam, p861_0]
                              · have p861_0 := h861c.1
                                have p861_1 := h861c.2.1
                                have p861_2 := h861c.2.2.1
                                have p861_3 := h861c.2.2.2
                                rcases p861_3 (m.d 0 1) (by simp) with h1005 | h1005
                                · rcases p861_3 (m.d 1 2) (by simp) with h1006 | h1006
                                  · linarith only [h1006, h697, hlam]
                                  · linarith only [h1006, h699, hlam]
                                · linarith only [h1005, h3, hlam]
                              · have p861_0 := h861c.1
                                have p861_1 := h861c.2.1
                                have p861_2 := h861c.2.2.1
                                have p861_3 := h861c.2.2.2
                                linarith only [h3, hlam, p861_0]
                              · have p861_0 := h861c.1
                                have p861_1 := h861c.2.1
                                have p861_2 := h861c.2.2.1
                                have p861_3 := h861c.2.2.2
                                linarith only [h699, hlam, p861_0]
                              · have p861_0 := h861c.1
                                have p861_1 := h861c.2.1
                                have p861_2 := h861c.2.2.1
                                have p861_3 := h861c.2.2.2
                                linarith only [h855, hlam, p861_0]
                              · have p861_0 := h861c.1
                                have p861_1 := h861c.2.1
                                have p861_2 := h861c.2.2.1
                                have p861_3 := h861c.2.2.2
                                linarith only [h856, hlam, p861_0]
                              · have p861_0 := h861c.1
                                have p861_1 := h861c.2.1
                                have p861_2 := h861c.2.2.1
                                have p861_3 := h861c.2.2.2
                                linarith only [hlam, p861_0]
                            · linarith only [h700, h860, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h859, hc24, hlam, hphi, ht45, u5elo4]
                        · linarith only [h4, h693, h695, h700, h858, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h4, h693, h857, hlam]
                    · linarith only [h856, hc14, hlam, hphi, ht45, u5elo4]
                  · linarith only [h695, h699, h855, hc25, hlam, hphi, u5elo3]
              · linarith only [h699, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h694, hc04, hlam, hphi, ht45, u5elo4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1023 | h1023
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1024 | h1024
          · linarith only [h0, h1024, h4, h692, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1026 | h1026
            · linarith only [h0, h1026, h570, h692, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1028 | h1028
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1029 | h1029
                · linarith only [h0, h1, h1028, h1029, h4, h693, hc01, hc25, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1031 | h1031
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1032 | h1032
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1033 | h1033
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1034 | h1034
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1035 | h1035
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1036 | h1036
                            · rcases h1bigk with h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c | h1037c
                              · have p1037_0 := h1037c.1
                                have p1037_1 := h1037c.2.1
                                have p1037_2 := h1037c.2.2.1
                                have p1037_3 := h1037c.2.2.2
                                linarith only [hlam, p1037_0]
                              · have p1037_0 := h1037c.1
                                have p1037_1 := h1037c.2.1
                                have p1037_2 := h1037c.2.2.1
                                have p1037_3 := h1037c.2.2.2
                                rcases p1037_3 (m.d 0 1) (by simp) with h1039 | h1039
                                · rcases p1037_3 (m.d 1 2) (by simp) with h1040 | h1040
                                  · linarith only [h1040, hlam, p1037_0]
                                  · rcases p1037_3 (m.d 1 3) (by simp) with h1042 | h1042
                                    · linarith only [h1, h1042, hlam]
                                    · linarith only [h1024, h1042, hlam]
                                · linarith only [h1039, hlam, p1037_0]
                              · have p1037_0 := h1037c.1
                                have p1037_1 := h1037c.2.1
                                have p1037_2 := h1037c.2.2.1
                                have p1037_3 := h1037c.2.2.2
                                rcases p1037_3 (m.d 0 1) (by simp) with h1046 | h1046
                                · rcases p1037_3 (m.d 1 2) (by simp) with h1047 | h1047
                                  · linarith only [h0, h1047, hlam]
                                  · rcases p1037_3 (m.d 1 3) (by simp) with h1049 | h1049
                                    · linarith only [h1049, hlam, p1037_0]
                                    · rcases p1037_3 (m.d 1 4) (by simp) with h1051 | h1051
                                      · linarith only [h1051, h2, hlam]
                                      · linarith only [h1029, h1051, hlam]
                                · linarith only [h1046, hlam, p1037_0]
                              · have p1037_0 := h1037c.1
                                have p1037_1 := h1037c.2.1
                                have p1037_2 := h1037c.2.2.1
                                have p1037_3 := h1037c.2.2.2
                                rcases p1037_3 (m.d 0 1) (by simp) with h1055 | h1055
                                · rcases p1037_3 (m.d 1 2) (by simp) with h1056 | h1056
                                  · linarith only [h0, h1056, hlam]
                                  · rcases p1037_3 (m.d 1 3) (by simp) with h1058 | h1058
                                    · linarith only [h1, h1058, hlam]
                                    · rcases p1037_3 (m.d 1 4) (by simp) with h1060 | h1060
                                      · linarith only [h1060, hlam, p1037_0]
                                      · rcases p1037_3 (m.d 1 5) (by simp) with h1062 | h1062
                                        · linarith only [h1062, h3, hlam]
                                        · rcases h2bigk with h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c
                                          · have p1064_0 := h1064c.1
                                            have p1064_1 := h1064c.2.1
                                            have p1064_2 := h1064c.2.2.1
                                            have p1064_3 := h1064c.2.2.2
                                            linarith only [hlam, p1064_0]
                                          · have p1064_0 := h1064c.1
                                            have p1064_1 := h1064c.2.1
                                            have p1064_2 := h1064c.2.2.1
                                            have p1064_3 := h1064c.2.2.2
                                            linarith only [h1028, h1033, h1034, h1036, h4, h693, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1064_1]
                                          · have p1064_0 := h1064c.1
                                            have p1064_1 := h1064c.2.1
                                            have p1064_2 := h1064c.2.2.1
                                            have p1064_3 := h1064c.2.2.2
                                            linarith only [h4, hlam, p1064_0]
                                          · have p1064_0 := h1064c.1
                                            have p1064_1 := h1064c.2.1
                                            have p1064_2 := h1064c.2.2.1
                                            have p1064_3 := h1064c.2.2.2
                                            linarith only [h570, hlam, p1064_0]
                                          · have p1064_0 := h1064c.1
                                            have p1064_1 := h1064c.2.1
                                            have p1064_2 := h1064c.2.2.1
                                            have p1064_3 := h1064c.2.2.2
                                            linarith only [h1033, h1034, h1036, h4, h693, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1064_1]
                                          · have p1064_0 := h1064c.1
                                            have p1064_1 := h1064c.2.1
                                            have p1064_2 := h1064c.2.2.1
                                            have p1064_3 := h1064c.2.2.2
                                            linarith only [h0, hlam, p1064_1]
                                          · have p1064_0 := h1064c.1
                                            have p1064_1 := h1064c.2.1
                                            have p1064_2 := h1064c.2.2.1
                                            have p1064_3 := h1064c.2.2.2
                                            linarith only [hlam, p1064_0]
                                          · have p1064_0 := h1064c.1
                                            have p1064_1 := h1064c.2.1
                                            have p1064_2 := h1064c.2.2.1
                                            have p1064_3 := h1064c.2.2.2
                                            linarith only [h1024, hlam, p1064_0]
                                          · have p1064_0 := h1064c.1
                                            have p1064_1 := h1064c.2.1
                                            have p1064_2 := h1064c.2.2.1
                                            have p1064_3 := h1064c.2.2.2
                                            linarith only [h1026, hlam, p1064_0]
                                          · have p1064_0 := h1064c.1
                                            have p1064_1 := h1064c.2.1
                                            have p1064_2 := h1064c.2.2.1
                                            have p1064_3 := h1064c.2.2.2
                                            linarith only [h0, h1033, h1034, h1036, h4, h693, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1064_1]
                                          · have p1064_0 := h1064c.1
                                            have p1064_1 := h1064c.2.1
                                            have p1064_2 := h1064c.2.2.1
                                            have p1064_3 := h1064c.2.2.2
                                            rcases p1064_3 (m.d 0 2) (by simp) with h1075 | h1075
                                            · linarith only [h1075, hlam, p1064_0]
                                            · rcases p1064_3 (m.d 1 2) (by simp) with h1077 | h1077
                                              · linarith only [h1024, h1077, hlam]
                                              · rcases p1064_3 (m.d 2 3) (by simp) with h1079 | h1079
                                                · rcases p1064_3 (m.d 2 4) (by simp) with h1080 | h1080
                                                  · linarith only [h1033, h1080, hlam]
                                                  · linarith only [h1080, h570, hlam]
                                                · linarith only [h1079, hlam, p1064_0]
                                          · have p1064_0 := h1064c.1
                                            have p1064_1 := h1064c.2.1
                                            have p1064_2 := h1064c.2.2.1
                                            have p1064_3 := h1064c.2.2.2
                                            rcases p1064_3 (m.d 0 2) (by simp) with h1084 | h1084
                                            · linarith only [h1084, h4, hlam]
                                            · linarith only [h0, h1084, hlam]
                                          · have p1064_0 := h1064c.1
                                            have p1064_1 := h1064c.2.1
                                            have p1064_2 := h1064c.2.2.1
                                            have p1064_3 := h1064c.2.2.2
                                            linarith only [hlam, p1064_0]
                                          · have p1064_0 := h1064c.1
                                            have p1064_1 := h1064c.2.1
                                            have p1064_2 := h1064c.2.2.1
                                            have p1064_3 := h1064c.2.2.2
                                            linarith only [h1033, h4, h693, hc02, hc23, hlam, hphi, p1064_1]
                                          · have p1064_0 := h1064c.1
                                            have p1064_1 := h1064c.2.1
                                            have p1064_2 := h1064c.2.2.1
                                            have p1064_3 := h1064c.2.2.2
                                            linarith only [h0, h1028, h1033, h4, h693, hlam, p1064_2]
                                          · have p1064_0 := h1064c.1
                                            have p1064_1 := h1064c.2.1
                                            have p1064_2 := h1064c.2.2.1
                                            have p1064_3 := h1064c.2.2.2
                                            rcases p1064_3 (m.d 0 2) (by simp) with h1090 | h1090
                                            · linarith only [h1090, hlam, p1064_0]
                                            · rcases p1064_3 (m.d 1 2) (by simp) with h1092 | h1092
                                              · linarith only [h1026, h1092, hlam]
                                              · rcases p1064_3 (m.d 2 3) (by simp) with h1094 | h1094
                                                · rcases p1064_3 (m.d 2 4) (by simp) with h1095 | h1095
                                                  · rcases p1064_3 (m.d 2 5) (by simp) with h1096 | h1096
                                                    · linarith only [h1035, h1096, hlam]
                                                    · rcases h4bigk with h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c
                                                      · have p1098_0 := h1098c.1
                                                        have p1098_1 := h1098c.2.1
                                                        have p1098_2 := h1098c.2.2.1
                                                        have p1098_3 := h1098c.2.2.2
                                                        linarith only [hlam, p1098_0]
                                                      · have p1098_0 := h1098c.1
                                                        have p1098_1 := h1098c.2.1
                                                        have p1098_2 := h1098c.2.2.1
                                                        have p1098_3 := h1098c.2.2.2
                                                        linarith only [h1024, h1028, h1029, h1033, h1034, h1036, h693, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1098_1]
                                                      · have p1098_0 := h1098c.1
                                                        have p1098_1 := h1098c.2.1
                                                        have p1098_2 := h1098c.2.2.1
                                                        have p1098_3 := h1098c.2.2.2
                                                        linarith only [h570, hlam, p1098_1]
                                                      · have p1098_0 := h1098c.1
                                                        have p1098_1 := h1098c.2.1
                                                        have p1098_2 := h1098c.2.2.1
                                                        have p1098_3 := h1098c.2.2.2
                                                        linarith only [h693, hlam, p1098_1]
                                                      · have p1098_0 := h1098c.1
                                                        have p1098_1 := h1098c.2.1
                                                        have p1098_2 := h1098c.2.2.1
                                                        have p1098_3 := h1098c.2.2.2
                                                        rcases p1098_3 (m.d 0 4) (by simp) with h1103 | h1103
                                                        · rcases p1098_3 (m.d 1 4) (by simp) with h1104 | h1104
                                                          · linarith only [h1104, h2, hlam]
                                                          · linarith only [h1032, h1104, hlam]
                                                        · linarith only [h1103, hlam, p1098_0]
                                                      · have p1098_0 := h1098c.1
                                                        have p1098_1 := h1098c.2.1
                                                        have p1098_2 := h1098c.2.2.1
                                                        have p1098_3 := h1098c.2.2.2
                                                        linarith only [h2, hlam, p1098_0]
                                                      · have p1098_0 := h1098c.1
                                                        have p1098_1 := h1098c.2.1
                                                        have p1098_2 := h1098c.2.2.1
                                                        have p1098_3 := h1098c.2.2.2
                                                        linarith only [hlam, p1098_0]
                                                      · have p1098_0 := h1098c.1
                                                        have p1098_1 := h1098c.2.1
                                                        have p1098_2 := h1098c.2.2.1
                                                        have p1098_3 := h1098c.2.2.2
                                                        linarith only [h1026, hlam, p1098_1]
                                                      · have p1098_0 := h1098c.1
                                                        have p1098_1 := h1098c.2.1
                                                        have p1098_2 := h1098c.2.2.1
                                                        have p1098_3 := h1098c.2.2.2
                                                        linarith only [h1029, hlam, p1098_1]
                                                      · have p1098_0 := h1098c.1
                                                        have p1098_1 := h1098c.2.1
                                                        have p1098_2 := h1098c.2.2.1
                                                        have p1098_3 := h1098c.2.2.2
                                                        linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p1037_1, p1098_1]
                                                      · have p1098_0 := h1098c.1
                                                        have p1098_1 := h1098c.2.1
                                                        have p1098_2 := h1098c.2.2.1
                                                        have p1098_3 := h1098c.2.2.2
                                                        rcases p1098_3 (m.d 0 4) (by simp) with h1113 | h1113
                                                        · linarith only [h1113, h570, hlam]
                                                        · rcases p1098_3 (m.d 1 4) (by simp) with h1115 | h1115
                                                          · linarith only [h1026, h1115, hlam]
                                                          · rcases p1098_3 (m.d 2 4) (by simp) with h1117 | h1117
                                                            · rcases p1098_3 (m.d 3 4) (by simp) with h1118 | h1118
                                                              · linarith only [h1033, h1118, hlam]
                                                              · linarith only [h1118, h693, hlam]
                                                            · linarith only [h1117, h570, hlam]
                                                      · have p1098_0 := h1098c.1
                                                        have p1098_1 := h1098c.2.1
                                                        have p1098_2 := h1098c.2.2.1
                                                        have p1098_3 := h1098c.2.2.2
                                                        rcases p1098_3 (m.d 0 4) (by simp) with h1122 | h1122
                                                        · linarith only [h1122, h570, hlam]
                                                        · linarith only [h1122, h2, hlam]
                                                      · have p1098_0 := h1098c.1
                                                        have p1098_1 := h1098c.2.1
                                                        have p1098_2 := h1098c.2.2.1
                                                        have p1098_3 := h1098c.2.2.2
                                                        linarith only [hlam, p1098_0]
                                                      · have p1098_0 := h1098c.1
                                                        have p1098_1 := h1098c.2.1
                                                        have p1098_2 := h1098c.2.2.1
                                                        have p1098_3 := h1098c.2.2.2
                                                        linarith only [h0, h1028, h1033, h1034, h1036, h4, h693, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1098_1]
                                                      · have p1098_0 := h1098c.1
                                                        have p1098_1 := h1098c.2.1
                                                        have p1098_2 := h1098c.2.2.1
                                                        have p1098_3 := h1098c.2.2.2
                                                        linarith only [h0, h1028, h1034, h1036, hlam, p1064_1, p1098_2]
                                                      · have p1098_0 := h1098c.1
                                                        have p1098_1 := h1098c.2.1
                                                        have p1098_2 := h1098c.2.2.1
                                                        have p1098_3 := h1098c.2.2.2
                                                        linarith only [h0, h1028, h1033, h1034, h1036, h4, h693, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1098_1]
                                                      · have p1098_0 := h1098c.1
                                                        have p1098_1 := h1098c.2.1
                                                        have p1098_2 := h1098c.2.2.1
                                                        have p1098_3 := h1098c.2.2.2
                                                        linarith only [h1026, h1028, h1033, h1034, h1036, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1098_1]
                                                      · have p1098_0 := h1098c.1
                                                        have p1098_1 := h1098c.2.1
                                                        have p1098_2 := h1098c.2.2.1
                                                        have p1098_3 := h1098c.2.2.2
                                                        linarith only [h1033, hlam, p1098_0]
                                                      · have p1098_0 := h1098c.1
                                                        have p1098_1 := h1098c.2.1
                                                        have p1098_2 := h1098c.2.2.1
                                                        have p1098_3 := h1098c.2.2.2
                                                        linarith only [hlam, p1098_0]
                                                      · have p1098_0 := h1098c.1
                                                        have p1098_1 := h1098c.2.1
                                                        have p1098_2 := h1098c.2.2.1
                                                        have p1098_3 := h1098c.2.2.2
                                                        rcases p1098_3 (m.d 0 4) (by simp) with h1132 | h1132
                                                        · linarith only [h1132, h693, hlam]
                                                        · linarith only [h1023, h1132, hlam]
                                                      · have p1098_0 := h1098c.1
                                                        have p1098_1 := h1098c.2.1
                                                        have p1098_2 := h1098c.2.2.1
                                                        have p1098_3 := h1098c.2.2.2
                                                        linarith only [h1023, hlam, p1098_0]
                                                      · have p1098_0 := h1098c.1
                                                        have p1098_1 := h1098c.2.1
                                                        have p1098_2 := h1098c.2.2.1
                                                        have p1098_3 := h1098c.2.2.2
                                                        linarith only [h1032, hlam, p1098_0]
                                                      · have p1098_0 := h1098c.1
                                                        have p1098_1 := h1098c.2.1
                                                        have p1098_2 := h1098c.2.2.1
                                                        have p1098_3 := h1098c.2.2.2
                                                        linarith only [h1035, hlam, p1098_0]
                                                      · have p1098_0 := h1098c.1
                                                        have p1098_1 := h1098c.2.1
                                                        have p1098_2 := h1098c.2.2.1
                                                        have p1098_3 := h1098c.2.2.2
                                                        linarith only [h1036, hlam, p1098_0]
                                                      · have p1098_0 := h1098c.1
                                                        have p1098_1 := h1098c.2.1
                                                        have p1098_2 := h1098c.2.2.1
                                                        have p1098_3 := h1098c.2.2.2
                                                        linarith only [hlam, p1098_0]
                                                  · linarith only [h1095, hlam, p1064_0]
                                                · linarith only [h1094, h4, hlam]
                                          · have p1064_0 := h1064c.1
                                            have p1064_1 := h1064c.2.1
                                            have p1064_2 := h1064c.2.2.1
                                            have p1064_3 := h1064c.2.2.2
                                            rcases p1064_3 (m.d 0 2) (by simp) with h1142 | h1142
                                            · linarith only [h1142, h570, hlam]
                                            · linarith only [h0, h1142, hlam]
                                          · have p1064_0 := h1064c.1
                                            have p1064_1 := h1064c.2.1
                                            have p1064_2 := h1064c.2.2.1
                                            have p1064_3 := h1064c.2.2.2
                                            linarith only [h1033, hlam, p1064_0]
                                          · have p1064_0 := h1064c.1
                                            have p1064_1 := h1064c.2.1
                                            have p1064_2 := h1064c.2.2.1
                                            have p1064_3 := h1064c.2.2.2
                                            linarith only [hlam, p1064_0]
                                          · have p1064_0 := h1064c.1
                                            have p1064_1 := h1064c.2.1
                                            have p1064_2 := h1064c.2.2.1
                                            have p1064_3 := h1064c.2.2.2
                                            rcases p1064_3 (m.d 0 2) (by simp) with h1147 | h1147
                                            · linarith only [h1147, h570, hlam]
                                            · linarith only [h1147, h692, hlam]
                                          · have p1064_0 := h1064c.1
                                            have p1064_1 := h1064c.2.1
                                            have p1064_2 := h1064c.2.2.1
                                            have p1064_3 := h1064c.2.2.2
                                            linarith only [h692, hlam, p1064_0]
                                          · have p1064_0 := h1064c.1
                                            have p1064_1 := h1064c.2.1
                                            have p1064_2 := h1064c.2.2.1
                                            have p1064_3 := h1064c.2.2.2
                                            linarith only [h1028, hlam, p1064_0]
                                          · have p1064_0 := h1064c.1
                                            have p1064_1 := h1064c.2.1
                                            have p1064_2 := h1064c.2.2.1
                                            have p1064_3 := h1064c.2.2.2
                                            linarith only [h1034, hlam, p1064_0]
                                          · have p1064_0 := h1064c.1
                                            have p1064_1 := h1064c.2.1
                                            have p1064_2 := h1064c.2.2.1
                                            have p1064_3 := h1064c.2.2.2
                                            linarith only [h1035, hlam, p1064_1]
                                          · have p1064_0 := h1064c.1
                                            have p1064_1 := h1064c.2.1
                                            have p1064_2 := h1064c.2.2.1
                                            have p1064_3 := h1064c.2.2.2
                                            linarith only [hlam, p1064_0]
                                · linarith only [h1055, hlam, p1037_0]
                              · have p1037_0 := h1037c.1
                                have p1037_1 := h1037c.2.1
                                have p1037_2 := h1037c.2.2.1
                                have p1037_3 := h1037c.2.2.2
                                rcases p1037_3 (m.d 0 1) (by simp) with h1156 | h1156
                                · rcases p1037_3 (m.d 1 2) (by simp) with h1157 | h1157
                                  · linarith only [h0, h1157, hlam]
                                  · linarith only [h1028, h1157, hlam]
                                · linarith only [h1156, hlam, p1037_0]
                              · have p1037_0 := h1037c.1
                                have p1037_1 := h1037c.2.1
                                have p1037_2 := h1037c.2.2.1
                                have p1037_3 := h1037c.2.2.2
                                linarith only [h0, hlam, p1037_0]
                              · have p1037_0 := h1037c.1
                                have p1037_1 := h1037c.2.1
                                have p1037_2 := h1037c.2.2.1
                                have p1037_3 := h1037c.2.2.2
                                linarith only [hlam, p1037_0]
                              · have p1037_0 := h1037c.1
                                have p1037_1 := h1037c.2.1
                                have p1037_2 := h1037c.2.2.1
                                have p1037_3 := h1037c.2.2.2
                                linarith only [h1024, hlam, p1037_1]
                              · have p1037_0 := h1037c.1
                                have p1037_1 := h1037c.2.1
                                have p1037_2 := h1037c.2.2.1
                                have p1037_3 := h1037c.2.2.2
                                linarith only [h1026, hlam, p1037_1]
                              · have p1037_0 := h1037c.1
                                have p1037_1 := h1037c.2.1
                                have p1037_2 := h1037c.2.2.1
                                have p1037_3 := h1037c.2.2.2
                                linarith only [h0, h1033, h4, h693, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1037_1]
                              · have p1037_0 := h1037c.1
                                have p1037_1 := h1037c.2.1
                                have p1037_2 := h1037c.2.2.1
                                have p1037_3 := h1037c.2.2.2
                                linarith only [h1, hlam, p1037_0]
                              · have p1037_0 := h1037c.1
                                have p1037_1 := h1037c.2.1
                                have p1037_2 := h1037c.2.2.1
                                have p1037_3 := h1037c.2.2.2
                                linarith only [h1, h1033, h693, hc12, hc23, hlam, hphi, p1037_1]
                              · have p1037_0 := h1037c.1
                                have p1037_1 := h1037c.2.1
                                have p1037_2 := h1037c.2.2.1
                                have p1037_3 := h1037c.2.2.2
                                linarith only [hlam, p1037_0]
                              · have p1037_0 := h1037c.1
                                have p1037_1 := h1037c.2.1
                                have p1037_2 := h1037c.2.2.1
                                have p1037_3 := h1037c.2.2.2
                                linarith only [h1029, hlam, p1037_0]
                              · have p1037_0 := h1037c.1
                                have p1037_1 := h1037c.2.1
                                have p1037_2 := h1037c.2.2.1
                                have p1037_3 := h1037c.2.2.2
                                linarith only [h1, h1028, h1033, h1034, h1036, h693, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1037_1]
                              · have p1037_0 := h1037c.1
                                have p1037_1 := h1037c.2.1
                                have p1037_2 := h1037c.2.2.1
                                have p1037_3 := h1037c.2.2.2
                                linarith only [h2, hlam, p1037_0]
                              · have p1037_0 := h1037c.1
                                have p1037_1 := h1037c.2.1
                                have p1037_2 := h1037c.2.2.1
                                have p1037_3 := h1037c.2.2.2
                                linarith only [h1028, h1034, h1036, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1037_1]
                              · have p1037_0 := h1037c.1
                                have p1037_1 := h1037c.2.1
                                have p1037_2 := h1037c.2.2.1
                                have p1037_3 := h1037c.2.2.2
                                linarith only [h1024, h1028, h1033, h1034, h1036, h2, h693, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1037_1]
                              · have p1037_0 := h1037c.1
                                have p1037_1 := h1037c.2.1
                                have p1037_2 := h1037c.2.2.1
                                have p1037_3 := h1037c.2.2.2
                                linarith only [hlam, p1037_0]
                              · have p1037_0 := h1037c.1
                                have p1037_1 := h1037c.2.1
                                have p1037_2 := h1037c.2.2.1
                                have p1037_3 := h1037c.2.2.2
                                rcases p1037_3 (m.d 0 1) (by simp) with h1175 | h1175
                                · rcases p1037_3 (m.d 1 2) (by simp) with h1176 | h1176
                                  · linarith only [h1026, h1176, hlam]
                                  · linarith only [h1028, h1176, hlam]
                                · linarith only [h1175, h3, hlam]
                              · have p1037_0 := h1037c.1
                                have p1037_1 := h1037c.2.1
                                have p1037_2 := h1037c.2.2.1
                                have p1037_3 := h1037c.2.2.2
                                linarith only [h3, hlam, p1037_0]
                              · have p1037_0 := h1037c.1
                                have p1037_1 := h1037c.2.1
                                have p1037_2 := h1037c.2.2.1
                                have p1037_3 := h1037c.2.2.2
                                linarith only [h1028, hlam, p1037_0]
                              · have p1037_0 := h1037c.1
                                have p1037_1 := h1037c.2.1
                                have p1037_2 := h1037c.2.2.1
                                have p1037_3 := h1037c.2.2.2
                                linarith only [h1031, hlam, p1037_0]
                              · have p1037_0 := h1037c.1
                                have p1037_1 := h1037c.2.1
                                have p1037_2 := h1037c.2.2.1
                                have p1037_3 := h1037c.2.2.2
                                linarith only [h1032, hlam, p1037_0]
                              · have p1037_0 := h1037c.1
                                have p1037_1 := h1037c.2.1
                                have p1037_2 := h1037c.2.2.1
                                have p1037_3 := h1037c.2.2.2
                                linarith only [hlam, p1037_0]
                            · linarith only [h1036, h693, hc03, hlam, hphi, ht34, ht45, u5elo4]
                          · linarith only [h1032, h1035, h3, hc24, hlam, hphi, ht45, u5elo0]
                        · linarith only [h1033, h1034, h693, hc03, hc35, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1188 | h1188
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1189 | h1189
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1190 | h1190
                            · rcases h1bigk with h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [hlam, p1191_0]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                rcases p1191_3 (m.d 0 1) (by simp) with h1193 | h1193
                                · rcases p1191_3 (m.d 1 2) (by simp) with h1194 | h1194
                                  · linarith only [h1194, hlam, p1191_0]
                                  · rcases p1191_3 (m.d 1 3) (by simp) with h1196 | h1196
                                    · linarith only [h1, h1196, hlam]
                                    · linarith only [h1024, h1196, hlam]
                                · linarith only [h1193, hlam, p1191_0]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                rcases p1191_3 (m.d 0 1) (by simp) with h1200 | h1200
                                · rcases p1191_3 (m.d 1 2) (by simp) with h1201 | h1201
                                  · linarith only [h0, h1201, hlam]
                                  · rcases p1191_3 (m.d 1 3) (by simp) with h1203 | h1203
                                    · linarith only [h1203, hlam, p1191_0]
                                    · rcases p1191_3 (m.d 1 4) (by simp) with h1205 | h1205
                                      · linarith only [h1205, h2, hlam]
                                      · linarith only [h1029, h1205, hlam]
                                · linarith only [h1200, hlam, p1191_0]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                rcases p1191_3 (m.d 0 1) (by simp) with h1209 | h1209
                                · rcases p1191_3 (m.d 1 2) (by simp) with h1210 | h1210
                                  · linarith only [h0, h1210, hlam]
                                  · rcases p1191_3 (m.d 1 3) (by simp) with h1212 | h1212
                                    · linarith only [h1, h1212, hlam]
                                    · rcases p1191_3 (m.d 1 4) (by simp) with h1214 | h1214
                                      · linarith only [h1214, hlam, p1191_0]
                                      · rcases p1191_3 (m.d 1 5) (by simp) with h1216 | h1216
                                        · linarith only [h1216, h3, hlam]
                                        · rcases h2bigk with h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c
                                          · have p1218_0 := h1218c.1
                                            have p1218_1 := h1218c.2.1
                                            have p1218_2 := h1218c.2.2.1
                                            have p1218_3 := h1218c.2.2.2
                                            linarith only [hlam, p1218_0]
                                          · have p1218_0 := h1218c.1
                                            have p1218_1 := h1218c.2.1
                                            have p1218_2 := h1218c.2.2.1
                                            have p1218_3 := h1218c.2.2.2
                                            linarith only [h1028, h1033, h1188, h1190, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1218_1]
                                          · have p1218_0 := h1218c.1
                                            have p1218_1 := h1218c.2.1
                                            have p1218_2 := h1218c.2.2.1
                                            have p1218_3 := h1218c.2.2.2
                                            linarith only [h4, hlam, p1218_0]
                                          · have p1218_0 := h1218c.1
                                            have p1218_1 := h1218c.2.1
                                            have p1218_2 := h1218c.2.2.1
                                            have p1218_3 := h1218c.2.2.2
                                            linarith only [h570, hlam, p1218_0]
                                          · have p1218_0 := h1218c.1
                                            have p1218_1 := h1218c.2.1
                                            have p1218_2 := h1218c.2.2.1
                                            have p1218_3 := h1218c.2.2.2
                                            linarith only [h1033, h1188, h1190, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1218_1]
                                          · have p1218_0 := h1218c.1
                                            have p1218_1 := h1218c.2.1
                                            have p1218_2 := h1218c.2.2.1
                                            have p1218_3 := h1218c.2.2.2
                                            linarith only [h0, hlam, p1218_1]
                                          · have p1218_0 := h1218c.1
                                            have p1218_1 := h1218c.2.1
                                            have p1218_2 := h1218c.2.2.1
                                            have p1218_3 := h1218c.2.2.2
                                            linarith only [hlam, p1218_0]
                                          · have p1218_0 := h1218c.1
                                            have p1218_1 := h1218c.2.1
                                            have p1218_2 := h1218c.2.2.1
                                            have p1218_3 := h1218c.2.2.2
                                            linarith only [h1024, hlam, p1218_0]
                                          · have p1218_0 := h1218c.1
                                            have p1218_1 := h1218c.2.1
                                            have p1218_2 := h1218c.2.2.1
                                            have p1218_3 := h1218c.2.2.2
                                            linarith only [h1026, hlam, p1218_0]
                                          · have p1218_0 := h1218c.1
                                            have p1218_1 := h1218c.2.1
                                            have p1218_2 := h1218c.2.2.1
                                            have p1218_3 := h1218c.2.2.2
                                            linarith only [h0, h1033, h1188, h1190, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1218_1]
                                          · have p1218_0 := h1218c.1
                                            have p1218_1 := h1218c.2.1
                                            have p1218_2 := h1218c.2.2.1
                                            have p1218_3 := h1218c.2.2.2
                                            linarith only [h1033, hc02, hc34, hlam, hphi, ht23, p1218_1]
                                          · have p1218_0 := h1218c.1
                                            have p1218_1 := h1218c.2.1
                                            have p1218_2 := h1218c.2.2.1
                                            have p1218_3 := h1218c.2.2.2
                                            linarith only [h1033, hc12, hc34, hlam, hphi, ht23, p1218_1]
                                          · have p1218_0 := h1218c.1
                                            have p1218_1 := h1218c.2.1
                                            have p1218_2 := h1218c.2.2.1
                                            have p1218_3 := h1218c.2.2.2
                                            linarith only [hlam, p1218_0]
                                          · have p1218_0 := h1218c.1
                                            have p1218_1 := h1218c.2.1
                                            have p1218_2 := h1218c.2.2.1
                                            have p1218_3 := h1218c.2.2.2
                                            linarith only [h1033, hlam, p1218_1]
                                          · have p1218_0 := h1218c.1
                                            have p1218_1 := h1218c.2.1
                                            have p1218_2 := h1218c.2.2.1
                                            have p1218_3 := h1218c.2.2.2
                                            rcases p1218_3 (m.d 0 2) (by simp) with h1233 | h1233
                                            · linarith only [h1233, h4, hlam]
                                            · linarith only [h1233, h692, hlam]
                                          · have p1218_0 := h1218c.1
                                            have p1218_1 := h1218c.2.1
                                            have p1218_2 := h1218c.2.2.1
                                            have p1218_3 := h1218c.2.2.2
                                            rcases p1218_3 (m.d 0 2) (by simp) with h1236 | h1236
                                            · linarith only [h1236, hlam, p1218_0]
                                            · rcases p1218_3 (m.d 1 2) (by simp) with h1238 | h1238
                                              · linarith only [h1026, h1238, hlam]
                                              · rcases p1218_3 (m.d 2 3) (by simp) with h1240 | h1240
                                                · linarith only [h1033, h1240, hlam]
                                                · linarith only [h1240, h4, hlam]
                                          · have p1218_0 := h1218c.1
                                            have p1218_1 := h1218c.2.1
                                            have p1218_2 := h1218c.2.2.1
                                            have p1218_3 := h1218c.2.2.2
                                            rcases p1218_3 (m.d 0 2) (by simp) with h1243 | h1243
                                            · linarith only [h1243, h570, hlam]
                                            · linarith only [h0, h1243, hlam]
                                          · have p1218_0 := h1218c.1
                                            have p1218_1 := h1218c.2.1
                                            have p1218_2 := h1218c.2.2.1
                                            have p1218_3 := h1218c.2.2.2
                                            linarith only [h1033, h4, hc02, hc34, hlam, hphi, ht23, p1218_1]
                                          · have p1218_0 := h1218c.1
                                            have p1218_1 := h1218c.2.1
                                            have p1218_2 := h1218c.2.2.1
                                            have p1218_3 := h1218c.2.2.2
                                            linarith only [hlam, p1218_0]
                                          · have p1218_0 := h1218c.1
                                            have p1218_1 := h1218c.2.1
                                            have p1218_2 := h1218c.2.2.1
                                            have p1218_3 := h1218c.2.2.2
                                            rcases p1218_3 (m.d 0 2) (by simp) with h1248 | h1248
                                            · linarith only [h1248, h570, hlam]
                                            · linarith only [h1248, h692, hlam]
                                          · have p1218_0 := h1218c.1
                                            have p1218_1 := h1218c.2.1
                                            have p1218_2 := h1218c.2.2.1
                                            have p1218_3 := h1218c.2.2.2
                                            linarith only [h692, hlam, p1218_0]
                                          · have p1218_0 := h1218c.1
                                            have p1218_1 := h1218c.2.1
                                            have p1218_2 := h1218c.2.2.1
                                            have p1218_3 := h1218c.2.2.2
                                            linarith only [h1028, hlam, p1218_0]
                                          · have p1218_0 := h1218c.1
                                            have p1218_1 := h1218c.2.1
                                            have p1218_2 := h1218c.2.2.1
                                            have p1218_3 := h1218c.2.2.2
                                            linarith only [h1188, hlam, p1218_0]
                                          · have p1218_0 := h1218c.1
                                            have p1218_1 := h1218c.2.1
                                            have p1218_2 := h1218c.2.2.1
                                            have p1218_3 := h1218c.2.2.2
                                            linarith only [h1189, hlam, p1218_1]
                                          · have p1218_0 := h1218c.1
                                            have p1218_1 := h1218c.2.1
                                            have p1218_2 := h1218c.2.2.1
                                            have p1218_3 := h1218c.2.2.2
                                            linarith only [hlam, p1218_0]
                                · linarith only [h1209, hlam, p1191_0]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                rcases p1191_3 (m.d 0 1) (by simp) with h1257 | h1257
                                · rcases p1191_3 (m.d 1 2) (by simp) with h1258 | h1258
                                  · linarith only [h0, h1258, hlam]
                                  · linarith only [h1028, h1258, hlam]
                                · linarith only [h1257, hlam, p1191_0]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [h0, hlam, p1191_0]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [hlam, p1191_0]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [h1024, hlam, p1191_1]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [h1026, hlam, p1191_1]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [h0, h1033, h4, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1191_1]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [h1, hlam, p1191_0]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [h1, h693, hc12, hc34, hlam, hphi, ht23, p1191_1]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [hlam, p1191_0]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [h1029, hlam, p1191_0]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                rcases p1191_3 (m.d 0 1) (by simp) with h1271 | h1271
                                · rcases p1191_3 (m.d 1 2) (by simp) with h1272 | h1272
                                  · linarith only [h1024, h1272, hlam]
                                  · linarith only [h1028, h1272, hlam]
                                · linarith only [h1271, h3, hlam]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [h2, hlam, p1191_0]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [h1028, h1188, h1190, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1191_1]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [h1024, h1028, h1188, h1190, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1191_1]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [hlam, p1191_0]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                rcases p1191_3 (m.d 0 1) (by simp) with h1280 | h1280
                                · rcases p1191_3 (m.d 1 2) (by simp) with h1281 | h1281
                                  · linarith only [h1026, h1281, hlam]
                                  · linarith only [h1028, h1281, hlam]
                                · linarith only [h1280, h3, hlam]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [h3, hlam, p1191_0]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [h1028, hlam, p1191_0]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [h1031, hlam, p1191_0]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [h1032, hlam, p1191_0]
                              · have p1191_0 := h1191c.1
                                have p1191_1 := h1191c.2.1
                                have p1191_2 := h1191c.2.2.1
                                have p1191_3 := h1191c.2.2.2
                                linarith only [hlam, p1191_0]
                            · linarith only [h1033, h1190, h4, hc02, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h1032, h1189, h3, h570, hc04, hlam, hphi, ht45, u5elo0]
                        · linarith only [h0, h1028, h1188, h4, hc25, hlam, hphi, u5elo3]
                    · linarith only [h1024, h1028, h1029, h1032, hc25, hlam, hphi, u5elo4]
                  · linarith only [h1024, h1028, h1031, hc25, hlam, hphi, u5elo3]
              · linarith only [h1028, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h1023, h4, h693, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
    · linarith only [h0, h692, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]

set_option maxHeartbeats 6266000 in
set_option maxHeartbeats 6266000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4

set_option maxHeartbeats 6266000 in
set_option maxHeartbeats 6266000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [h3, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

set_option maxHeartbeats 6266000 in
set_option maxHeartbeats 6266000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 h0 h1 h2 h3
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 h0 h1 h2 h3

end R2N4
