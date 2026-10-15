import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_33S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8858000 in
set_option maxHeartbeats 8858000 in
theorem r1l7_22_13_15_M_LI_L_I_L_I_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h602 | h602
  · rcases m.htr 0 4 5 (by decide) (by decide) with h603 | h603
    · rcases m.htr 1 2 3 (by decide) (by decide) with h604 | h604
      · rcases m.htr 1 2 4 (by decide) (by decide) with h605 | h605
        · rcases m.htr 1 2 5 (by decide) (by decide) with h606 | h606
          · rcases m.htr 1 3 4 (by decide) (by decide) with h607 | h607
            · linarith only [h1, h6, h602, h607, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h609 | h609
              · rcases m.htr 1 4 5 (by decide) (by decide) with h610 | h610
                · rcases m.htr 2 3 4 (by decide) (by decide) with h611 | h611
                  · linarith only [h1, h6, h604, h609, h611, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h613 | h613
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h614 | h614
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h615 | h615
                        · rcases h2bigk with h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c
                          · have p616_0 := h616c.1
                            have p616_1 := h616c.2.1
                            have p616_2 := h616c.2.2.1
                            have p616_3 := h616c.2.2.2
                            linarith only [hlam, p616_0]
                          · have p616_0 := h616c.1
                            have p616_1 := h616c.2.1
                            have p616_2 := h616c.2.2.1
                            have p616_3 := h616c.2.2.2
                            linarith only [hc12, hlam, hphi, p616_1, u2elo0]
                          · have p616_0 := h616c.1
                            have p616_1 := h616c.2.1
                            have p616_2 := h616c.2.2.1
                            have p616_3 := h616c.2.2.2
                            linarith only [h613, h615, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p616_1, u2elo0]
                          · have p616_0 := h616c.1
                            have p616_1 := h616c.2.1
                            have p616_2 := h616c.2.2.1
                            have p616_3 := h616c.2.2.2
                            linarith only [h611, h613, h615, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p616_1, u2elo0]
                          · have p616_0 := h616c.1
                            have p616_1 := h616c.2.1
                            have p616_2 := h616c.2.2.1
                            have p616_3 := h616c.2.2.2
                            rcases p616_3 (m.d 0 2) (by simp) with h621 | h621
                            · rcases p616_3 (m.d 1 2) (by simp) with h622 | h622
                              · linarith only [h0, h622, hlam]
                              · linarith only [h606, h622, hlam]
                            · linarith only [h621, hlam, p616_0]
                          · have p616_0 := h616c.1
                            have p616_1 := h616c.2.1
                            have p616_2 := h616c.2.2.1
                            have p616_3 := h616c.2.2.2
                            linarith only [h0, hlam, p616_1]
                          · have p616_0 := h616c.1
                            have p616_1 := h616c.2.1
                            have p616_2 := h616c.2.2.1
                            have p616_3 := h616c.2.2.2
                            linarith only [hlam, p616_0]
                          · have p616_0 := h616c.1
                            have p616_1 := h616c.2.1
                            have p616_2 := h616c.2.2.1
                            have p616_3 := h616c.2.2.2
                            linarith only [h613, h615, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p616_1, u2elo1]
                          · have p616_0 := h616c.1
                            have p616_1 := h616c.2.1
                            have p616_2 := h616c.2.2.1
                            have p616_3 := h616c.2.2.2
                            linarith only [h0, h611, h613, h615, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p616_1, u2elo0]
                          · have p616_0 := h616c.1
                            have p616_1 := h616c.2.1
                            have p616_2 := h616c.2.2.1
                            have p616_3 := h616c.2.2.2
                            rcases p616_3 (m.d 0 2) (by simp) with h630 | h630
                            · rcases p616_3 (m.d 1 2) (by simp) with h631 | h631
                              · rcases p616_3 (m.d 2 3) (by simp) with h632 | h632
                                · linarith only [h604, h632, hlam]
                                · linarith only [h613, h632, hlam]
                              · linarith only [h631, hlam, p616_0]
                            · linarith only [h5, h630, hlam]
                          · have p616_0 := h616c.1
                            have p616_1 := h616c.2.1
                            have p616_2 := h616c.2.2.1
                            have p616_3 := h616c.2.2.2
                            linarith only [h3, hlam, p616_0]
                          · have p616_0 := h616c.1
                            have p616_1 := h616c.2.1
                            have p616_2 := h616c.2.2.1
                            have p616_3 := h616c.2.2.2
                            linarith only [h604, hlam, p616_0]
                          · have p616_0 := h616c.1
                            have p616_1 := h616c.2.1
                            have p616_2 := h616c.2.2.1
                            have p616_3 := h616c.2.2.2
                            linarith only [hlam, p616_0]
                          · have p616_0 := h616c.1
                            have p616_1 := h616c.2.1
                            have p616_2 := h616c.2.2.1
                            have p616_3 := h616c.2.2.2
                            linarith only [h611, hlam, p616_1]
                          · have p616_0 := h616c.1
                            have p616_1 := h616c.2.1
                            have p616_2 := h616c.2.2.1
                            have p616_3 := h616c.2.2.2
                            linarith only [h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p616_1, u2elo0]
                          · have p616_0 := h616c.1
                            have p616_1 := h616c.2.1
                            have p616_2 := h616c.2.2.1
                            have p616_3 := h616c.2.2.2
                            linarith only [h4, hlam, p616_0]
                          · have p616_0 := h616c.1
                            have p616_1 := h616c.2.1
                            have p616_2 := h616c.2.2.1
                            have p616_3 := h616c.2.2.2
                            linarith only [h605, hlam, p616_0]
                          · have p616_0 := h616c.1
                            have p616_1 := h616c.2.1
                            have p616_2 := h616c.2.2.1
                            have p616_3 := h616c.2.2.2
                            linarith only [h613, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p616_1, u2elo3]
                          · have p616_0 := h616c.1
                            have p616_1 := h616c.2.1
                            have p616_2 := h616c.2.2.1
                            have p616_3 := h616c.2.2.2
                            linarith only [hlam, p616_0]
                          · have p616_0 := h616c.1
                            have p616_1 := h616c.2.1
                            have p616_2 := h616c.2.2.1
                            have p616_3 := h616c.2.2.2
                            linarith only [h0, h605, h613, h615, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p616_1, u2elo0]
                          · have p616_0 := h616c.1
                            have p616_1 := h616c.2.1
                            have p616_2 := h616c.2.2.1
                            have p616_3 := h616c.2.2.2
                            linarith only [h5, hlam, p616_0]
                          · have p616_0 := h616c.1
                            have p616_1 := h616c.2.1
                            have p616_2 := h616c.2.2.1
                            have p616_3 := h616c.2.2.2
                            linarith only [h606, hlam, p616_0]
                          · have p616_0 := h616c.1
                            have p616_1 := h616c.2.1
                            have p616_2 := h616c.2.2.1
                            have p616_3 := h616c.2.2.2
                            linarith only [h613, hlam, p616_0]
                          · have p616_0 := h616c.1
                            have p616_1 := h616c.2.1
                            have p616_2 := h616c.2.2.1
                            have p616_3 := h616c.2.2.2
                            linarith only [h614, hlam, p616_1]
                          · have p616_0 := h616c.1
                            have p616_1 := h616c.2.1
                            have p616_2 := h616c.2.2.1
                            have p616_3 := h616c.2.2.2
                            linarith only [hlam, p616_0]
                        · linarith only [h1, h6, h603, h604, h613, h615, hc04, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h4, h603, h611, h613, h614, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                    · linarith only [h6, h602, h613, hc23, hc34, hlam, hphi]
                · linarith only [h4, h603, h607, h609, h610, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
              · linarith only [h6, h602, h609, hc13, hc34, hlam, hphi]
          · linarith only [h5, h606, hc12, hlam, hphi, u2elo0]
        · linarith only [h4, h604, h605, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
      · linarith only [h3, h604, hc12, hlam, hphi, u2elo0]
    · linarith only [h6, h602, h603, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h661 | h661
    · rcases m.htr 1 2 3 (by decide) (by decide) with h662 | h662
      · rcases m.htr 1 2 4 (by decide) (by decide) with h663 | h663
        · rcases m.htr 1 2 5 (by decide) (by decide) with h664 | h664
          · rcases m.htr 1 3 4 (by decide) (by decide) with h665 | h665
            · linarith only [h1, h6, h665, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h667 | h667
              · linarith only [h1, h602, h667, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h669 | h669
                · rcases m.htr 2 3 4 (by decide) (by decide) with h670 | h670
                  · linarith only [h3, h6, h670, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h672 | h672
                    · linarith only [h1, h602, h662, h672, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h674 | h674
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h675 | h675
                        · rcases h2bigk with h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [hlam, p676_0]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [hc12, hlam, hphi, p676_1, u2elo0]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            rcases p676_3 (m.d 0 2) (by simp) with h679 | h679
                            · rcases p676_3 (m.d 1 2) (by simp) with h680 | h680
                              · linarith only [h0, h680, hlam]
                              · linarith only [h662, h680, hlam]
                            · linarith only [h679, hlam, p676_0]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [h674, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p676_1, u2elo0]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            rcases p676_3 (m.d 0 2) (by simp) with h685 | h685
                            · rcases p676_3 (m.d 1 2) (by simp) with h686 | h686
                              · linarith only [h0, h686, hlam]
                              · linarith only [h664, h686, hlam]
                            · linarith only [h685, hlam, p676_0]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [h0, hlam, p676_1]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [hlam, p676_0]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            rcases p676_3 (m.d 0 2) (by simp) with h692 | h692
                            · rcases p676_3 (m.d 1 2) (by simp) with h693 | h693
                              · rcases p676_3 (m.d 2 3) (by simp) with h694 | h694
                                · linarith only [h694, hlam, p676_0]
                                · rcases p676_3 (m.d 2 4) (by simp) with h696 | h696
                                  · linarith only [h663, h696, hlam]
                                  · linarith only [h670, h696, hlam]
                              · linarith only [h693, hlam, p676_0]
                            · linarith only [h3, h692, hlam]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [h674, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p676_1, u2elo1]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            rcases p676_3 (m.d 0 2) (by simp) with h702 | h702
                            · rcases p676_3 (m.d 1 2) (by simp) with h703 | h703
                              · rcases p676_3 (m.d 2 3) (by simp) with h704 | h704
                                · linarith only [h662, h704, hlam]
                                · rcases p676_3 (m.d 2 4) (by simp) with h706 | h706
                                  · linarith only [h663, h706, hlam]
                                  · linarith only [h674, h706, hlam]
                              · linarith only [h703, hlam, p676_0]
                            · linarith only [h5, h702, hlam]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [h3, hlam, p676_0]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [h662, hlam, p676_0]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [hlam, p676_0]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [h670, hlam, p676_1]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [h672, hlam, p676_1]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [h4, hlam, p676_0]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [h663, hlam, p676_0]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p676_1, u2elo0]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [hlam, p676_0]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [h0, h663, h672, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p676_1, u2elo0]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [h5, hlam, p676_0]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [h664, hlam, p676_0]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p676_1, u2elo0]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [h674, hlam, p676_1]
                          · have p676_0 := h676c.1
                            have p676_1 := h676c.2.1
                            have p676_2 := h676c.2.2.1
                            have p676_3 := h676c.2.2.2
                            linarith only [hlam, p676_0]
                        · linarith only [h6, h661, h675, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h727 | h727
                        · rcases h2bigk with h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c
                          · have p728_0 := h728c.1
                            have p728_1 := h728c.2.1
                            have p728_2 := h728c.2.2.1
                            have p728_3 := h728c.2.2.2
                            linarith only [hlam, p728_0]
                          · have p728_0 := h728c.1
                            have p728_1 := h728c.2.1
                            have p728_2 := h728c.2.2.1
                            have p728_3 := h728c.2.2.2
                            linarith only [hc12, hlam, hphi, p728_1, u2elo0]
                          · have p728_0 := h728c.1
                            have p728_1 := h728c.2.1
                            have p728_2 := h728c.2.2.1
                            have p728_3 := h728c.2.2.2
                            rcases p728_3 (m.d 0 2) (by simp) with h731 | h731
                            · rcases p728_3 (m.d 1 2) (by simp) with h732 | h732
                              · linarith only [h0, h732, hlam]
                              · linarith only [h662, h732, hlam]
                            · linarith only [h731, hlam, p728_0]
                          · have p728_0 := h728c.1
                            have p728_1 := h728c.2.1
                            have p728_2 := h728c.2.2.1
                            have p728_3 := h728c.2.2.2
                            rcases p728_3 (m.d 0 2) (by simp) with h736 | h736
                            · rcases p728_3 (m.d 1 2) (by simp) with h737 | h737
                              · linarith only [h0, h737, hlam]
                              · linarith only [h663, h737, hlam]
                            · linarith only [h736, hlam, p728_0]
                          · have p728_0 := h728c.1
                            have p728_1 := h728c.2.1
                            have p728_2 := h728c.2.2.1
                            have p728_3 := h728c.2.2.2
                            rcases p728_3 (m.d 0 2) (by simp) with h741 | h741
                            · rcases p728_3 (m.d 1 2) (by simp) with h742 | h742
                              · linarith only [h0, h742, hlam]
                              · linarith only [h664, h742, hlam]
                            · linarith only [h741, hlam, p728_0]
                          · have p728_0 := h728c.1
                            have p728_1 := h728c.2.1
                            have p728_2 := h728c.2.2.1
                            have p728_3 := h728c.2.2.2
                            linarith only [h0, hlam, p728_1]
                          · have p728_0 := h728c.1
                            have p728_1 := h728c.2.1
                            have p728_2 := h728c.2.2.1
                            have p728_3 := h728c.2.2.2
                            linarith only [hlam, p728_0]
                          · have p728_0 := h728c.1
                            have p728_1 := h728c.2.1
                            have p728_2 := h728c.2.2.1
                            have p728_3 := h728c.2.2.2
                            rcases p728_3 (m.d 0 2) (by simp) with h748 | h748
                            · rcases p728_3 (m.d 1 2) (by simp) with h749 | h749
                              · rcases p728_3 (m.d 2 3) (by simp) with h750 | h750
                                · linarith only [h750, hlam, p728_0]
                                · rcases p728_3 (m.d 2 4) (by simp) with h752 | h752
                                  · linarith only [h663, h752, hlam]
                                  · linarith only [h670, h752, hlam]
                              · linarith only [h749, hlam, p728_0]
                            · linarith only [h3, h748, hlam]
                          · have p728_0 := h728c.1
                            have p728_1 := h728c.2.1
                            have p728_2 := h728c.2.2.1
                            have p728_3 := h728c.2.2.2
                            rcases p728_3 (m.d 0 2) (by simp) with h757 | h757
                            · rcases p728_3 (m.d 1 2) (by simp) with h758 | h758
                              · rcases p728_3 (m.d 2 3) (by simp) with h759 | h759
                                · linarith only [h662, h759, hlam]
                                · rcases p728_3 (m.d 2 4) (by simp) with h761 | h761
                                  · linarith only [h761, hlam, p728_0]
                                  · rcases p728_3 (m.d 2 5) (by simp) with h763 | h763
                                    · linarith only [h664, h763, hlam]
                                    · linarith only [h674, h763, hlam]
                              · linarith only [h758, hlam, p728_0]
                            · linarith only [h4, h757, hlam]
                          · have p728_0 := h728c.1
                            have p728_1 := h728c.2.1
                            have p728_2 := h728c.2.2.1
                            have p728_3 := h728c.2.2.2
                            rcases p728_3 (m.d 0 2) (by simp) with h768 | h768
                            · rcases p728_3 (m.d 1 2) (by simp) with h769 | h769
                              · rcases p728_3 (m.d 2 3) (by simp) with h770 | h770
                                · linarith only [h662, h770, hlam]
                                · rcases p728_3 (m.d 2 4) (by simp) with h772 | h772
                                  · linarith only [h663, h772, hlam]
                                  · rcases p728_3 (m.d 2 5) (by simp) with h774 | h774
                                    · linarith only [h774, hlam, p728_0]
                                    · rcases h3bigk with h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c
                                      · have p776_0 := h776c.1
                                        have p776_1 := h776c.2.1
                                        have p776_2 := h776c.2.2.1
                                        have p776_3 := h776c.2.2.2
                                        linarith only [hlam, p776_0]
                                      · have p776_0 := h776c.1
                                        have p776_1 := h776c.2.1
                                        have p776_2 := h776c.2.2.1
                                        have p776_3 := h776c.2.2.2
                                        linarith only [h6, h662, hc23, hc34, hlam, hphi, p776_1]
                                      · have p776_0 := h776c.1
                                        have p776_1 := h776c.2.1
                                        have p776_2 := h776c.2.2.1
                                        have p776_3 := h776c.2.2.2
                                        linarith only [h6, hc23, hc34, hlam, hphi, p776_1]
                                      · have p776_0 := h776c.1
                                        have p776_1 := h776c.2.1
                                        have p776_2 := h776c.2.2.1
                                        have p776_3 := h776c.2.2.2
                                        linarith only [h6, hlam, p776_0]
                                      · have p776_0 := h776c.1
                                        have p776_1 := h776c.2.1
                                        have p776_2 := h776c.2.2.1
                                        have p776_3 := h776c.2.2.2
                                        linarith only [h602, hlam, p776_0]
                                      · have p776_0 := h776c.1
                                        have p776_1 := h776c.2.1
                                        have p776_2 := h776c.2.2.1
                                        have p776_3 := h776c.2.2.2
                                        linarith only [h1, hlam, p776_0]
                                      · have p776_0 := h776c.1
                                        have p776_1 := h776c.2.1
                                        have p776_2 := h776c.2.2.1
                                        have p776_3 := h776c.2.2.2
                                        linarith only [hlam, p776_0]
                                      · have p776_0 := h776c.1
                                        have p776_1 := h776c.2.1
                                        have p776_2 := h776c.2.2.1
                                        have p776_3 := h776c.2.2.2
                                        linarith only [h1, h6, hc23, hc34, hlam, hphi, p776_1]
                                      · have p776_0 := h776c.1
                                        have p776_1 := h776c.2.1
                                        have p776_2 := h776c.2.2.1
                                        have p776_3 := h776c.2.2.2
                                        linarith only [h665, hlam, p776_0]
                                      · have p776_0 := h776c.1
                                        have p776_1 := h776c.2.1
                                        have p776_2 := h776c.2.2.1
                                        have p776_3 := h776c.2.2.2
                                        linarith only [h667, hlam, p776_0]
                                      · have p776_0 := h776c.1
                                        have p776_1 := h776c.2.1
                                        have p776_2 := h776c.2.2.1
                                        have p776_3 := h776c.2.2.2
                                        linarith only [h3, hlam, p776_1]
                                      · have p776_0 := h776c.1
                                        have p776_1 := h776c.2.1
                                        have p776_2 := h776c.2.2.1
                                        have p776_3 := h776c.2.2.2
                                        linarith only [h662, hlam, p776_1]
                                      · have p776_0 := h776c.1
                                        have p776_1 := h776c.2.1
                                        have p776_2 := h776c.2.2.1
                                        have p776_3 := h776c.2.2.2
                                        linarith only [hlam, p776_0]
                                      · have p776_0 := h776c.1
                                        have p776_1 := h776c.2.1
                                        have p776_2 := h776c.2.2.1
                                        have p776_3 := h776c.2.2.2
                                        linarith only [h670, hlam, p776_0]
                                      · have p776_0 := h776c.1
                                        have p776_1 := h776c.2.1
                                        have p776_2 := h776c.2.2.1
                                        have p776_3 := h776c.2.2.2
                                        linarith only [h672, hlam, p776_0]
                                      · have p776_0 := h776c.1
                                        have p776_1 := h776c.2.1
                                        have p776_2 := h776c.2.2.1
                                        have p776_3 := h776c.2.2.2
                                        rcases p776_3 (m.d 0 3) (by simp) with h792 | h792
                                        · linarith only [h792, hlam, p776_0]
                                        · rcases p776_3 (m.d 1 3) (by simp) with h794 | h794
                                          · linarith only [h665, h794, hlam]
                                          · rcases p776_3 (m.d 2 3) (by simp) with h796 | h796
                                            · linarith only [h670, h796, hlam]
                                            · rcases p776_3 (m.d 3 4) (by simp) with h798 | h798
                                              · rcases p776_3 (m.d 3 5) (by simp) with h799 | h799
                                                · linarith only [h727, h799, hlam]
                                                · linarith only [h602, h799, hlam]
                                              · linarith only [h798, hlam, p776_0]
                                      · have p776_0 := h776c.1
                                        have p776_1 := h776c.2.1
                                        have p776_2 := h776c.2.2.1
                                        have p776_3 := h776c.2.2.2
                                        rcases p776_3 (m.d 0 3) (by simp) with h803 | h803
                                        · linarith only [h6, h803, hlam]
                                        · linarith only [h1, h803, hlam]
                                      · have p776_0 := h776c.1
                                        have p776_1 := h776c.2.1
                                        have p776_2 := h776c.2.2.1
                                        have p776_3 := h776c.2.2.2
                                        rcases p776_3 (m.d 0 3) (by simp) with h806 | h806
                                        · linarith only [h6, h806, hlam]
                                        · linarith only [h3, h806, hlam]
                                      · have p776_0 := h776c.1
                                        have p776_1 := h776c.2.1
                                        have p776_2 := h776c.2.2.1
                                        have p776_3 := h776c.2.2.2
                                        linarith only [hlam, p776_0]
                                      · have p776_0 := h776c.1
                                        have p776_1 := h776c.2.1
                                        have p776_2 := h776c.2.2.1
                                        have p776_3 := h776c.2.2.2
                                        linarith only [h602, hc03, hc34, hlam, hphi, p776_1]
                                      · have p776_0 := h776c.1
                                        have p776_1 := h776c.2.1
                                        have p776_2 := h776c.2.2.1
                                        have p776_3 := h776c.2.2.2
                                        rcases p776_3 (m.d 0 3) (by simp) with h811 | h811
                                        · linarith only [h811, hlam, p776_0]
                                        · rcases p776_3 (m.d 1 3) (by simp) with h813 | h813
                                          · linarith only [h667, h813, hlam]
                                          · rcases p776_3 (m.d 2 3) (by simp) with h815 | h815
                                            · linarith only [h672, h815, hlam]
                                            · rcases p776_3 (m.d 3 4) (by simp) with h817 | h817
                                              · rcases p776_3 (m.d 3 5) (by simp) with h818 | h818
                                                · rcases h5bigk with h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [hlam, p819_0]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [h5, h669, h670, h674, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p819_1, u2elo0]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    rcases p819_3 (m.d 0 5) (by simp) with h822 | h822
                                                    · rcases p819_3 (m.d 1 5) (by simp) with h823 | h823
                                                      · linarith only [h2, h823, hlam]
                                                      · linarith only [h664, h823, hlam]
                                                    · linarith only [h5, h822, hlam]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [h602, hlam, p819_0]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [h4, h661, h670, h674, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p819_1, u2elo0]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [h2, hlam, p819_0]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [hlam, p819_0]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    rcases p819_3 (m.d 0 5) (by simp) with h831 | h831
                                                    · rcases p819_3 (m.d 1 5) (by simp) with h832 | h832
                                                      · rcases p819_3 (m.d 2 5) (by simp) with h833 | h833
                                                        · linarith only [h664, h833, hlam]
                                                        · rcases p819_3 (m.d 3 5) (by simp) with h835 | h835
                                                          · rcases p819_3 (m.d 4 5) (by simp) with h836 | h836
                                                            · linarith only [h669, h836, hlam]
                                                            · linarith only [h674, h836, hlam]
                                                          · linarith only [h672, h835, hlam]
                                                      · linarith only [h664, h832, hlam]
                                                    · linarith only [h5, h831, hlam]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [h667, hlam, p819_0]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [h663, h669, h670, h674, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p819_1, u2elo1]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [h5, hlam, p819_1]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [h664, hlam, p819_1]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [hlam, p819_0]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [h672, hlam, p819_1]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [h674, hlam, p819_0]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [h661, h670, h674, hc23, hc35, hlam, hphi, p819_1]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [h669, h670, h674, hc23, hc35, hlam, hphi, p819_1]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    rcases p819_3 (m.d 0 5) (by simp) with h851 | h851
                                                    · linarith only [h602, h851, hlam]
                                                    · linarith only [h5, h851, hlam]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [hlam, p819_0]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [h670, h674, h727, hc23, hc34, hlam, hphi, p819_1]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [h661, hlam, p819_1]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [h669, hlam, p819_1]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [h4, h661, h670, h674, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p819_1, u2elo0]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [h727, hlam, p819_1]
                                                  · have p819_0 := h819c.1
                                                    have p819_1 := h819c.2.1
                                                    have p819_2 := h819c.2.2.1
                                                    have p819_3 := h819c.2.2.2
                                                    linarith only [hlam, p819_0]
                                                · linarith only [h818, hlam, p776_0]
                                              · linarith only [h6, h817, hlam]
                                      · have p776_0 := h776c.1
                                        have p776_1 := h776c.2.1
                                        have p776_2 := h776c.2.2.1
                                        have p776_3 := h776c.2.2.2
                                        rcases p776_3 (m.d 0 3) (by simp) with h863 | h863
                                        · linarith only [h602, h863, hlam]
                                        · linarith only [h1, h863, hlam]
                                      · have p776_0 := h776c.1
                                        have p776_1 := h776c.2.1
                                        have p776_2 := h776c.2.2.1
                                        have p776_3 := h776c.2.2.2
                                        rcases p776_3 (m.d 0 3) (by simp) with h866 | h866
                                        · linarith only [h602, h866, hlam]
                                        · linarith only [h3, h866, hlam]
                                      · have p776_0 := h776c.1
                                        have p776_1 := h776c.2.1
                                        have p776_2 := h776c.2.2.1
                                        have p776_3 := h776c.2.2.2
                                        linarith only [h727, hlam, p776_1]
                                      · have p776_0 := h776c.1
                                        have p776_1 := h776c.2.1
                                        have p776_2 := h776c.2.2.1
                                        have p776_3 := h776c.2.2.2
                                        linarith only [hlam, p776_0]
                              · linarith only [h769, hlam, p728_0]
                            · linarith only [h5, h768, hlam]
                          · have p728_0 := h728c.1
                            have p728_1 := h728c.2.1
                            have p728_2 := h728c.2.2.1
                            have p728_3 := h728c.2.2.2
                            linarith only [h3, hlam, p728_0]
                          · have p728_0 := h728c.1
                            have p728_1 := h728c.2.1
                            have p728_2 := h728c.2.2.1
                            have p728_3 := h728c.2.2.2
                            linarith only [h662, hlam, p728_0]
                          · have p728_0 := h728c.1
                            have p728_1 := h728c.2.1
                            have p728_2 := h728c.2.2.1
                            have p728_3 := h728c.2.2.2
                            linarith only [hlam, p728_0]
                          · have p728_0 := h728c.1
                            have p728_1 := h728c.2.1
                            have p728_2 := h728c.2.2.1
                            have p728_3 := h728c.2.2.2
                            linarith only [h670, hlam, p728_1]
                          · have p728_0 := h728c.1
                            have p728_1 := h728c.2.1
                            have p728_2 := h728c.2.2.1
                            have p728_3 := h728c.2.2.2
                            linarith only [h672, hlam, p728_1]
                          · have p728_0 := h728c.1
                            have p728_1 := h728c.2.1
                            have p728_2 := h728c.2.2.1
                            have p728_3 := h728c.2.2.2
                            linarith only [h4, hlam, p728_0]
                          · have p728_0 := h728c.1
                            have p728_1 := h728c.2.1
                            have p728_2 := h728c.2.2.1
                            have p728_3 := h728c.2.2.2
                            linarith only [h663, hlam, p728_0]
                          · have p728_0 := h728c.1
                            have p728_1 := h728c.2.1
                            have p728_2 := h728c.2.2.1
                            have p728_3 := h728c.2.2.2
                            linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p728_1, u2elo0]
                          · have p728_0 := h728c.1
                            have p728_1 := h728c.2.1
                            have p728_2 := h728c.2.2.1
                            have p728_3 := h728c.2.2.2
                            linarith only [hlam, p728_0]
                          · have p728_0 := h728c.1
                            have p728_1 := h728c.2.1
                            have p728_2 := h728c.2.2.1
                            have p728_3 := h728c.2.2.2
                            linarith only [h674, hlam, p728_0]
                          · have p728_0 := h728c.1
                            have p728_1 := h728c.2.1
                            have p728_2 := h728c.2.2.1
                            have p728_3 := h728c.2.2.2
                            linarith only [h5, hlam, p728_0]
                          · have p728_0 := h728c.1
                            have p728_1 := h728c.2.1
                            have p728_2 := h728c.2.2.1
                            have p728_3 := h728c.2.2.2
                            linarith only [h664, hlam, p728_0]
                          · have p728_0 := h728c.1
                            have p728_1 := h728c.2.1
                            have p728_2 := h728c.2.2.1
                            have p728_3 := h728c.2.2.2
                            linarith only [h0, h664, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p728_1, u2elo0]
                          · have p728_0 := h728c.1
                            have p728_1 := h728c.2.1
                            have p728_2 := h728c.2.2.1
                            have p728_3 := h728c.2.2.2
                            linarith only [h0, h664, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p728_1, u2elo0]
                          · have p728_0 := h728c.1
                            have p728_1 := h728c.2.1
                            have p728_2 := h728c.2.2.1
                            have p728_3 := h728c.2.2.2
                            linarith only [hlam, p728_0]
                        · linarith only [h0, h1, h6, h662, h663, h669, h727, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h889 | h889
                  · linarith only [h6, h661, h669, h889, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h891 | h891
                    · linarith only [h3, h602, h891, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h893 | h893
                      · linarith only [h4, h665, h669, h893, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h895 | h895
                        · rcases h2bigk with h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c
                          · have p896_0 := h896c.1
                            have p896_1 := h896c.2.1
                            have p896_2 := h896c.2.2.1
                            have p896_3 := h896c.2.2.2
                            linarith only [hlam, p896_0]
                          · have p896_0 := h896c.1
                            have p896_1 := h896c.2.1
                            have p896_2 := h896c.2.2.1
                            have p896_3 := h896c.2.2.2
                            linarith only [hc12, hlam, hphi, p896_1, u2elo0]
                          · have p896_0 := h896c.1
                            have p896_1 := h896c.2.1
                            have p896_2 := h896c.2.2.1
                            have p896_3 := h896c.2.2.2
                            rcases p896_3 (m.d 0 2) (by simp) with h899 | h899
                            · rcases p896_3 (m.d 1 2) (by simp) with h900 | h900
                              · linarith only [h0, h900, hlam]
                              · linarith only [h662, h900, hlam]
                            · linarith only [h899, hlam, p896_0]
                          · have p896_0 := h896c.1
                            have p896_1 := h896c.2.1
                            have p896_2 := h896c.2.2.1
                            have p896_3 := h896c.2.2.2
                            rcases p896_3 (m.d 0 2) (by simp) with h904 | h904
                            · rcases p896_3 (m.d 1 2) (by simp) with h905 | h905
                              · linarith only [h0, h905, hlam]
                              · linarith only [h663, h905, hlam]
                            · linarith only [h904, hlam, p896_0]
                          · have p896_0 := h896c.1
                            have p896_1 := h896c.2.1
                            have p896_2 := h896c.2.2.1
                            have p896_3 := h896c.2.2.2
                            rcases p896_3 (m.d 0 2) (by simp) with h909 | h909
                            · rcases p896_3 (m.d 1 2) (by simp) with h910 | h910
                              · linarith only [h0, h910, hlam]
                              · linarith only [h664, h910, hlam]
                            · linarith only [h909, hlam, p896_0]
                          · have p896_0 := h896c.1
                            have p896_1 := h896c.2.1
                            have p896_2 := h896c.2.2.1
                            have p896_3 := h896c.2.2.2
                            linarith only [h0, hlam, p896_1]
                          · have p896_0 := h896c.1
                            have p896_1 := h896c.2.1
                            have p896_2 := h896c.2.2.1
                            have p896_3 := h896c.2.2.2
                            linarith only [hlam, p896_0]
                          · have p896_0 := h896c.1
                            have p896_1 := h896c.2.1
                            have p896_2 := h896c.2.2.1
                            have p896_3 := h896c.2.2.2
                            rcases p896_3 (m.d 0 2) (by simp) with h916 | h916
                            · rcases p896_3 (m.d 1 2) (by simp) with h917 | h917
                              · rcases p896_3 (m.d 2 3) (by simp) with h918 | h918
                                · linarith only [h918, hlam, p896_0]
                                · rcases p896_3 (m.d 2 4) (by simp) with h920 | h920
                                  · linarith only [h663, h920, hlam]
                                  · linarith only [h889, h920, hlam]
                              · linarith only [h917, hlam, p896_0]
                            · linarith only [h3, h916, hlam]
                          · have p896_0 := h896c.1
                            have p896_1 := h896c.2.1
                            have p896_2 := h896c.2.2.1
                            have p896_3 := h896c.2.2.2
                            rcases p896_3 (m.d 0 2) (by simp) with h925 | h925
                            · rcases p896_3 (m.d 1 2) (by simp) with h926 | h926
                              · rcases p896_3 (m.d 2 3) (by simp) with h927 | h927
                                · linarith only [h662, h927, hlam]
                                · rcases p896_3 (m.d 2 4) (by simp) with h929 | h929
                                  · linarith only [h929, hlam, p896_0]
                                  · rcases p896_3 (m.d 2 5) (by simp) with h931 | h931
                                    · linarith only [h664, h931, hlam]
                                    · linarith only [h893, h931, hlam]
                              · linarith only [h926, hlam, p896_0]
                            · linarith only [h4, h925, hlam]
                          · have p896_0 := h896c.1
                            have p896_1 := h896c.2.1
                            have p896_2 := h896c.2.2.1
                            have p896_3 := h896c.2.2.2
                            rcases p896_3 (m.d 0 2) (by simp) with h936 | h936
                            · rcases p896_3 (m.d 1 2) (by simp) with h937 | h937
                              · rcases p896_3 (m.d 2 3) (by simp) with h938 | h938
                                · linarith only [h662, h938, hlam]
                                · rcases p896_3 (m.d 2 4) (by simp) with h940 | h940
                                  · linarith only [h663, h940, hlam]
                                  · rcases p896_3 (m.d 2 5) (by simp) with h942 | h942
                                    · linarith only [h942, hlam, p896_0]
                                    · rcases h3bigk with h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c
                                      · have p944_0 := h944c.1
                                        have p944_1 := h944c.2.1
                                        have p944_2 := h944c.2.2.1
                                        have p944_3 := h944c.2.2.2
                                        linarith only [hlam, p944_0]
                                      · have p944_0 := h944c.1
                                        have p944_1 := h944c.2.1
                                        have p944_2 := h944c.2.2.1
                                        have p944_3 := h944c.2.2.2
                                        linarith only [h602, h662, hc23, hc35, hlam, hphi, p944_1]
                                      · have p944_0 := h944c.1
                                        have p944_1 := h944c.2.1
                                        have p944_2 := h944c.2.2.1
                                        have p944_3 := h944c.2.2.2
                                        linarith only [h602, hc23, hc35, hlam, hphi, p944_1]
                                      · have p944_0 := h944c.1
                                        have p944_1 := h944c.2.1
                                        have p944_2 := h944c.2.2.1
                                        have p944_3 := h944c.2.2.2
                                        linarith only [h6, hlam, p944_0]
                                      · have p944_0 := h944c.1
                                        have p944_1 := h944c.2.1
                                        have p944_2 := h944c.2.2.1
                                        have p944_3 := h944c.2.2.2
                                        linarith only [h602, hlam, p944_0]
                                      · have p944_0 := h944c.1
                                        have p944_1 := h944c.2.1
                                        have p944_2 := h944c.2.2.1
                                        have p944_3 := h944c.2.2.2
                                        linarith only [h1, hlam, p944_0]
                                      · have p944_0 := h944c.1
                                        have p944_1 := h944c.2.1
                                        have p944_2 := h944c.2.2.1
                                        have p944_3 := h944c.2.2.2
                                        linarith only [hlam, p944_0]
                                      · have p944_0 := h944c.1
                                        have p944_1 := h944c.2.1
                                        have p944_2 := h944c.2.2.1
                                        have p944_3 := h944c.2.2.2
                                        linarith only [h665, h669, hc23, hc45, hlam, hphi, ht34, p944_1]
                                      · have p944_0 := h944c.1
                                        have p944_1 := h944c.2.1
                                        have p944_2 := h944c.2.2.1
                                        have p944_3 := h944c.2.2.2
                                        linarith only [h665, hlam, p944_0]
                                      · have p944_0 := h944c.1
                                        have p944_1 := h944c.2.1
                                        have p944_2 := h944c.2.2.1
                                        have p944_3 := h944c.2.2.2
                                        linarith only [h667, hlam, p944_0]
                                      · have p944_0 := h944c.1
                                        have p944_1 := h944c.2.1
                                        have p944_2 := h944c.2.2.1
                                        have p944_3 := h944c.2.2.2
                                        linarith only [h3, hlam, p944_1]
                                      · have p944_0 := h944c.1
                                        have p944_1 := h944c.2.1
                                        have p944_2 := h944c.2.2.1
                                        have p944_3 := h944c.2.2.2
                                        linarith only [h662, hlam, p944_1]
                                      · have p944_0 := h944c.1
                                        have p944_1 := h944c.2.1
                                        have p944_2 := h944c.2.2.1
                                        have p944_3 := h944c.2.2.2
                                        linarith only [hlam, p944_0]
                                      · have p944_0 := h944c.1
                                        have p944_1 := h944c.2.1
                                        have p944_2 := h944c.2.2.1
                                        have p944_3 := h944c.2.2.2
                                        linarith only [h889, hlam, p944_0]
                                      · have p944_0 := h944c.1
                                        have p944_1 := h944c.2.1
                                        have p944_2 := h944c.2.2.1
                                        have p944_3 := h944c.2.2.2
                                        linarith only [h891, hlam, p944_0]
                                      · have p944_0 := h944c.1
                                        have p944_1 := h944c.2.1
                                        have p944_2 := h944c.2.2.1
                                        have p944_3 := h944c.2.2.2
                                        rcases p944_3 (m.d 0 3) (by simp) with h960 | h960
                                        · linarith only [h960, hlam, p944_0]
                                        · rcases p944_3 (m.d 1 3) (by simp) with h962 | h962
                                          · linarith only [h665, h962, hlam]
                                          · rcases p944_3 (m.d 2 3) (by simp) with h964 | h964
                                            · linarith only [h889, h964, hlam]
                                            · rcases p944_3 (m.d 3 4) (by simp) with h966 | h966
                                              · rcases p944_3 (m.d 3 5) (by simp) with h967 | h967
                                                · linarith only [h895, h967, hlam]
                                                · linarith only [h602, h967, hlam]
                                              · linarith only [h966, hlam, p944_0]
                                      · have p944_0 := h944c.1
                                        have p944_1 := h944c.2.1
                                        have p944_2 := h944c.2.2.1
                                        have p944_3 := h944c.2.2.2
                                        rcases p944_3 (m.d 0 3) (by simp) with h971 | h971
                                        · linarith only [h6, h971, hlam]
                                        · linarith only [h1, h971, hlam]
                                      · have p944_0 := h944c.1
                                        have p944_1 := h944c.2.1
                                        have p944_2 := h944c.2.2.1
                                        have p944_3 := h944c.2.2.2
                                        rcases p944_3 (m.d 0 3) (by simp) with h974 | h974
                                        · linarith only [h6, h974, hlam]
                                        · linarith only [h3, h974, hlam]
                                      · have p944_0 := h944c.1
                                        have p944_1 := h944c.2.1
                                        have p944_2 := h944c.2.2.1
                                        have p944_3 := h944c.2.2.2
                                        linarith only [hlam, p944_0]
                                      · have p944_0 := h944c.1
                                        have p944_1 := h944c.2.1
                                        have p944_2 := h944c.2.2.1
                                        have p944_3 := h944c.2.2.2
                                        linarith only [h602, hc03, hc34, hlam, hphi, p944_1]
                                      · have p944_0 := h944c.1
                                        have p944_1 := h944c.2.1
                                        have p944_2 := h944c.2.2.1
                                        have p944_3 := h944c.2.2.2
                                        rcases p944_3 (m.d 0 3) (by simp) with h979 | h979
                                        · linarith only [h979, hlam, p944_0]
                                        · rcases p944_3 (m.d 1 3) (by simp) with h981 | h981
                                          · linarith only [h667, h981, hlam]
                                          · rcases p944_3 (m.d 2 3) (by simp) with h983 | h983
                                            · linarith only [h891, h983, hlam]
                                            · rcases p944_3 (m.d 3 4) (by simp) with h985 | h985
                                              · rcases p944_3 (m.d 3 5) (by simp) with h986 | h986
                                                · rcases h5bigk with h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c | h987c
                                                  · have p987_0 := h987c.1
                                                    have p987_1 := h987c.2.1
                                                    have p987_2 := h987c.2.2.1
                                                    have p987_3 := h987c.2.2.2
                                                    linarith only [hlam, p987_0]
                                                  · have p987_0 := h987c.1
                                                    have p987_1 := h987c.2.1
                                                    have p987_2 := h987c.2.2.1
                                                    have p987_3 := h987c.2.2.2
                                                    rcases p987_3 (m.d 0 5) (by simp) with h989 | h989
                                                    · rcases p987_3 (m.d 1 5) (by simp) with h990 | h990
                                                      · linarith only [h2, h990, hlam]
                                                      · rcases p987_3 (m.d 2 5) (by simp) with h992 | h992
                                                        · linarith only [h5, h992, hlam]
                                                        · rcases p987_3 (m.d 3 5) (by simp) with h994 | h994
                                                          · rcases p987_3 (m.d 4 5) (by simp) with h995 | h995
                                                            · linarith only [h661, h995, hlam]
                                                            · linarith only [h669, h995, hlam]
                                                          · linarith only [h667, h994, hlam]
                                                    · linarith only [h2, h989, hlam]
                                                  · have p987_0 := h987c.1
                                                    have p987_1 := h987c.2.1
                                                    have p987_2 := h987c.2.2.1
                                                    have p987_3 := h987c.2.2.2
                                                    rcases p987_3 (m.d 0 5) (by simp) with h1000 | h1000
                                                    · rcases p987_3 (m.d 1 5) (by simp) with h1001 | h1001
                                                      · linarith only [h1001, h2, hlam]
                                                      · linarith only [h1001, h664, hlam]
                                                    · linarith only [h1000, h5, hlam]
                                                  · have p987_0 := h987c.1
                                                    have p987_1 := h987c.2.1
                                                    have p987_2 := h987c.2.2.1
                                                    have p987_3 := h987c.2.2.2
                                                    linarith only [h602, hlam, p987_0]
                                                  · have p987_0 := h987c.1
                                                    have p987_1 := h987c.2.1
                                                    have p987_2 := h987c.2.2.1
                                                    have p987_3 := h987c.2.2.2
                                                    linarith only [h5, h669, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p987_1, u2elo0]
                                                  · have p987_0 := h987c.1
                                                    have p987_1 := h987c.2.1
                                                    have p987_2 := h987c.2.2.1
                                                    have p987_3 := h987c.2.2.2
                                                    linarith only [h2, hlam, p987_0]
                                                  · have p987_0 := h987c.1
                                                    have p987_1 := h987c.2.1
                                                    have p987_2 := h987c.2.2.1
                                                    have p987_3 := h987c.2.2.2
                                                    linarith only [hlam, p987_0]
                                                  · have p987_0 := h987c.1
                                                    have p987_1 := h987c.2.1
                                                    have p987_2 := h987c.2.2.1
                                                    have p987_3 := h987c.2.2.2
                                                    linarith only [h4, h661, h669, h889, h893, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p987_1, u2elo0]
                                                  · have p987_0 := h987c.1
                                                    have p987_1 := h987c.2.1
                                                    have p987_2 := h987c.2.2.1
                                                    have p987_3 := h987c.2.2.2
                                                    linarith only [h667, hlam, p987_0]
                                                  · have p987_0 := h987c.1
                                                    have p987_1 := h987c.2.1
                                                    have p987_2 := h987c.2.2.1
                                                    have p987_3 := h987c.2.2.2
                                                    linarith only [h669, hlam, p987_0]
                                                  · have p987_0 := h987c.1
                                                    have p987_1 := h987c.2.1
                                                    have p987_2 := h987c.2.2.1
                                                    have p987_3 := h987c.2.2.2
                                                    linarith only [h5, hlam, p987_1]
                                                  · have p987_0 := h987c.1
                                                    have p987_1 := h987c.2.1
                                                    have p987_2 := h987c.2.2.1
                                                    have p987_3 := h987c.2.2.2
                                                    linarith only [h664, hlam, p987_1]
                                                  · have p987_0 := h987c.1
                                                    have p987_1 := h987c.2.1
                                                    have p987_2 := h987c.2.2.1
                                                    have p987_3 := h987c.2.2.2
                                                    linarith only [hlam, p987_0]
                                                  · have p987_0 := h987c.1
                                                    have p987_1 := h987c.2.1
                                                    have p987_2 := h987c.2.2.1
                                                    have p987_3 := h987c.2.2.2
                                                    linarith only [h891, hlam, p987_1]
                                                  · have p987_0 := h987c.1
                                                    have p987_1 := h987c.2.1
                                                    have p987_2 := h987c.2.2.1
                                                    have p987_3 := h987c.2.2.2
                                                    linarith only [h893, hlam, p987_0]
                                                  · have p987_0 := h987c.1
                                                    have p987_1 := h987c.2.1
                                                    have p987_2 := h987c.2.2.1
                                                    have p987_3 := h987c.2.2.2
                                                    linarith only [h661, h663, h669, h889, hc23, hc35, hlam, hphi, p987_1]
                                                  · have p987_0 := h987c.1
                                                    have p987_1 := h987c.2.1
                                                    have p987_2 := h987c.2.2.1
                                                    have p987_3 := h987c.2.2.2
                                                    rcases p987_3 (m.d 0 5) (by simp) with h1018 | h1018
                                                    · linarith only [h1018, h602, hlam]
                                                    · linarith only [h1018, h2, hlam]
                                                  · have p987_0 := h987c.1
                                                    have p987_1 := h987c.2.1
                                                    have p987_2 := h987c.2.2.1
                                                    have p987_3 := h987c.2.2.2
                                                    rcases p987_3 (m.d 0 5) (by simp) with h1021 | h1021
                                                    · linarith only [h1021, h602, hlam]
                                                    · linarith only [h1021, h5, hlam]
                                                  · have p987_0 := h987c.1
                                                    have p987_1 := h987c.2.1
                                                    have p987_2 := h987c.2.2.1
                                                    have p987_3 := h987c.2.2.2
                                                    linarith only [hlam, p987_0]
                                                  · have p987_0 := h987c.1
                                                    have p987_1 := h987c.2.1
                                                    have p987_2 := h987c.2.2.1
                                                    have p987_3 := h987c.2.2.2
                                                    linarith only [h663, h669, h889, h895, hc23, hc34, hlam, hphi, p987_1]
                                                  · have p987_0 := h987c.1
                                                    have p987_1 := h987c.2.1
                                                    have p987_2 := h987c.2.2.1
                                                    have p987_3 := h987c.2.2.2
                                                    linarith only [h661, hlam, p987_1]
                                                  · have p987_0 := h987c.1
                                                    have p987_1 := h987c.2.1
                                                    have p987_2 := h987c.2.2.1
                                                    have p987_3 := h987c.2.2.2
                                                    linarith only [h4, h661, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p987_1, u2elo0]
                                                  · have p987_0 := h987c.1
                                                    have p987_1 := h987c.2.1
                                                    have p987_2 := h987c.2.2.1
                                                    have p987_3 := h987c.2.2.2
                                                    linarith only [h4, h661, h889, h893, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p987_1, u2elo0]
                                                  · have p987_0 := h987c.1
                                                    have p987_1 := h987c.2.1
                                                    have p987_2 := h987c.2.2.1
                                                    have p987_3 := h987c.2.2.2
                                                    linarith only [h895, hlam, p987_1]
                                                  · have p987_0 := h987c.1
                                                    have p987_1 := h987c.2.1
                                                    have p987_2 := h987c.2.2.1
                                                    have p987_3 := h987c.2.2.2
                                                    linarith only [hlam, p987_0]
                                                · linarith only [h986, hlam, p944_0]
                                              · linarith only [h6, h985, hlam]
                                      · have p944_0 := h944c.1
                                        have p944_1 := h944c.2.1
                                        have p944_2 := h944c.2.2.1
                                        have p944_3 := h944c.2.2.2
                                        rcases p944_3 (m.d 0 3) (by simp) with h1033 | h1033
                                        · linarith only [h1033, h602, hlam]
                                        · linarith only [h1, h1033, hlam]
                                      · have p944_0 := h944c.1
                                        have p944_1 := h944c.2.1
                                        have p944_2 := h944c.2.2.1
                                        have p944_3 := h944c.2.2.2
                                        rcases p944_3 (m.d 0 3) (by simp) with h1036 | h1036
                                        · linarith only [h1036, h602, hlam]
                                        · linarith only [h1036, h3, hlam]
                                      · have p944_0 := h944c.1
                                        have p944_1 := h944c.2.1
                                        have p944_2 := h944c.2.2.1
                                        have p944_3 := h944c.2.2.2
                                        linarith only [h895, hlam, p944_1]
                                      · have p944_0 := h944c.1
                                        have p944_1 := h944c.2.1
                                        have p944_2 := h944c.2.2.1
                                        have p944_3 := h944c.2.2.2
                                        linarith only [hlam, p944_0]
                              · linarith only [h937, hlam, p896_0]
                            · linarith only [h5, h936, hlam]
                          · have p896_0 := h896c.1
                            have p896_1 := h896c.2.1
                            have p896_2 := h896c.2.2.1
                            have p896_3 := h896c.2.2.2
                            linarith only [h3, hlam, p896_0]
                          · have p896_0 := h896c.1
                            have p896_1 := h896c.2.1
                            have p896_2 := h896c.2.2.1
                            have p896_3 := h896c.2.2.2
                            linarith only [h662, hlam, p896_0]
                          · have p896_0 := h896c.1
                            have p896_1 := h896c.2.1
                            have p896_2 := h896c.2.2.1
                            have p896_3 := h896c.2.2.2
                            linarith only [hlam, p896_0]
                          · have p896_0 := h896c.1
                            have p896_1 := h896c.2.1
                            have p896_2 := h896c.2.2.1
                            have p896_3 := h896c.2.2.2
                            linarith only [h889, hlam, p896_1]
                          · have p896_0 := h896c.1
                            have p896_1 := h896c.2.1
                            have p896_2 := h896c.2.2.1
                            have p896_3 := h896c.2.2.2
                            linarith only [h891, hlam, p896_1]
                          · have p896_0 := h896c.1
                            have p896_1 := h896c.2.1
                            have p896_2 := h896c.2.2.1
                            have p896_3 := h896c.2.2.2
                            linarith only [h4, hlam, p896_0]
                          · have p896_0 := h896c.1
                            have p896_1 := h896c.2.1
                            have p896_2 := h896c.2.2.1
                            have p896_3 := h896c.2.2.2
                            linarith only [h663, hlam, p896_0]
                          · have p896_0 := h896c.1
                            have p896_1 := h896c.2.1
                            have p896_2 := h896c.2.2.1
                            have p896_3 := h896c.2.2.2
                            linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p896_1, u2elo0]
                          · have p896_0 := h896c.1
                            have p896_1 := h896c.2.1
                            have p896_2 := h896c.2.2.1
                            have p896_3 := h896c.2.2.2
                            linarith only [hlam, p896_0]
                          · have p896_0 := h896c.1
                            have p896_1 := h896c.2.1
                            have p896_2 := h896c.2.2.1
                            have p896_3 := h896c.2.2.2
                            linarith only [h893, hlam, p896_0]
                          · have p896_0 := h896c.1
                            have p896_1 := h896c.2.1
                            have p896_2 := h896c.2.2.1
                            have p896_3 := h896c.2.2.2
                            linarith only [h5, hlam, p896_0]
                          · have p896_0 := h896c.1
                            have p896_1 := h896c.2.1
                            have p896_2 := h896c.2.2.1
                            have p896_3 := h896c.2.2.2
                            linarith only [h664, hlam, p896_0]
                          · have p896_0 := h896c.1
                            have p896_1 := h896c.2.1
                            have p896_2 := h896c.2.2.1
                            have p896_3 := h896c.2.2.2
                            linarith only [h4, h661, h664, h669, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p896_1, u2elo0]
                          · have p896_0 := h896c.1
                            have p896_1 := h896c.2.1
                            have p896_2 := h896c.2.2.1
                            have p896_3 := h896c.2.2.2
                            linarith only [h4, h661, h664, h669, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p896_1, u2elo0]
                          · have p896_0 := h896c.1
                            have p896_1 := h896c.2.1
                            have p896_2 := h896c.2.2.1
                            have p896_3 := h896c.2.2.2
                            linarith only [hlam, p896_0]
                        · linarith only [h1, h4, h6, h661, h662, h895, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
          · linarith only [h5, h664, hc12, hlam, hphi, u2elo0]
        · linarith only [h4, h662, h663, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
      · linarith only [h3, h662, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1062 | h1062
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1063 | h1063
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1064 | h1064
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1065 | h1065
            · linarith only [h1, h1065, h6, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1067 | h1067
              · linarith only [h1, h1067, h602, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1069 | h1069
                · linarith only [h1069, h2, h661, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1071 | h1071
                  · linarith only [h1071, h3, h6, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1073 | h1073
                    · linarith only [h1, h1062, h1073, h602, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1075 | h1075
                      · linarith only [h1075, h4, h6, h661, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1077 | h1077
                        · rcases h2bigk with h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c
                          · have p1078_0 := h1078c.1
                            have p1078_1 := h1078c.2.1
                            have p1078_2 := h1078c.2.2.1
                            have p1078_3 := h1078c.2.2.2
                            linarith only [hlam, p1078_0]
                          · have p1078_0 := h1078c.1
                            have p1078_1 := h1078c.2.1
                            have p1078_2 := h1078c.2.2.1
                            have p1078_3 := h1078c.2.2.2
                            linarith only [hc12, hlam, hphi, p1078_1, u2elo0]
                          · have p1078_0 := h1078c.1
                            have p1078_1 := h1078c.2.1
                            have p1078_2 := h1078c.2.2.1
                            have p1078_3 := h1078c.2.2.2
                            rcases p1078_3 (m.d 0 2) (by simp) with h1081 | h1081
                            · rcases p1078_3 (m.d 1 2) (by simp) with h1082 | h1082
                              · linarith only [h0, h1082, hlam]
                              · linarith only [h1062, h1082, hlam]
                            · linarith only [h1081, hlam, p1078_0]
                          · have p1078_0 := h1078c.1
                            have p1078_1 := h1078c.2.1
                            have p1078_2 := h1078c.2.2.1
                            have p1078_3 := h1078c.2.2.2
                            rcases p1078_3 (m.d 0 2) (by simp) with h1086 | h1086
                            · rcases p1078_3 (m.d 1 2) (by simp) with h1087 | h1087
                              · linarith only [h0, h1087, hlam]
                              · linarith only [h1063, h1087, hlam]
                            · linarith only [h1086, hlam, p1078_0]
                          · have p1078_0 := h1078c.1
                            have p1078_1 := h1078c.2.1
                            have p1078_2 := h1078c.2.2.1
                            have p1078_3 := h1078c.2.2.2
                            rcases p1078_3 (m.d 0 2) (by simp) with h1091 | h1091
                            · rcases p1078_3 (m.d 1 2) (by simp) with h1092 | h1092
                              · linarith only [h0, h1092, hlam]
                              · linarith only [h1064, h1092, hlam]
                            · linarith only [h1091, hlam, p1078_0]
                          · have p1078_0 := h1078c.1
                            have p1078_1 := h1078c.2.1
                            have p1078_2 := h1078c.2.2.1
                            have p1078_3 := h1078c.2.2.2
                            linarith only [h0, hlam, p1078_1]
                          · have p1078_0 := h1078c.1
                            have p1078_1 := h1078c.2.1
                            have p1078_2 := h1078c.2.2.1
                            have p1078_3 := h1078c.2.2.2
                            linarith only [hlam, p1078_0]
                          · have p1078_0 := h1078c.1
                            have p1078_1 := h1078c.2.1
                            have p1078_2 := h1078c.2.2.1
                            have p1078_3 := h1078c.2.2.2
                            rcases p1078_3 (m.d 0 2) (by simp) with h1098 | h1098
                            · rcases p1078_3 (m.d 1 2) (by simp) with h1099 | h1099
                              · rcases p1078_3 (m.d 2 3) (by simp) with h1100 | h1100
                                · linarith only [h1100, hlam, p1078_0]
                                · rcases p1078_3 (m.d 2 4) (by simp) with h1102 | h1102
                                  · linarith only [h1063, h1102, hlam]
                                  · linarith only [h1071, h1102, hlam]
                              · linarith only [h1099, hlam, p1078_0]
                            · linarith only [h1098, h3, hlam]
                          · have p1078_0 := h1078c.1
                            have p1078_1 := h1078c.2.1
                            have p1078_2 := h1078c.2.2.1
                            have p1078_3 := h1078c.2.2.2
                            rcases p1078_3 (m.d 0 2) (by simp) with h1107 | h1107
                            · rcases p1078_3 (m.d 1 2) (by simp) with h1108 | h1108
                              · rcases p1078_3 (m.d 2 3) (by simp) with h1109 | h1109
                                · linarith only [h1062, h1109, hlam]
                                · rcases p1078_3 (m.d 2 4) (by simp) with h1111 | h1111
                                  · linarith only [h1111, hlam, p1078_0]
                                  · rcases p1078_3 (m.d 2 5) (by simp) with h1113 | h1113
                                    · linarith only [h1064, h1113, hlam]
                                    · linarith only [h1075, h1113, hlam]
                              · linarith only [h1108, hlam, p1078_0]
                            · linarith only [h1107, h4, hlam]
                          · have p1078_0 := h1078c.1
                            have p1078_1 := h1078c.2.1
                            have p1078_2 := h1078c.2.2.1
                            have p1078_3 := h1078c.2.2.2
                            rcases p1078_3 (m.d 0 2) (by simp) with h1118 | h1118
                            · rcases p1078_3 (m.d 1 2) (by simp) with h1119 | h1119
                              · rcases p1078_3 (m.d 2 3) (by simp) with h1120 | h1120
                                · linarith only [h1062, h1120, hlam]
                                · rcases p1078_3 (m.d 2 4) (by simp) with h1122 | h1122
                                  · linarith only [h1063, h1122, hlam]
                                  · rcases p1078_3 (m.d 2 5) (by simp) with h1124 | h1124
                                    · linarith only [h1124, hlam, p1078_0]
                                    · rcases h3bigk with h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c
                                      · have p1126_0 := h1126c.1
                                        have p1126_1 := h1126c.2.1
                                        have p1126_2 := h1126c.2.2.1
                                        have p1126_3 := h1126c.2.2.2
                                        linarith only [hlam, p1126_0]
                                      · have p1126_0 := h1126c.1
                                        have p1126_1 := h1126c.2.1
                                        have p1126_2 := h1126c.2.2.1
                                        have p1126_3 := h1126c.2.2.2
                                        linarith only [h1062, h1077, h6, h661, hc23, hc34, hlam, hphi, p1126_1]
                                      · have p1126_0 := h1126c.1
                                        have p1126_1 := h1126c.2.1
                                        have p1126_2 := h1126c.2.2.1
                                        have p1126_3 := h1126c.2.2.2
                                        linarith only [h1077, h6, h661, hc23, hc34, hlam, hphi, p1126_1]
                                      · have p1126_0 := h1126c.1
                                        have p1126_1 := h1126c.2.1
                                        have p1126_2 := h1126c.2.2.1
                                        have p1126_3 := h1126c.2.2.2
                                        linarith only [h6, hlam, p1126_0]
                                      · have p1126_0 := h1126c.1
                                        have p1126_1 := h1126c.2.1
                                        have p1126_2 := h1126c.2.2.1
                                        have p1126_3 := h1126c.2.2.2
                                        linarith only [h602, hlam, p1126_0]
                                      · have p1126_0 := h1126c.1
                                        have p1126_1 := h1126c.2.1
                                        have p1126_2 := h1126c.2.2.1
                                        have p1126_3 := h1126c.2.2.2
                                        linarith only [h1, hlam, p1126_0]
                                      · have p1126_0 := h1126c.1
                                        have p1126_1 := h1126c.2.1
                                        have p1126_2 := h1126c.2.2.1
                                        have p1126_3 := h1126c.2.2.2
                                        linarith only [hlam, p1126_0]
                                      · have p1126_0 := h1126c.1
                                        have p1126_1 := h1126c.2.1
                                        have p1126_2 := h1126c.2.2.1
                                        have p1126_3 := h1126c.2.2.2
                                        linarith only [h1, h1077, h6, h661, hc23, hc34, hlam, hphi, p1126_1]
                                      · have p1126_0 := h1126c.1
                                        have p1126_1 := h1126c.2.1
                                        have p1126_2 := h1126c.2.2.1
                                        have p1126_3 := h1126c.2.2.2
                                        linarith only [h1065, hlam, p1126_0]
                                      · have p1126_0 := h1126c.1
                                        have p1126_1 := h1126c.2.1
                                        have p1126_2 := h1126c.2.2.1
                                        have p1126_3 := h1126c.2.2.2
                                        linarith only [h1067, hlam, p1126_0]
                                      · have p1126_0 := h1126c.1
                                        have p1126_1 := h1126c.2.1
                                        have p1126_2 := h1126c.2.2.1
                                        have p1126_3 := h1126c.2.2.2
                                        linarith only [h3, hlam, p1126_1]
                                      · have p1126_0 := h1126c.1
                                        have p1126_1 := h1126c.2.1
                                        have p1126_2 := h1126c.2.2.1
                                        have p1126_3 := h1126c.2.2.2
                                        linarith only [h1062, hlam, p1126_1]
                                      · have p1126_0 := h1126c.1
                                        have p1126_1 := h1126c.2.1
                                        have p1126_2 := h1126c.2.2.1
                                        have p1126_3 := h1126c.2.2.2
                                        linarith only [hlam, p1126_0]
                                      · have p1126_0 := h1126c.1
                                        have p1126_1 := h1126c.2.1
                                        have p1126_2 := h1126c.2.2.1
                                        have p1126_3 := h1126c.2.2.2
                                        linarith only [h1071, hlam, p1126_0]
                                      · have p1126_0 := h1126c.1
                                        have p1126_1 := h1126c.2.1
                                        have p1126_2 := h1126c.2.2.1
                                        have p1126_3 := h1126c.2.2.2
                                        linarith only [h1073, hlam, p1126_0]
                                      · have p1126_0 := h1126c.1
                                        have p1126_1 := h1126c.2.1
                                        have p1126_2 := h1126c.2.2.1
                                        have p1126_3 := h1126c.2.2.2
                                        rcases p1126_3 (m.d 0 3) (by simp) with h1142 | h1142
                                        · linarith only [h1142, hlam, p1126_0]
                                        · rcases p1126_3 (m.d 1 3) (by simp) with h1144 | h1144
                                          · linarith only [h1065, h1144, hlam]
                                          · rcases p1126_3 (m.d 2 3) (by simp) with h1146 | h1146
                                            · linarith only [h1071, h1146, hlam]
                                            · rcases p1126_3 (m.d 3 4) (by simp) with h1148 | h1148
                                              · rcases p1126_3 (m.d 3 5) (by simp) with h1149 | h1149
                                                · linarith only [h1077, h1149, hlam]
                                                · linarith only [h1149, h602, hlam]
                                              · linarith only [h1148, hlam, p1126_0]
                                      · have p1126_0 := h1126c.1
                                        have p1126_1 := h1126c.2.1
                                        have p1126_2 := h1126c.2.2.1
                                        have p1126_3 := h1126c.2.2.2
                                        rcases p1126_3 (m.d 0 3) (by simp) with h1153 | h1153
                                        · linarith only [h1153, h6, hlam]
                                        · linarith only [h1, h1153, hlam]
                                      · have p1126_0 := h1126c.1
                                        have p1126_1 := h1126c.2.1
                                        have p1126_2 := h1126c.2.2.1
                                        have p1126_3 := h1126c.2.2.2
                                        rcases p1126_3 (m.d 0 3) (by simp) with h1156 | h1156
                                        · linarith only [h1156, h6, hlam]
                                        · linarith only [h1156, h3, hlam]
                                      · have p1126_0 := h1126c.1
                                        have p1126_1 := h1126c.2.1
                                        have p1126_2 := h1126c.2.2.1
                                        have p1126_3 := h1126c.2.2.2
                                        linarith only [hlam, p1126_0]
                                      · have p1126_0 := h1126c.1
                                        have p1126_1 := h1126c.2.1
                                        have p1126_2 := h1126c.2.2.1
                                        have p1126_3 := h1126c.2.2.2
                                        linarith only [h1077, h6, h661, hc03, hc34, hlam, hphi, p1126_1]
                                      · have p1126_0 := h1126c.1
                                        have p1126_1 := h1126c.2.1
                                        have p1126_2 := h1126c.2.2.1
                                        have p1126_3 := h1126c.2.2.2
                                        rcases p1126_3 (m.d 0 3) (by simp) with h1161 | h1161
                                        · linarith only [h1161, hlam, p1126_0]
                                        · rcases p1126_3 (m.d 1 3) (by simp) with h1163 | h1163
                                          · linarith only [h1067, h1163, hlam]
                                          · rcases p1126_3 (m.d 2 3) (by simp) with h1165 | h1165
                                            · linarith only [h1073, h1165, hlam]
                                            · rcases p1126_3 (m.d 3 4) (by simp) with h1167 | h1167
                                              · rcases p1126_3 (m.d 3 5) (by simp) with h1168 | h1168
                                                · rcases h5bigk with h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c
                                                  · have p1169_0 := h1169c.1
                                                    have p1169_1 := h1169c.2.1
                                                    have p1169_2 := h1169c.2.2.1
                                                    have p1169_3 := h1169c.2.2.2
                                                    linarith only [hlam, p1169_0]
                                                  · have p1169_0 := h1169c.1
                                                    have p1169_1 := h1169c.2.1
                                                    have p1169_2 := h1169c.2.2.1
                                                    have p1169_3 := h1169c.2.2.2
                                                    linarith only [h1062, h1065, h1069, h1077, h661, hc23, hc34, hlam, hphi, p1169_1]
                                                  · have p1169_0 := h1169c.1
                                                    have p1169_1 := h1169c.2.1
                                                    have p1169_2 := h1169c.2.2.1
                                                    have p1169_3 := h1169c.2.2.2
                                                    linarith only [h1071, h1075, h1077, h661, hc23, hc34, hlam, hphi, p1169_1]
                                                  · have p1169_0 := h1169c.1
                                                    have p1169_1 := h1169c.2.1
                                                    have p1169_2 := h1169c.2.2.1
                                                    have p1169_3 := h1169c.2.2.2
                                                    linarith only [h602, hlam, p1169_0]
                                                  · have p1169_0 := h1169c.1
                                                    have p1169_1 := h1169c.2.1
                                                    have p1169_2 := h1169c.2.2.1
                                                    have p1169_3 := h1169c.2.2.2
                                                    linarith only [h661, hlam, p1169_0]
                                                  · have p1169_0 := h1169c.1
                                                    have p1169_1 := h1169c.2.1
                                                    have p1169_2 := h1169c.2.2.1
                                                    have p1169_3 := h1169c.2.2.2
                                                    linarith only [h2, hlam, p1169_0]
                                                  · have p1169_0 := h1169c.1
                                                    have p1169_1 := h1169c.2.1
                                                    have p1169_2 := h1169c.2.2.1
                                                    have p1169_3 := h1169c.2.2.2
                                                    linarith only [hlam, p1169_0]
                                                  · have p1169_0 := h1169c.1
                                                    have p1169_1 := h1169c.2.1
                                                    have p1169_2 := h1169c.2.2.1
                                                    have p1169_3 := h1169c.2.2.2
                                                    linarith only [h1071, h1075, h1077, h2, h661, hc23, hc34, hlam, hphi, p1169_1]
                                                  · have p1169_0 := h1169c.1
                                                    have p1169_1 := h1169c.2.1
                                                    have p1169_2 := h1169c.2.2.1
                                                    have p1169_3 := h1169c.2.2.2
                                                    linarith only [h1067, hlam, p1169_0]
                                                  · have p1169_0 := h1169c.1
                                                    have p1169_1 := h1169c.2.1
                                                    have p1169_2 := h1169c.2.2.1
                                                    have p1169_3 := h1169c.2.2.2
                                                    linarith only [h1069, hlam, p1169_0]
                                                  · have p1169_0 := h1169c.1
                                                    have p1169_1 := h1169c.2.1
                                                    have p1169_2 := h1169c.2.2.1
                                                    have p1169_3 := h1169c.2.2.2
                                                    linarith only [h5, hlam, p1169_1]
                                                  · have p1169_0 := h1169c.1
                                                    have p1169_1 := h1169c.2.1
                                                    have p1169_2 := h1169c.2.2.1
                                                    have p1169_3 := h1169c.2.2.2
                                                    linarith only [h1064, hlam, p1169_1]
                                                  · have p1169_0 := h1169c.1
                                                    have p1169_1 := h1169c.2.1
                                                    have p1169_2 := h1169c.2.2.1
                                                    have p1169_3 := h1169c.2.2.2
                                                    linarith only [hlam, p1169_0]
                                                  · have p1169_0 := h1169c.1
                                                    have p1169_1 := h1169c.2.1
                                                    have p1169_2 := h1169c.2.2.1
                                                    have p1169_3 := h1169c.2.2.2
                                                    linarith only [h1073, hlam, p1169_1]
                                                  · have p1169_0 := h1169c.1
                                                    have p1169_1 := h1169c.2.1
                                                    have p1169_2 := h1169c.2.2.1
                                                    have p1169_3 := h1169c.2.2.2
                                                    linarith only [h1075, hlam, p1169_0]
                                                  · have p1169_0 := h1169c.1
                                                    have p1169_1 := h1169c.2.1
                                                    have p1169_2 := h1169c.2.2.1
                                                    have p1169_3 := h1169c.2.2.2
                                                    rcases p1169_3 (m.d 0 5) (by simp) with h1185 | h1185
                                                    · linarith only [h1185, h602, hlam]
                                                    · rcases p1169_3 (m.d 1 5) (by simp) with h1187 | h1187
                                                      · linarith only [h1067, h1187, hlam]
                                                      · rcases p1169_3 (m.d 2 5) (by simp) with h1189 | h1189
                                                        · linarith only [h1073, h1189, hlam]
                                                        · rcases p1169_3 (m.d 3 5) (by simp) with h1191 | h1191
                                                          · rcases p1169_3 (m.d 4 5) (by simp) with h1192 | h1192
                                                            · linarith only [h1077, h1192, hlam]
                                                            · linarith only [h1192, h661, hlam]
                                                          · linarith only [h1191, h602, hlam]
                                                  · have p1169_0 := h1169c.1
                                                    have p1169_1 := h1169c.2.1
                                                    have p1169_2 := h1169c.2.2.1
                                                    have p1169_3 := h1169c.2.2.2
                                                    rcases p1169_3 (m.d 0 5) (by simp) with h1196 | h1196
                                                    · linarith only [h1196, h602, hlam]
                                                    · linarith only [h1196, h2, hlam]
                                                  · have p1169_0 := h1169c.1
                                                    have p1169_1 := h1169c.2.1
                                                    have p1169_2 := h1169c.2.2.1
                                                    have p1169_3 := h1169c.2.2.2
                                                    rcases p1169_3 (m.d 0 5) (by simp) with h1199 | h1199
                                                    · linarith only [h1199, h602, hlam]
                                                    · linarith only [h1199, h5, hlam]
                                                  · have p1169_0 := h1169c.1
                                                    have p1169_1 := h1169c.2.1
                                                    have p1169_2 := h1169c.2.2.1
                                                    have p1169_3 := h1169c.2.2.2
                                                    linarith only [hlam, p1169_0]
                                                  · have p1169_0 := h1169c.1
                                                    have p1169_1 := h1169c.2.1
                                                    have p1169_2 := h1169c.2.2.1
                                                    have p1169_3 := h1169c.2.2.2
                                                    linarith only [h1, h1062, h1077, h6, h661, hc23, hc34, hlam, hphi, p1169_1]
                                                  · have p1169_0 := h1169c.1
                                                    have p1169_1 := h1169c.2.1
                                                    have p1169_2 := h1169c.2.2.1
                                                    have p1169_3 := h1169c.2.2.2
                                                    linarith only [h1071, h1075, h1077, h5, hc23, hc34, hlam, hphi, p1169_1]
                                                  · have p1169_0 := h1169c.1
                                                    have p1169_1 := h1169c.2.1
                                                    have p1169_2 := h1169c.2.2.1
                                                    have p1169_3 := h1169c.2.2.2
                                                    linarith only [h1064, h1071, h1075, h1077, hc23, hc34, hlam, hphi, p1169_1]
                                                  · have p1169_0 := h1169c.1
                                                    have p1169_1 := h1169c.2.1
                                                    have p1169_2 := h1169c.2.2.1
                                                    have p1169_3 := h1169c.2.2.2
                                                    linarith only [h1071, h1075, h1077, hc23, hc34, hlam, hphi, p1169_1]
                                                  · have p1169_0 := h1169c.1
                                                    have p1169_1 := h1169c.2.1
                                                    have p1169_2 := h1169c.2.2.1
                                                    have p1169_3 := h1169c.2.2.2
                                                    linarith only [h1077, hlam, p1169_1]
                                                  · have p1169_0 := h1169c.1
                                                    have p1169_1 := h1169c.2.1
                                                    have p1169_2 := h1169c.2.2.1
                                                    have p1169_3 := h1169c.2.2.2
                                                    linarith only [hlam, p1169_0]
                                                · linarith only [h1168, hlam, p1126_0]
                                              · linarith only [h1167, h6, hlam]
                                      · have p1126_0 := h1126c.1
                                        have p1126_1 := h1126c.2.1
                                        have p1126_2 := h1126c.2.2.1
                                        have p1126_3 := h1126c.2.2.2
                                        rcases p1126_3 (m.d 0 3) (by simp) with h1211 | h1211
                                        · linarith only [h1211, h602, hlam]
                                        · linarith only [h1, h1211, hlam]
                                      · have p1126_0 := h1126c.1
                                        have p1126_1 := h1126c.2.1
                                        have p1126_2 := h1126c.2.2.1
                                        have p1126_3 := h1126c.2.2.2
                                        rcases p1126_3 (m.d 0 3) (by simp) with h1214 | h1214
                                        · linarith only [h1214, h602, hlam]
                                        · linarith only [h1214, h3, hlam]
                                      · have p1126_0 := h1126c.1
                                        have p1126_1 := h1126c.2.1
                                        have p1126_2 := h1126c.2.2.1
                                        have p1126_3 := h1126c.2.2.2
                                        linarith only [h1077, hlam, p1126_1]
                                      · have p1126_0 := h1126c.1
                                        have p1126_1 := h1126c.2.1
                                        have p1126_2 := h1126c.2.2.1
                                        have p1126_3 := h1126c.2.2.2
                                        linarith only [hlam, p1126_0]
                              · linarith only [h1119, hlam, p1078_0]
                            · linarith only [h1118, h5, hlam]
                          · have p1078_0 := h1078c.1
                            have p1078_1 := h1078c.2.1
                            have p1078_2 := h1078c.2.2.1
                            have p1078_3 := h1078c.2.2.2
                            linarith only [h3, hlam, p1078_0]
                          · have p1078_0 := h1078c.1
                            have p1078_1 := h1078c.2.1
                            have p1078_2 := h1078c.2.2.1
                            have p1078_3 := h1078c.2.2.2
                            linarith only [h1062, hlam, p1078_0]
                          · have p1078_0 := h1078c.1
                            have p1078_1 := h1078c.2.1
                            have p1078_2 := h1078c.2.2.1
                            have p1078_3 := h1078c.2.2.2
                            linarith only [hlam, p1078_0]
                          · have p1078_0 := h1078c.1
                            have p1078_1 := h1078c.2.1
                            have p1078_2 := h1078c.2.2.1
                            have p1078_3 := h1078c.2.2.2
                            linarith only [h1071, hlam, p1078_1]
                          · have p1078_0 := h1078c.1
                            have p1078_1 := h1078c.2.1
                            have p1078_2 := h1078c.2.2.1
                            have p1078_3 := h1078c.2.2.2
                            linarith only [h1073, hlam, p1078_1]
                          · have p1078_0 := h1078c.1
                            have p1078_1 := h1078c.2.1
                            have p1078_2 := h1078c.2.2.1
                            have p1078_3 := h1078c.2.2.2
                            linarith only [h4, hlam, p1078_0]
                          · have p1078_0 := h1078c.1
                            have p1078_1 := h1078c.2.1
                            have p1078_2 := h1078c.2.2.1
                            have p1078_3 := h1078c.2.2.2
                            linarith only [h1063, hlam, p1078_0]
                          · have p1078_0 := h1078c.1
                            have p1078_1 := h1078c.2.1
                            have p1078_2 := h1078c.2.2.1
                            have p1078_3 := h1078c.2.2.2
                            linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1078_1, u2elo0]
                          · have p1078_0 := h1078c.1
                            have p1078_1 := h1078c.2.1
                            have p1078_2 := h1078c.2.2.1
                            have p1078_3 := h1078c.2.2.2
                            linarith only [hlam, p1078_0]
                          · have p1078_0 := h1078c.1
                            have p1078_1 := h1078c.2.1
                            have p1078_2 := h1078c.2.2.1
                            have p1078_3 := h1078c.2.2.2
                            linarith only [h1075, hlam, p1078_0]
                          · have p1078_0 := h1078c.1
                            have p1078_1 := h1078c.2.1
                            have p1078_2 := h1078c.2.2.1
                            have p1078_3 := h1078c.2.2.2
                            linarith only [h5, hlam, p1078_0]
                          · have p1078_0 := h1078c.1
                            have p1078_1 := h1078c.2.1
                            have p1078_2 := h1078c.2.2.1
                            have p1078_3 := h1078c.2.2.2
                            linarith only [h1064, hlam, p1078_0]
                          · have p1078_0 := h1078c.1
                            have p1078_1 := h1078c.2.1
                            have p1078_2 := h1078c.2.2.1
                            have p1078_3 := h1078c.2.2.2
                            linarith only [h0, h1064, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1078_1, u2elo0]
                          · have p1078_0 := h1078c.1
                            have p1078_1 := h1078c.2.1
                            have p1078_2 := h1078c.2.2.1
                            have p1078_3 := h1078c.2.2.2
                            linarith only [h0, h1064, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1078_1, u2elo0]
                          · have p1078_0 := h1078c.1
                            have p1078_1 := h1078c.2.1
                            have p1078_2 := h1078c.2.2.1
                            have p1078_3 := h1078c.2.2.2
                            linarith only [hlam, p1078_0]
                        · rcases h2bigk with h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c
                          · have p1236_0 := h1236c.1
                            have p1236_1 := h1236c.2.1
                            have p1236_2 := h1236c.2.2.1
                            have p1236_3 := h1236c.2.2.2
                            linarith only [hlam, p1236_0]
                          · have p1236_0 := h1236c.1
                            have p1236_1 := h1236c.2.1
                            have p1236_2 := h1236c.2.2.1
                            have p1236_3 := h1236c.2.2.2
                            linarith only [hc12, hlam, hphi, p1236_1, u2elo0]
                          · have p1236_0 := h1236c.1
                            have p1236_1 := h1236c.2.1
                            have p1236_2 := h1236c.2.2.1
                            have p1236_3 := h1236c.2.2.2
                            rcases p1236_3 (m.d 0 2) (by simp) with h1239 | h1239
                            · rcases p1236_3 (m.d 1 2) (by simp) with h1240 | h1240
                              · linarith only [h0, h1240, hlam]
                              · linarith only [h1062, h1240, hlam]
                            · linarith only [h1239, hlam, p1236_0]
                          · have p1236_0 := h1236c.1
                            have p1236_1 := h1236c.2.1
                            have p1236_2 := h1236c.2.2.1
                            have p1236_3 := h1236c.2.2.2
                            rcases p1236_3 (m.d 0 2) (by simp) with h1244 | h1244
                            · rcases p1236_3 (m.d 1 2) (by simp) with h1245 | h1245
                              · linarith only [h0, h1245, hlam]
                              · linarith only [h1063, h1245, hlam]
                            · linarith only [h1244, hlam, p1236_0]
                          · have p1236_0 := h1236c.1
                            have p1236_1 := h1236c.2.1
                            have p1236_2 := h1236c.2.2.1
                            have p1236_3 := h1236c.2.2.2
                            rcases p1236_3 (m.d 0 2) (by simp) with h1249 | h1249
                            · rcases p1236_3 (m.d 1 2) (by simp) with h1250 | h1250
                              · linarith only [h0, h1250, hlam]
                              · linarith only [h1064, h1250, hlam]
                            · linarith only [h1249, hlam, p1236_0]
                          · have p1236_0 := h1236c.1
                            have p1236_1 := h1236c.2.1
                            have p1236_2 := h1236c.2.2.1
                            have p1236_3 := h1236c.2.2.2
                            linarith only [h0, hlam, p1236_1]
                          · have p1236_0 := h1236c.1
                            have p1236_1 := h1236c.2.1
                            have p1236_2 := h1236c.2.2.1
                            have p1236_3 := h1236c.2.2.2
                            linarith only [hlam, p1236_0]
                          · have p1236_0 := h1236c.1
                            have p1236_1 := h1236c.2.1
                            have p1236_2 := h1236c.2.2.1
                            have p1236_3 := h1236c.2.2.2
                            rcases p1236_3 (m.d 0 2) (by simp) with h1256 | h1256
                            · rcases p1236_3 (m.d 1 2) (by simp) with h1257 | h1257
                              · rcases p1236_3 (m.d 2 3) (by simp) with h1258 | h1258
                                · linarith only [h1258, hlam, p1236_0]
                                · rcases p1236_3 (m.d 2 4) (by simp) with h1260 | h1260
                                  · linarith only [h1063, h1260, hlam]
                                  · linarith only [h1071, h1260, hlam]
                              · linarith only [h1257, hlam, p1236_0]
                            · linarith only [h1256, h3, hlam]
                          · have p1236_0 := h1236c.1
                            have p1236_1 := h1236c.2.1
                            have p1236_2 := h1236c.2.2.1
                            have p1236_3 := h1236c.2.2.2
                            rcases p1236_3 (m.d 0 2) (by simp) with h1265 | h1265
                            · rcases p1236_3 (m.d 1 2) (by simp) with h1266 | h1266
                              · rcases p1236_3 (m.d 2 3) (by simp) with h1267 | h1267
                                · linarith only [h1062, h1267, hlam]
                                · rcases p1236_3 (m.d 2 4) (by simp) with h1269 | h1269
                                  · linarith only [h1269, hlam, p1236_0]
                                  · rcases p1236_3 (m.d 2 5) (by simp) with h1271 | h1271
                                    · linarith only [h1064, h1271, hlam]
                                    · linarith only [h1075, h1271, hlam]
                              · linarith only [h1266, hlam, p1236_0]
                            · linarith only [h1265, h4, hlam]
                          · have p1236_0 := h1236c.1
                            have p1236_1 := h1236c.2.1
                            have p1236_2 := h1236c.2.2.1
                            have p1236_3 := h1236c.2.2.2
                            rcases p1236_3 (m.d 0 2) (by simp) with h1276 | h1276
                            · rcases p1236_3 (m.d 1 2) (by simp) with h1277 | h1277
                              · rcases p1236_3 (m.d 2 3) (by simp) with h1278 | h1278
                                · linarith only [h1062, h1278, hlam]
                                · rcases p1236_3 (m.d 2 4) (by simp) with h1280 | h1280
                                  · linarith only [h1063, h1280, hlam]
                                  · rcases p1236_3 (m.d 2 5) (by simp) with h1282 | h1282
                                    · linarith only [h1282, hlam, p1236_0]
                                    · rcases h3bigk with h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [hlam, p1284_0]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [h1062, h1077, h6, hc23, hc45, hlam, hphi, ht34, p1284_1]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [h1077, h6, hc23, hc45, hlam, hphi, ht34, p1284_1]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [h6, hlam, p1284_0]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [h602, hlam, p1284_0]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [h1, hlam, p1284_0]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [hlam, p1284_0]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [h1, h1077, h6, hc23, hc45, hlam, hphi, ht34, p1284_1]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [h1065, hlam, p1284_0]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [h1067, hlam, p1284_0]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [h3, hlam, p1284_1]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [h1062, hlam, p1284_1]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [hlam, p1284_0]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [h1071, hlam, p1284_0]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [h1073, hlam, p1284_0]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [h1077, hc03, hc45, hlam, hphi, ht34, p1284_1]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [h1062, h1077, hc23, hc45, hlam, hphi, ht34, p1284_1]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [h1077, hc23, hc45, hlam, hphi, ht34, p1284_1]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [hlam, p1284_0]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [h1077, hlam, p1284_0]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        rcases p1284_3 (m.d 0 3) (by simp) with h1305 | h1305
                                        · linarith only [h1305, hlam, p1284_0]
                                        · rcases p1284_3 (m.d 1 3) (by simp) with h1307 | h1307
                                          · linarith only [h1067, h1307, hlam]
                                          · rcases p1284_3 (m.d 2 3) (by simp) with h1309 | h1309
                                            · linarith only [h1073, h1309, hlam]
                                            · rcases p1284_3 (m.d 3 4) (by simp) with h1311 | h1311
                                              · linarith only [h1077, h1311, hlam]
                                              · linarith only [h1311, h6, hlam]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        rcases p1284_3 (m.d 0 3) (by simp) with h1314 | h1314
                                        · linarith only [h1314, h602, hlam]
                                        · linarith only [h1, h1314, hlam]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        rcases p1284_3 (m.d 0 3) (by simp) with h1317 | h1317
                                        · linarith only [h1317, h602, hlam]
                                        · linarith only [h1317, h3, hlam]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [h1, h1062, h1077, h6, hc23, hc45, hlam, hphi, ht34, p1284_1]
                                      · have p1284_0 := h1284c.1
                                        have p1284_1 := h1284c.2.1
                                        have p1284_2 := h1284c.2.2.1
                                        have p1284_3 := h1284c.2.2.2
                                        linarith only [hlam, p1284_0]
                              · linarith only [h1277, hlam, p1236_0]
                            · linarith only [h1276, h5, hlam]
                          · have p1236_0 := h1236c.1
                            have p1236_1 := h1236c.2.1
                            have p1236_2 := h1236c.2.2.1
                            have p1236_3 := h1236c.2.2.2
                            linarith only [h3, hlam, p1236_0]
                          · have p1236_0 := h1236c.1
                            have p1236_1 := h1236c.2.1
                            have p1236_2 := h1236c.2.2.1
                            have p1236_3 := h1236c.2.2.2
                            linarith only [h1062, hlam, p1236_0]
                          · have p1236_0 := h1236c.1
                            have p1236_1 := h1236c.2.1
                            have p1236_2 := h1236c.2.2.1
                            have p1236_3 := h1236c.2.2.2
                            linarith only [hlam, p1236_0]
                          · have p1236_0 := h1236c.1
                            have p1236_1 := h1236c.2.1
                            have p1236_2 := h1236c.2.2.1
                            have p1236_3 := h1236c.2.2.2
                            linarith only [h1071, hlam, p1236_1]
                          · have p1236_0 := h1236c.1
                            have p1236_1 := h1236c.2.1
                            have p1236_2 := h1236c.2.2.1
                            have p1236_3 := h1236c.2.2.2
                            linarith only [h1073, hlam, p1236_1]
                          · have p1236_0 := h1236c.1
                            have p1236_1 := h1236c.2.1
                            have p1236_2 := h1236c.2.2.1
                            have p1236_3 := h1236c.2.2.2
                            linarith only [h4, hlam, p1236_0]
                          · have p1236_0 := h1236c.1
                            have p1236_1 := h1236c.2.1
                            have p1236_2 := h1236c.2.2.1
                            have p1236_3 := h1236c.2.2.2
                            linarith only [h1063, hlam, p1236_0]
                          · have p1236_0 := h1236c.1
                            have p1236_1 := h1236c.2.1
                            have p1236_2 := h1236c.2.2.1
                            have p1236_3 := h1236c.2.2.2
                            linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1236_1, u2elo0]
                          · have p1236_0 := h1236c.1
                            have p1236_1 := h1236c.2.1
                            have p1236_2 := h1236c.2.2.1
                            have p1236_3 := h1236c.2.2.2
                            linarith only [hlam, p1236_0]
                          · have p1236_0 := h1236c.1
                            have p1236_1 := h1236c.2.1
                            have p1236_2 := h1236c.2.2.1
                            have p1236_3 := h1236c.2.2.2
                            linarith only [h1075, hlam, p1236_0]
                          · have p1236_0 := h1236c.1
                            have p1236_1 := h1236c.2.1
                            have p1236_2 := h1236c.2.2.1
                            have p1236_3 := h1236c.2.2.2
                            linarith only [h5, hlam, p1236_0]
                          · have p1236_0 := h1236c.1
                            have p1236_1 := h1236c.2.1
                            have p1236_2 := h1236c.2.2.1
                            have p1236_3 := h1236c.2.2.2
                            linarith only [h1064, hlam, p1236_0]
                          · have p1236_0 := h1236c.1
                            have p1236_1 := h1236c.2.1
                            have p1236_2 := h1236c.2.2.1
                            have p1236_3 := h1236c.2.2.2
                            linarith only [h0, h1064, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1236_1, u2elo0]
                          · have p1236_0 := h1236c.1
                            have p1236_1 := h1236c.2.1
                            have p1236_2 := h1236c.2.2.1
                            have p1236_3 := h1236c.2.2.2
                            linarith only [h0, h1064, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1236_1, u2elo0]
                          · have p1236_0 := h1236c.1
                            have p1236_1 := h1236c.2.1
                            have p1236_2 := h1236c.2.2.1
                            have p1236_3 := h1236c.2.2.2
                            linarith only [hlam, p1236_0]
          · linarith only [h1064, h5, hc12, hlam, hphi, u2elo0]
        · linarith only [h1062, h1063, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
      · linarith only [h1062, h3, hc12, hlam, hphi, u2elo0]

set_option maxHeartbeats 8858000 in
set_option maxHeartbeats 8858000 in
theorem r1l7_22_13_15_M_LI_L_I_L_I_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
  · exact r1l7_22_13_15_M_LI_L_I_L_I_x0_x0_x0_x0_x0_x0_x0 m hb2 hb3 hb5 h0 h1 h2 h3 h4 h5 h6
  · exact r1l7_22_13_15_M_LI_L_I_L_I_x0_x0_x0_x0_x0_x0_x1 m hb2 hb3 hb5 h0 h1 h2 h3 h4 h5 h6

set_option maxHeartbeats 8858000 in
set_option maxHeartbeats 8858000 in
theorem r1l7_22_13_15_M_LI_L_I_L_I_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h1342 | h1342
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1343 | h1343
    · linarith only [h1343, h3, h5, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1345 | h1345
      · linarith only [h1345, h4, h5, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1347 | h1347
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1348 | h1348
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1349 | h1349
            · linarith only [h1349, h5, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1351 | h1351
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1352 | h1352
                · linarith only [h1, h1343, h1352, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1354 | h1354
                  · linarith only [h0, h1345, h1348, h1354, h5, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1356 | h1356
                    · linarith only [h1356, h3, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                    · linarith only [h1, h1343, h1351, h1356, hc23, hc35, hlam, hphi]
              · linarith only [h1342, h1351, h3, h5, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
          · linarith only [h1348, h4, h5, hc12, hlam, hphi, u2elo4]
        · linarith only [h1347, h3, h5, hc12, hlam, hphi, u2elo4]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1362 | h1362
    · linarith only [h1342, h1362, h4, h5, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1364 | h1364
      · linarith only [h1364, h4, h5, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1366 | h1366
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1367 | h1367
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1368 | h1368
            · linarith only [h1368, h5, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1370 | h1370
              · linarith only [h1, h1342, h1370, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1372 | h1372
                · linarith only [h1, h1362, h1372, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1374 | h1374
                  · linarith only [h0, h1364, h1367, h1374, h5, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1376 | h1376
                    · linarith only [h1342, h1376, h3, h5, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1378 | h1378
                      · linarith only [h1362, h1378, h3, h5, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1380 | h1380
                        · linarith only [h0, h1367, h1374, h1380, h5, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1382 | h1382
                          · linarith only [h0, h1367, h1376, h1380, h1382, h5, hc23, hc34, hlam, hphi]
                          · rcases h2bigk with h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [hlam, p1384_0]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [h1367, h1376, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1384_1, u2elo4]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1384_1, u2elo4]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [h1376, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1384_1, u2elo4]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [h5, hlam, p1384_0]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [h0, hlam, p1384_1]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [hlam, p1384_0]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [h0, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1384_1, u2elo4]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [h0, h1376, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1384_1, u2elo4]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [h1368, hlam, p1384_0]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [h3, hlam, p1384_0]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [h1366, hlam, p1384_0]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [hlam, p1384_0]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [h1376, hlam, p1384_1]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [h1378, hlam, p1384_1]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [h4, hlam, p1384_0]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [h1367, hlam, p1384_0]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [h4, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1384_1, u2elo4]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [hlam, p1384_0]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [h1380, hlam, p1384_0]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [hc02, hlam, hphi, p1384_1, u2elo4]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [h1366, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1384_1, u2elo4]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              rcases p1384_3 (m.d 0 2) (by simp) with h1407 | h1407
                              · linarith only [h1407, h5, hlam]
                              · linarith only [h1407, h3, hlam]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              rcases p1384_3 (m.d 0 2) (by simp) with h1410 | h1410
                              · linarith only [h1410, h5, hlam]
                              · linarith only [h1410, h4, hlam]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [hlam, p1384_0]
          · linarith only [h1367, h4, hc12, hlam, hphi, u2elo0]
        · linarith only [h1366, h3, h5, hc12, hlam, hphi, u2elo4]

end R2N4
