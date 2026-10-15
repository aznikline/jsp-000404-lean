import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5884000 in
set_option maxHeartbeats 5884000 in
theorem r1l7_22_14_M_IR_L_I_x1_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h664 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h4bigk := hb4.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h665 | h665
  · rcases m.htr 0 2 4 (by decide) (by decide) with h666 | h666
    · rcases m.htr 0 2 5 (by decide) (by decide) with h667 | h667
      · rcases m.htr 0 3 4 (by decide) (by decide) with h668 | h668
        · rcases m.htr 0 4 5 (by decide) (by decide) with h669 | h669
          · rcases m.htr 1 2 3 (by decide) (by decide) with h670 | h670
            · rcases m.htr 1 2 4 (by decide) (by decide) with h671 | h671
              · rcases m.htr 1 2 5 (by decide) (by decide) with h672 | h672
                · rcases m.htr 1 3 4 (by decide) (by decide) with h673 | h673
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h674 | h674
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h675 | h675
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h676 | h676
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h677 | h677
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h678 | h678
                            · rcases h2bigk with h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [hlam, p679_0]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [h0, hlam, p679_1]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [h675, h678, hc02, hc45, hlam, hphi, ht0b, ht5b, p679_1]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                rcases p679_3 (m.d 0 2) (by simp) with h683 | h683
                                · rcases p679_3 (m.d 1 2) (by simp) with h684 | h684
                                  · rcases p679_3 (m.d 2 3) (by simp) with h685 | h685
                                    · linarith only [h665, h685, hlam]
                                    · linarith only [h675, h685, hlam]
                                  · linarith only [h671, h684, hlam]
                                · linarith only [h683, hlam, p679_0]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                rcases p679_3 (m.d 0 2) (by simp) with h690 | h690
                                · rcases p679_3 (m.d 1 2) (by simp) with h691 | h691
                                  · rcases p679_3 (m.d 2 3) (by simp) with h692 | h692
                                    · linarith only [h665, h692, hlam]
                                    · linarith only [h676, h692, hlam]
                                  · linarith only [h672, h691, hlam]
                                · linarith only [h690, hlam, p679_0]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [h0, h664, h672, h674, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p679_1, u2ehi4]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [hlam, p679_0]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [h675, h678, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p679_1]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                rcases p679_3 (m.d 0 2) (by simp) with h700 | h700
                                · linarith only [h0, h700, hlam]
                                · linarith only [h666, h700, hlam]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                rcases p679_3 (m.d 0 2) (by simp) with h703 | h703
                                · linarith only [h0, h703, hlam]
                                · linarith only [h667, h703, hlam]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [h665, hlam, p679_0]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [h670, hlam, p679_0]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [hlam, p679_0]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [h665, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p679_1, u2ehi3]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [h0, h665, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p679_1, u2ehi4]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [h666, hlam, p679_0]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [h671, hlam, p679_0]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [h675, hlam, p679_1]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [hlam, p679_0]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [hc24, hlam, hphi, p679_1, u2ehi4]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [h667, hlam, p679_0]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [h672, hlam, p679_0]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [h676, hlam, p679_1]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [h677, hlam, p679_0]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [hlam, p679_0]
                            · linarith only [h0, h664, h674, h678, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h0, h664, h674, h677, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h723 | h723
                          · linarith only [h675, h676, h723, hlam]
                          · linarith only [h0, h664, h669, h723, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h0, h664, h673, h675, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h664, h669, h671, h674, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h728 | h728
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h729 | h729
                      · linarith only [h670, h673, h729, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h731 | h731
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h732 | h732
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h733 | h733
                            · rcases h2bigk with h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c
                              · have p734_0 := h734c.1
                                have p734_1 := h734c.2.1
                                have p734_2 := h734c.2.2.1
                                have p734_3 := h734c.2.2.2
                                linarith only [hlam, p734_0]
                              · have p734_0 := h734c.1
                                have p734_1 := h734c.2.1
                                have p734_2 := h734c.2.2.1
                                have p734_3 := h734c.2.2.2
                                linarith only [h0, hlam, p734_1]
                              · have p734_0 := h734c.1
                                have p734_1 := h734c.2.1
                                have p734_2 := h734c.2.2.1
                                have p734_3 := h734c.2.2.2
                                rcases p734_3 (m.d 0 2) (by simp) with h737 | h737
                                · rcases p734_3 (m.d 1 2) (by simp) with h738 | h738
                                  · rcases p734_3 (m.d 2 3) (by simp) with h739 | h739
                                    · linarith only [h739, hlam, p734_0]
                                    · rcases p734_3 (m.d 2 4) (by simp) with h741 | h741
                                      · linarith only [h666, h741, hlam]
                                      · linarith only [h729, h741, hlam]
                                  · linarith only [h670, h738, hlam]
                                · linarith only [h737, hlam, p734_0]
                              · have p734_0 := h734c.1
                                have p734_1 := h734c.2.1
                                have p734_2 := h734c.2.2.1
                                have p734_3 := h734c.2.2.2
                                rcases p734_3 (m.d 0 2) (by simp) with h746 | h746
                                · rcases p734_3 (m.d 1 2) (by simp) with h747 | h747
                                  · rcases p734_3 (m.d 2 3) (by simp) with h748 | h748
                                    · linarith only [h665, h748, hlam]
                                    · rcases p734_3 (m.d 2 4) (by simp) with h750 | h750
                                      · linarith only [h750, hlam, p734_0]
                                      · rcases p734_3 (m.d 2 5) (by simp) with h752 | h752
                                        · linarith only [h667, h752, hlam]
                                        · rcases h4bigk with h754c | h754c | h754c | h754c | h754c | h754c | h754c | h754c | h754c | h754c | h754c | h754c | h754c | h754c | h754c | h754c | h754c | h754c | h754c | h754c | h754c | h754c | h754c | h754c | h754c
                                          · have p754_0 := h754c.1
                                            have p754_1 := h754c.2.1
                                            have p754_2 := h754c.2.2.1
                                            have p754_3 := h754c.2.2.2
                                            linarith only [hlam, p754_0]
                                          · have p754_0 := h754c.1
                                            have p754_1 := h754c.2.1
                                            have p754_2 := h754c.2.2.1
                                            have p754_3 := h754c.2.2.2
                                            linarith only [h0, h664, h671, h729, h731, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p754_1, u2ehi4]
                                          · have p754_0 := h754c.1
                                            have p754_1 := h754c.2.1
                                            have p754_2 := h754c.2.2.1
                                            have p754_3 := h754c.2.2.2
                                            linarith only [h0, h664, h729, h731, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p754_1, u2ehi4]
                                          · have p754_0 := h754c.1
                                            have p754_1 := h754c.2.1
                                            have p754_2 := h754c.2.2.1
                                            have p754_3 := h754c.2.2.2
                                            linarith only [h0, h664, h670, h673, h731, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p754_1, u2ehi4]
                                          · have p754_0 := h754c.1
                                            have p754_1 := h754c.2.1
                                            have p754_2 := h754c.2.2.1
                                            have p754_3 := h754c.2.2.2
                                            rcases p754_3 (m.d 0 4) (by simp) with h759 | h759
                                            · rcases p754_3 (m.d 1 4) (by simp) with h760 | h760
                                              · linarith only [h664, h760, hlam]
                                              · linarith only [h728, h760, hlam]
                                            · linarith only [h759, hlam, p754_0]
                                          · have p754_0 := h754c.1
                                            have p754_1 := h754c.2.1
                                            have p754_2 := h754c.2.2.1
                                            have p754_3 := h754c.2.2.2
                                            linarith only [h664, hlam, p754_1]
                                          · have p754_0 := h754c.1
                                            have p754_1 := h754c.2.1
                                            have p754_2 := h754c.2.2.1
                                            have p754_3 := h754c.2.2.2
                                            linarith only [hlam, p754_0]
                                          · have p754_0 := h754c.1
                                            have p754_1 := h754c.2.1
                                            have p754_2 := h754c.2.2.1
                                            have p754_3 := h754c.2.2.2
                                            linarith only [h0, h664, h729, h731, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p754_1, u2ehi4]
                                          · have p754_0 := h754c.1
                                            have p754_1 := h754c.2.1
                                            have p754_2 := h754c.2.2.1
                                            have p754_3 := h754c.2.2.2
                                            linarith only [h673, hlam, p754_1]
                                          · have p754_0 := h754c.1
                                            have p754_1 := h754c.2.1
                                            have p754_2 := h754c.2.2.1
                                            have p754_3 := h754c.2.2.2
                                            linarith only [h0, h664, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p754_1]
                                          · have p754_0 := h754c.1
                                            have p754_1 := h754c.2.1
                                            have p754_2 := h754c.2.2.1
                                            have p754_3 := h754c.2.2.2
                                            linarith only [h666, hlam, p754_1]
                                          · have p754_0 := h754c.1
                                            have p754_1 := h754c.2.1
                                            have p754_2 := h754c.2.2.1
                                            have p754_3 := h754c.2.2.2
                                            linarith only [h671, hlam, p754_1]
                                          · have p754_0 := h754c.1
                                            have p754_1 := h754c.2.1
                                            have p754_2 := h754c.2.2.1
                                            have p754_3 := h754c.2.2.2
                                            linarith only [hlam, p754_0]
                                          · have p754_0 := h754c.1
                                            have p754_1 := h754c.2.1
                                            have p754_2 := h754c.2.2.1
                                            have p754_3 := h754c.2.2.2
                                            linarith only [h729, hlam, p754_1]
                                          · have p754_0 := h754c.1
                                            have p754_1 := h754c.2.1
                                            have p754_2 := h754c.2.2.1
                                            have p754_3 := h754c.2.2.2
                                            linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p734_1, p754_1]
                                          · have p754_0 := h754c.1
                                            have p754_1 := h754c.2.1
                                            have p754_2 := h754c.2.2.1
                                            have p754_3 := h754c.2.2.2
                                            linarith only [h668, hlam, p754_1]
                                          · have p754_0 := h754c.1
                                            have p754_1 := h754c.2.1
                                            have p754_2 := h754c.2.2.1
                                            have p754_3 := h754c.2.2.2
                                            linarith only [h0, h665, h668, h671, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p754_1, u2ehi3]
                                          · have p754_0 := h754c.1
                                            have p754_1 := h754c.2.1
                                            have p754_2 := h754c.2.2.1
                                            have p754_3 := h754c.2.2.2
                                            linarith only [h0, h665, h668, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p754_1, u2ehi3]
                                          · have p754_0 := h754c.1
                                            have p754_1 := h754c.2.1
                                            have p754_2 := h754c.2.2.1
                                            have p754_3 := h754c.2.2.2
                                            linarith only [hlam, p754_0]
                                          · have p754_0 := h754c.1
                                            have p754_1 := h754c.2.1
                                            have p754_2 := h754c.2.2.1
                                            have p754_3 := h754c.2.2.2
                                            rcases p754_3 (m.d 0 4) (by simp) with h778 | h778
                                            · rcases p754_3 (m.d 1 4) (by simp) with h779 | h779
                                              · linarith only [h673, h779, hlam]
                                              · linarith only [h728, h779, hlam]
                                            · linarith only [h669, h778, hlam]
                                          · have p754_0 := h754c.1
                                            have p754_1 := h754c.2.1
                                            have p754_2 := h754c.2.2.1
                                            have p754_3 := h754c.2.2.2
                                            linarith only [h669, hlam, p754_0]
                                          · have p754_0 := h754c.1
                                            have p754_1 := h754c.2.1
                                            have p754_2 := h754c.2.2.1
                                            have p754_3 := h754c.2.2.2
                                            linarith only [h728, hlam, p754_0]
                                          · have p754_0 := h754c.1
                                            have p754_1 := h754c.2.1
                                            have p754_2 := h754c.2.2.1
                                            have p754_3 := h754c.2.2.2
                                            linarith only [h732, hlam, p754_0]
                                          · have p754_0 := h754c.1
                                            have p754_1 := h754c.2.1
                                            have p754_2 := h754c.2.2.1
                                            have p754_3 := h754c.2.2.2
                                            linarith only [h733, hlam, p754_0]
                                          · have p754_0 := h754c.1
                                            have p754_1 := h754c.2.1
                                            have p754_2 := h754c.2.2.1
                                            have p754_3 := h754c.2.2.2
                                            linarith only [hlam, p754_0]
                                  · linarith only [h671, h747, hlam]
                                · linarith only [h746, hlam, p734_0]
                              · have p734_0 := h734c.1
                                have p734_1 := h734c.2.1
                                have p734_2 := h734c.2.2.1
                                have p734_3 := h734c.2.2.2
                                rcases p734_3 (m.d 0 2) (by simp) with h790 | h790
                                · rcases p734_3 (m.d 1 2) (by simp) with h791 | h791
                                  · rcases p734_3 (m.d 2 3) (by simp) with h792 | h792
                                    · linarith only [h665, h792, hlam]
                                    · linarith only [h731, h792, hlam]
                                  · linarith only [h672, h791, hlam]
                                · linarith only [h790, hlam, p734_0]
                              · have p734_0 := h734c.1
                                have p734_1 := h734c.2.1
                                have p734_2 := h734c.2.2.1
                                have p734_3 := h734c.2.2.2
                                linarith only [h0, h664, h670, h673, h731, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p734_1, u2ehi4]
                              · have p734_0 := h734c.1
                                have p734_1 := h734c.2.1
                                have p734_2 := h734c.2.2.1
                                have p734_3 := h734c.2.2.2
                                linarith only [hlam, p734_0]
                              · have p734_0 := h734c.1
                                have p734_1 := h734c.2.1
                                have p734_2 := h734c.2.2.1
                                have p734_3 := h734c.2.2.2
                                rcases p734_3 (m.d 0 2) (by simp) with h799 | h799
                                · linarith only [h0, h799, hlam]
                                · linarith only [h665, h799, hlam]
                              · have p734_0 := h734c.1
                                have p734_1 := h734c.2.1
                                have p734_2 := h734c.2.2.1
                                have p734_3 := h734c.2.2.2
                                rcases p734_3 (m.d 0 2) (by simp) with h802 | h802
                                · linarith only [h0, h802, hlam]
                                · linarith only [h666, h802, hlam]
                              · have p734_0 := h734c.1
                                have p734_1 := h734c.2.1
                                have p734_2 := h734c.2.2.1
                                have p734_3 := h734c.2.2.2
                                rcases p734_3 (m.d 0 2) (by simp) with h805 | h805
                                · linarith only [h0, h805, hlam]
                                · linarith only [h667, h805, hlam]
                              · have p734_0 := h734c.1
                                have p734_1 := h734c.2.1
                                have p734_2 := h734c.2.2.1
                                have p734_3 := h734c.2.2.2
                                linarith only [h665, hlam, p734_0]
                              · have p734_0 := h734c.1
                                have p734_1 := h734c.2.1
                                have p734_2 := h734c.2.2.1
                                have p734_3 := h734c.2.2.2
                                linarith only [h670, hlam, p734_0]
                              · have p734_0 := h734c.1
                                have p734_1 := h734c.2.1
                                have p734_2 := h734c.2.2.1
                                have p734_3 := h734c.2.2.2
                                linarith only [hlam, p734_0]
                              · have p734_0 := h734c.1
                                have p734_1 := h734c.2.1
                                have p734_2 := h734c.2.2.1
                                have p734_3 := h734c.2.2.2
                                linarith only [h729, hlam, p734_0]
                              · have p734_0 := h734c.1
                                have p734_1 := h734c.2.1
                                have p734_2 := h734c.2.2.1
                                have p734_3 := h734c.2.2.2
                                linarith only [h664, h668, h670, h673, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p734_1, u2ehi4]
                              · have p734_0 := h734c.1
                                have p734_1 := h734c.2.1
                                have p734_2 := h734c.2.2.1
                                have p734_3 := h734c.2.2.2
                                linarith only [h666, hlam, p734_0]
                              · have p734_0 := h734c.1
                                have p734_1 := h734c.2.1
                                have p734_2 := h734c.2.2.1
                                have p734_3 := h734c.2.2.2
                                linarith only [h671, hlam, p734_0]
                              · have p734_0 := h734c.1
                                have p734_1 := h734c.2.1
                                have p734_2 := h734c.2.2.1
                                have p734_3 := h734c.2.2.2
                                linarith only [hc24, hlam, hphi, p734_1, u2ehi2]
                              · have p734_0 := h734c.1
                                have p734_1 := h734c.2.1
                                have p734_2 := h734c.2.2.1
                                have p734_3 := h734c.2.2.2
                                linarith only [hlam, p734_0]
                              · have p734_0 := h734c.1
                                have p734_1 := h734c.2.1
                                have p734_2 := h734c.2.2.1
                                have p734_3 := h734c.2.2.2
                                linarith only [h0, h664, h671, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p734_1, u2ehi4]
                              · have p734_0 := h734c.1
                                have p734_1 := h734c.2.1
                                have p734_2 := h734c.2.2.1
                                have p734_3 := h734c.2.2.2
                                linarith only [h667, hlam, p734_0]
                              · have p734_0 := h734c.1
                                have p734_1 := h734c.2.1
                                have p734_2 := h734c.2.2.1
                                have p734_3 := h734c.2.2.2
                                linarith only [h672, hlam, p734_0]
                              · have p734_0 := h734c.1
                                have p734_1 := h734c.2.1
                                have p734_2 := h734c.2.2.1
                                have p734_3 := h734c.2.2.2
                                linarith only [h731, hlam, p734_1]
                              · have p734_0 := h734c.1
                                have p734_1 := h734c.2.1
                                have p734_2 := h734c.2.2.1
                                have p734_3 := h734c.2.2.2
                                linarith only [h732, hlam, p734_0]
                              · have p734_0 := h734c.1
                                have p734_1 := h734c.2.1
                                have p734_2 := h734c.2.2.1
                                have p734_3 := h734c.2.2.2
                                linarith only [hlam, p734_0]
                            · linarith only [h670, h673, h733, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                          · linarith only [h0, h664, h728, h732, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h825 | h825
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h826 | h826
                            · rcases h2bigk with h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [hlam, p827_0]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [h0, hlam, p827_1]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                rcases p827_3 (m.d 0 2) (by simp) with h830 | h830
                                · rcases p827_3 (m.d 1 2) (by simp) with h831 | h831
                                  · rcases p827_3 (m.d 2 3) (by simp) with h832 | h832
                                    · linarith only [h832, hlam, p827_0]
                                    · rcases p827_3 (m.d 2 4) (by simp) with h834 | h834
                                      · linarith only [h666, h834, hlam]
                                      · linarith only [h729, h834, hlam]
                                  · linarith only [h670, h831, hlam]
                                · linarith only [h830, hlam, p827_0]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                rcases p827_3 (m.d 0 2) (by simp) with h839 | h839
                                · rcases p827_3 (m.d 1 2) (by simp) with h840 | h840
                                  · rcases p827_3 (m.d 2 3) (by simp) with h841 | h841
                                    · linarith only [h665, h841, hlam]
                                    · rcases p827_3 (m.d 2 4) (by simp) with h843 | h843
                                      · linarith only [h843, hlam, p827_0]
                                      · rcases p827_3 (m.d 2 5) (by simp) with h845 | h845
                                        · linarith only [h667, h845, hlam]
                                        · rcases h4bigk with h847c | h847c | h847c | h847c | h847c | h847c | h847c | h847c | h847c | h847c | h847c | h847c | h847c | h847c | h847c | h847c | h847c | h847c | h847c | h847c | h847c | h847c | h847c | h847c | h847c
                                          · have p847_0 := h847c.1
                                            have p847_1 := h847c.2.1
                                            have p847_2 := h847c.2.2.1
                                            have p847_3 := h847c.2.2.2
                                            linarith only [hlam, p847_0]
                                          · have p847_0 := h847c.1
                                            have p847_1 := h847c.2.1
                                            have p847_2 := h847c.2.2.1
                                            have p847_3 := h847c.2.2.2
                                            linarith only [h0, h664, h671, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p847_1, u2ehi3]
                                          · have p847_0 := h847c.1
                                            have p847_1 := h847c.2.1
                                            have p847_2 := h847c.2.2.1
                                            have p847_3 := h847c.2.2.2
                                            linarith only [h0, h664, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p847_1, u2ehi3]
                                          · have p847_0 := h847c.1
                                            have p847_1 := h847c.2.1
                                            have p847_2 := h847c.2.2.1
                                            have p847_3 := h847c.2.2.2
                                            linarith only [h0, h664, h670, h673, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p847_1, u2ehi2]
                                          · have p847_0 := h847c.1
                                            have p847_1 := h847c.2.1
                                            have p847_2 := h847c.2.2.1
                                            have p847_3 := h847c.2.2.2
                                            rcases p847_3 (m.d 0 4) (by simp) with h852 | h852
                                            · rcases p847_3 (m.d 1 4) (by simp) with h853 | h853
                                              · linarith only [h664, h853, hlam]
                                              · linarith only [h728, h853, hlam]
                                            · linarith only [h852, hlam, p847_0]
                                          · have p847_0 := h847c.1
                                            have p847_1 := h847c.2.1
                                            have p847_2 := h847c.2.2.1
                                            have p847_3 := h847c.2.2.2
                                            linarith only [h664, hlam, p847_1]
                                          · have p847_0 := h847c.1
                                            have p847_1 := h847c.2.1
                                            have p847_2 := h847c.2.2.1
                                            have p847_3 := h847c.2.2.2
                                            linarith only [hlam, p847_0]
                                          · have p847_0 := h847c.1
                                            have p847_1 := h847c.2.1
                                            have p847_2 := h847c.2.2.1
                                            have p847_3 := h847c.2.2.2
                                            linarith only [h0, h664, h731, h825, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p847_1, u2ehi2]
                                          · have p847_0 := h847c.1
                                            have p847_1 := h847c.2.1
                                            have p847_2 := h847c.2.2.1
                                            have p847_3 := h847c.2.2.2
                                            linarith only [h673, hlam, p847_1]
                                          · have p847_0 := h847c.1
                                            have p847_1 := h847c.2.1
                                            have p847_2 := h847c.2.2.1
                                            have p847_3 := h847c.2.2.2
                                            linarith only [h0, h664, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p847_1]
                                          · have p847_0 := h847c.1
                                            have p847_1 := h847c.2.1
                                            have p847_2 := h847c.2.2.1
                                            have p847_3 := h847c.2.2.2
                                            linarith only [h666, hlam, p847_1]
                                          · have p847_0 := h847c.1
                                            have p847_1 := h847c.2.1
                                            have p847_2 := h847c.2.2.1
                                            have p847_3 := h847c.2.2.2
                                            linarith only [h671, hlam, p847_1]
                                          · have p847_0 := h847c.1
                                            have p847_1 := h847c.2.1
                                            have p847_2 := h847c.2.2.1
                                            have p847_3 := h847c.2.2.2
                                            linarith only [hlam, p847_0]
                                          · have p847_0 := h847c.1
                                            have p847_1 := h847c.2.1
                                            have p847_2 := h847c.2.2.1
                                            have p847_3 := h847c.2.2.2
                                            linarith only [h729, hlam, p847_1]
                                          · have p847_0 := h847c.1
                                            have p847_1 := h847c.2.1
                                            have p847_2 := h847c.2.2.1
                                            have p847_3 := h847c.2.2.2
                                            linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p827_1, p847_1]
                                          · have p847_0 := h847c.1
                                            have p847_1 := h847c.2.1
                                            have p847_2 := h847c.2.2.1
                                            have p847_3 := h847c.2.2.2
                                            linarith only [h668, hlam, p847_1]
                                          · have p847_0 := h847c.1
                                            have p847_1 := h847c.2.1
                                            have p847_2 := h847c.2.2.1
                                            have p847_3 := h847c.2.2.2
                                            linarith only [h671, hc34, hlam, hphi, ht23, p847_1, u2ehi3]
                                          · have p847_0 := h847c.1
                                            have p847_1 := h847c.2.1
                                            have p847_2 := h847c.2.2.1
                                            have p847_3 := h847c.2.2.2
                                            linarith only [h0, h665, h668, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p847_1, u2ehi3]
                                          · have p847_0 := h847c.1
                                            have p847_1 := h847c.2.1
                                            have p847_2 := h847c.2.2.1
                                            have p847_3 := h847c.2.2.2
                                            linarith only [hlam, p847_0]
                                          · have p847_0 := h847c.1
                                            have p847_1 := h847c.2.1
                                            have p847_2 := h847c.2.2.1
                                            have p847_3 := h847c.2.2.2
                                            rcases p847_3 (m.d 0 4) (by simp) with h871 | h871
                                            · rcases p847_3 (m.d 1 4) (by simp) with h872 | h872
                                              · linarith only [h673, h872, hlam]
                                              · linarith only [h728, h872, hlam]
                                            · linarith only [h669, h871, hlam]
                                          · have p847_0 := h847c.1
                                            have p847_1 := h847c.2.1
                                            have p847_2 := h847c.2.2.1
                                            have p847_3 := h847c.2.2.2
                                            linarith only [h669, hlam, p847_0]
                                          · have p847_0 := h847c.1
                                            have p847_1 := h847c.2.1
                                            have p847_2 := h847c.2.2.1
                                            have p847_3 := h847c.2.2.2
                                            linarith only [h728, hlam, p847_0]
                                          · have p847_0 := h847c.1
                                            have p847_1 := h847c.2.1
                                            have p847_2 := h847c.2.2.1
                                            have p847_3 := h847c.2.2.2
                                            linarith only [h825, hlam, p847_0]
                                          · have p847_0 := h847c.1
                                            have p847_1 := h847c.2.1
                                            have p847_2 := h847c.2.2.1
                                            have p847_3 := h847c.2.2.2
                                            linarith only [h826, hlam, p847_0]
                                          · have p847_0 := h847c.1
                                            have p847_1 := h847c.2.1
                                            have p847_2 := h847c.2.2.1
                                            have p847_3 := h847c.2.2.2
                                            linarith only [hlam, p847_0]
                                  · linarith only [h671, h840, hlam]
                                · linarith only [h839, hlam, p827_0]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                rcases p827_3 (m.d 0 2) (by simp) with h883 | h883
                                · rcases p827_3 (m.d 1 2) (by simp) with h884 | h884
                                  · rcases p827_3 (m.d 2 3) (by simp) with h885 | h885
                                    · linarith only [h665, h885, hlam]
                                    · rcases p827_3 (m.d 2 4) (by simp) with h887 | h887
                                      · linarith only [h666, h887, hlam]
                                      · linarith only [h825, h887, hlam]
                                  · linarith only [h672, h884, hlam]
                                · linarith only [h883, hlam, p827_0]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [h0, h664, h672, h728, h731, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p827_1, u2ehi2]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [hlam, p827_0]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                rcases p827_3 (m.d 0 2) (by simp) with h894 | h894
                                · linarith only [h0, h894, hlam]
                                · linarith only [h665, h894, hlam]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                rcases p827_3 (m.d 0 2) (by simp) with h897 | h897
                                · linarith only [h0, h897, hlam]
                                · linarith only [h666, h897, hlam]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                rcases p827_3 (m.d 0 2) (by simp) with h900 | h900
                                · linarith only [h0, h900, hlam]
                                · linarith only [h667, h900, hlam]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [h665, hlam, p827_0]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [h670, hlam, p827_0]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [hlam, p827_0]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [h729, hlam, p827_0]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [h731, hlam, p827_0]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [h666, hlam, p827_0]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [h671, hlam, p827_0]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [hc24, hlam, hphi, p827_1, u2ehi2]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [hlam, p827_0]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [h664, h671, h731, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p827_1, u2ehi2]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [h667, hlam, p827_0]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [h672, hlam, p827_0]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [hc25, hlam, hphi, p827_1, u2ehi2]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [h825, hlam, p827_0]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [hlam, p827_0]
                            · linarith only [h670, h673, h826, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                          · linarith only [h0, h664, h728, h825, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h664, h669, h671, h728, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                · linarith only [h0, h664, h671, h672, hc25, hlam, hphi, u2ehi3]
              · linarith only [h0, h664, h667, h669, h671, hc24, hlam, hphi, u2ehi4]
            · linarith only [h0, h664, h665, h667, h669, h670, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h924 | h924
            · rcases m.htr 1 2 4 (by decide) (by decide) with h925 | h925
              · rcases m.htr 1 2 5 (by decide) (by decide) with h926 | h926
                · rcases m.htr 1 3 4 (by decide) (by decide) with h927 | h927
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h928 | h928
                    · linarith only [h664, h669, h928, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h930 | h930
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h931 | h931
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h932 | h932
                          · linarith only [h664, h669, h925, h932, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h934 | h934
                            · linarith only [h664, h669, h925, h930, h934, hlam]
                            · rcases h2bigk with h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c
                              · have p936_0 := h936c.1
                                have p936_1 := h936c.2.1
                                have p936_2 := h936c.2.2.1
                                have p936_3 := h936c.2.2.2
                                linarith only [hlam, p936_0]
                              · have p936_0 := h936c.1
                                have p936_1 := h936c.2.1
                                have p936_2 := h936c.2.2.1
                                have p936_3 := h936c.2.2.2
                                linarith only [h0, hlam, p936_1]
                              · have p936_0 := h936c.1
                                have p936_1 := h936c.2.1
                                have p936_2 := h936c.2.2.1
                                have p936_3 := h936c.2.2.2
                                rcases p936_3 (m.d 0 2) (by simp) with h939 | h939
                                · rcases p936_3 (m.d 1 2) (by simp) with h940 | h940
                                  · rcases p936_3 (m.d 2 3) (by simp) with h941 | h941
                                    · linarith only [h941, hlam, p936_0]
                                    · rcases p936_3 (m.d 2 4) (by simp) with h943 | h943
                                      · linarith only [h666, h943, hlam]
                                      · rcases p936_3 (m.d 2 5) (by simp) with h945 | h945
                                        · linarith only [h667, h945, hlam]
                                        · rcases h4bigk with h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c
                                          · have p947_0 := h947c.1
                                            have p947_1 := h947c.2.1
                                            have p947_2 := h947c.2.2.1
                                            have p947_3 := h947c.2.2.2
                                            linarith only [hlam, p947_0]
                                          · have p947_0 := h947c.1
                                            have p947_1 := h947c.2.1
                                            have p947_2 := h947c.2.2.1
                                            have p947_3 := h947c.2.2.2
                                            linarith only [h669, h925, hc45, hlam, hphi, ht23, ht34, p947_1, u2ehi3]
                                          · have p947_0 := h947c.1
                                            have p947_1 := h947c.2.1
                                            have p947_2 := h947c.2.2.1
                                            have p947_3 := h947c.2.2.2
                                            linarith only [h669, hc45, hlam, hphi, ht23, ht34, p947_1, u2ehi3]
                                          · have p947_0 := h947c.1
                                            have p947_1 := h947c.2.1
                                            have p947_2 := h947c.2.2.1
                                            have p947_3 := h947c.2.2.2
                                            linarith only [h669, hc34, hc45, hlam, hphi, p947_1]
                                          · have p947_0 := h947c.1
                                            have p947_1 := h947c.2.1
                                            have p947_2 := h947c.2.2.1
                                            have p947_3 := h947c.2.2.2
                                            linarith only [h669, hlam, p947_0]
                                          · have p947_0 := h947c.1
                                            have p947_1 := h947c.2.1
                                            have p947_2 := h947c.2.2.1
                                            have p947_3 := h947c.2.2.2
                                            linarith only [h664, hlam, p947_1]
                                          · have p947_0 := h947c.1
                                            have p947_1 := h947c.2.1
                                            have p947_2 := h947c.2.2.1
                                            have p947_3 := h947c.2.2.2
                                            linarith only [hlam, p947_0]
                                          · have p947_0 := h947c.1
                                            have p947_1 := h947c.2.1
                                            have p947_2 := h947c.2.2.1
                                            have p947_3 := h947c.2.2.2
                                            linarith only [h664, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p947_1, u2ehi3]
                                          · have p947_0 := h947c.1
                                            have p947_1 := h947c.2.1
                                            have p947_2 := h947c.2.2.1
                                            have p947_3 := h947c.2.2.2
                                            linarith only [h0, h664, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p947_1]
                                          · have p947_0 := h947c.1
                                            have p947_1 := h947c.2.1
                                            have p947_2 := h947c.2.2.1
                                            have p947_3 := h947c.2.2.2
                                            linarith only [h928, hlam, p947_0]
                                          · have p947_0 := h947c.1
                                            have p947_1 := h947c.2.1
                                            have p947_2 := h947c.2.2.1
                                            have p947_3 := h947c.2.2.2
                                            linarith only [h666, hlam, p947_1]
                                          · have p947_0 := h947c.1
                                            have p947_1 := h947c.2.1
                                            have p947_2 := h947c.2.2.1
                                            have p947_3 := h947c.2.2.2
                                            linarith only [h925, hlam, p947_1]
                                          · have p947_0 := h947c.1
                                            have p947_1 := h947c.2.1
                                            have p947_2 := h947c.2.2.1
                                            have p947_3 := h947c.2.2.2
                                            linarith only [hlam, p947_0]
                                          · have p947_0 := h947c.1
                                            have p947_1 := h947c.2.1
                                            have p947_2 := h947c.2.2.1
                                            have p947_3 := h947c.2.2.2
                                            linarith only [h666, h669, hc34, hc45, hlam, hphi, p947_1]
                                          · have p947_0 := h947c.1
                                            have p947_1 := h947c.2.1
                                            have p947_2 := h947c.2.2.1
                                            have p947_3 := h947c.2.2.2
                                            linarith only [h932, hlam, p947_0]
                                          · have p947_0 := h947c.1
                                            have p947_1 := h947c.2.1
                                            have p947_2 := h947c.2.2.1
                                            have p947_3 := h947c.2.2.2
                                            linarith only [h668, hlam, p947_1]
                                          · have p947_0 := h947c.1
                                            have p947_1 := h947c.2.1
                                            have p947_2 := h947c.2.2.1
                                            have p947_3 := h947c.2.2.2
                                            linarith only [h927, hlam, p947_0]
                                          · have p947_0 := h947c.1
                                            have p947_1 := h947c.2.1
                                            have p947_2 := h947c.2.2.1
                                            have p947_3 := h947c.2.2.2
                                            linarith only [h930, hlam, p947_0]
                                          · have p947_0 := h947c.1
                                            have p947_1 := h947c.2.1
                                            have p947_2 := h947c.2.2.1
                                            have p947_3 := h947c.2.2.2
                                            linarith only [hlam, p947_0]
                                          · have p947_0 := h947c.1
                                            have p947_1 := h947c.2.1
                                            have p947_2 := h947c.2.2.1
                                            have p947_3 := h947c.2.2.2
                                            linarith only [h934, hlam, p947_0]
                                          · have p947_0 := h947c.1
                                            have p947_1 := h947c.2.1
                                            have p947_2 := h947c.2.2.1
                                            have p947_3 := h947c.2.2.2
                                            linarith only [h666, hc45, hlam, hphi, ht23, ht34, p947_1, u2ehi3]
                                          · have p947_0 := h947c.1
                                            have p947_1 := h947c.2.1
                                            have p947_2 := h947c.2.2.1
                                            have p947_3 := h947c.2.2.2
                                            linarith only [h925, hc45, hlam, hphi, ht23, ht34, p947_1, u2ehi3]
                                          · have p947_0 := h947c.1
                                            have p947_1 := h947c.2.1
                                            have p947_2 := h947c.2.2.1
                                            have p947_3 := h947c.2.2.2
                                            linarith only [hc45, hlam, hphi, ht23, ht34, p947_1, u2ehi3]
                                          · have p947_0 := h947c.1
                                            have p947_1 := h947c.2.1
                                            have p947_2 := h947c.2.2.1
                                            have p947_3 := h947c.2.2.2
                                            rcases p947_3 (m.d 0 4) (by simp) with h971 | h971
                                            · linarith only [h669, h971, hlam]
                                            · linarith only [h668, h971, hlam]
                                          · have p947_0 := h947c.1
                                            have p947_1 := h947c.2.1
                                            have p947_2 := h947c.2.2.1
                                            have p947_3 := h947c.2.2.2
                                            linarith only [hlam, p947_0]
                                  · linarith only [h924, h940, hlam]
                                · linarith only [h939, hlam, p936_0]
                              · have p936_0 := h936c.1
                                have p936_1 := h936c.2.1
                                have p936_2 := h936c.2.2.1
                                have p936_3 := h936c.2.2.2
                                rcases p936_3 (m.d 0 2) (by simp) with h977 | h977
                                · rcases p936_3 (m.d 1 2) (by simp) with h978 | h978
                                  · rcases p936_3 (m.d 2 3) (by simp) with h979 | h979
                                    · linarith only [h665, h979, hlam]
                                    · linarith only [h930, h979, hlam]
                                  · linarith only [h925, h978, hlam]
                                · linarith only [h977, hlam, p936_0]
                              · have p936_0 := h936c.1
                                have p936_1 := h936c.2.1
                                have p936_2 := h936c.2.2.1
                                have p936_3 := h936c.2.2.2
                                rcases p936_3 (m.d 0 2) (by simp) with h984 | h984
                                · rcases p936_3 (m.d 1 2) (by simp) with h985 | h985
                                  · rcases p936_3 (m.d 2 3) (by simp) with h986 | h986
                                    · linarith only [h665, h986, hlam]
                                    · linarith only [h931, h986, hlam]
                                  · linarith only [h926, h985, hlam]
                                · linarith only [h984, hlam, p936_0]
                              · have p936_0 := h936c.1
                                have p936_1 := h936c.2.1
                                have p936_2 := h936c.2.2.1
                                have p936_3 := h936c.2.2.2
                                linarith only [h0, h664, h925, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p936_1, u2ehi3]
                              · have p936_0 := h936c.1
                                have p936_1 := h936c.2.1
                                have p936_2 := h936c.2.2.1
                                have p936_3 := h936c.2.2.2
                                linarith only [hlam, p936_0]
                              · have p936_0 := h936c.1
                                have p936_1 := h936c.2.1
                                have p936_2 := h936c.2.2.1
                                have p936_3 := h936c.2.2.2
                                rcases p936_3 (m.d 0 2) (by simp) with h993 | h993
                                · linarith only [h0, h993, hlam]
                                · linarith only [h665, h993, hlam]
                              · have p936_0 := h936c.1
                                have p936_1 := h936c.2.1
                                have p936_2 := h936c.2.2.1
                                have p936_3 := h936c.2.2.2
                                rcases p936_3 (m.d 0 2) (by simp) with h996 | h996
                                · linarith only [h0, h996, hlam]
                                · linarith only [h666, h996, hlam]
                              · have p936_0 := h936c.1
                                have p936_1 := h936c.2.1
                                have p936_2 := h936c.2.2.1
                                have p936_3 := h936c.2.2.2
                                rcases p936_3 (m.d 0 2) (by simp) with h999 | h999
                                · linarith only [h0, h999, hlam]
                                · linarith only [h667, h999, hlam]
                              · have p936_0 := h936c.1
                                have p936_1 := h936c.2.1
                                have p936_2 := h936c.2.2.1
                                have p936_3 := h936c.2.2.2
                                linarith only [h665, hlam, p936_0]
                              · have p936_0 := h936c.1
                                have p936_1 := h936c.2.1
                                have p936_2 := h936c.2.2.1
                                have p936_3 := h936c.2.2.2
                                linarith only [h924, hlam, p936_0]
                              · have p936_0 := h936c.1
                                have p936_1 := h936c.2.1
                                have p936_2 := h936c.2.2.1
                                have p936_3 := h936c.2.2.2
                                linarith only [hlam, p936_0]
                              · have p936_0 := h936c.1
                                have p936_1 := h936c.2.1
                                have p936_2 := h936c.2.2.1
                                have p936_3 := h936c.2.2.2
                                linarith only [hc23, hlam, hphi, p936_1, u2ehi3]
                              · have p936_0 := h936c.1
                                have p936_1 := h936c.2.1
                                have p936_2 := h936c.2.2.1
                                have p936_3 := h936c.2.2.2
                                linarith only [h0, h665, h932, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p936_1, u2ehi3]
                              · have p936_0 := h936c.1
                                have p936_1 := h936c.2.1
                                have p936_2 := h936c.2.2.1
                                have p936_3 := h936c.2.2.2
                                linarith only [h666, hlam, p936_0]
                              · have p936_0 := h936c.1
                                have p936_1 := h936c.2.1
                                have p936_2 := h936c.2.2.1
                                have p936_3 := h936c.2.2.2
                                linarith only [h925, hlam, p936_0]
                              · have p936_0 := h936c.1
                                have p936_1 := h936c.2.1
                                have p936_2 := h936c.2.2.1
                                have p936_3 := h936c.2.2.2
                                linarith only [h930, hlam, p936_1]
                              · have p936_0 := h936c.1
                                have p936_1 := h936c.2.1
                                have p936_2 := h936c.2.2.1
                                have p936_3 := h936c.2.2.2
                                linarith only [hlam, p936_0]
                              · have p936_0 := h936c.1
                                have p936_1 := h936c.2.1
                                have p936_2 := h936c.2.2.1
                                have p936_3 := h936c.2.2.2
                                linarith only [h932, hlam, p936_1]
                              · have p936_0 := h936c.1
                                have p936_1 := h936c.2.1
                                have p936_2 := h936c.2.2.1
                                have p936_3 := h936c.2.2.2
                                linarith only [h667, hlam, p936_0]
                              · have p936_0 := h936c.1
                                have p936_1 := h936c.2.1
                                have p936_2 := h936c.2.2.1
                                have p936_3 := h936c.2.2.2
                                linarith only [h926, hlam, p936_0]
                              · have p936_0 := h936c.1
                                have p936_1 := h936c.2.1
                                have p936_2 := h936c.2.2.1
                                have p936_3 := h936c.2.2.2
                                linarith only [h931, hlam, p936_1]
                              · have p936_0 := h936c.1
                                have p936_1 := h936c.2.1
                                have p936_2 := h936c.2.2.1
                                have p936_3 := h936c.2.2.2
                                linarith only [hc25, hlam, hphi, p936_1, u2ehi3]
                              · have p936_0 := h936c.1
                                have p936_1 := h936c.2.1
                                have p936_2 := h936c.2.2.1
                                have p936_3 := h936c.2.2.2
                                linarith only [hlam, p936_0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1017 | h1017
                          · linarith only [h1017, h664, h669, h925, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1019 | h1019
                            · linarith only [h1019, h668, h669, hlam]
                            · rcases h2bigk with h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [hlam, p1021_0]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [h0, hlam, p1021_1]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                rcases p1021_3 (m.d 0 2) (by simp) with h1024 | h1024
                                · rcases p1021_3 (m.d 1 2) (by simp) with h1025 | h1025
                                  · rcases p1021_3 (m.d 2 3) (by simp) with h1026 | h1026
                                    · linarith only [h1026, hlam, p1021_0]
                                    · rcases p1021_3 (m.d 2 4) (by simp) with h1028 | h1028
                                      · linarith only [h1028, h666, hlam]
                                      · rcases p1021_3 (m.d 2 5) (by simp) with h1030 | h1030
                                        · linarith only [h1030, h667, hlam]
                                        · linarith only [h1030, h931, hlam]
                                  · linarith only [h1025, h924, hlam]
                                · linarith only [h1024, hlam, p1021_0]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                rcases p1021_3 (m.d 0 2) (by simp) with h1035 | h1035
                                · rcases p1021_3 (m.d 1 2) (by simp) with h1036 | h1036
                                  · rcases p1021_3 (m.d 2 3) (by simp) with h1037 | h1037
                                    · linarith only [h1037, h665, hlam]
                                    · linarith only [h1037, h930, hlam]
                                  · linarith only [h1036, h925, hlam]
                                · linarith only [h1035, hlam, p1021_0]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                rcases p1021_3 (m.d 0 2) (by simp) with h1042 | h1042
                                · rcases p1021_3 (m.d 1 2) (by simp) with h1043 | h1043
                                  · rcases p1021_3 (m.d 2 3) (by simp) with h1044 | h1044
                                    · linarith only [h1044, h665, hlam]
                                    · rcases p1021_3 (m.d 2 4) (by simp) with h1046 | h1046
                                      · linarith only [h1046, h666, hlam]
                                      · rcases p1021_3 (m.d 2 5) (by simp) with h1048 | h1048
                                        · linarith only [h1048, hlam, p1021_0]
                                        · rcases h4bigk with h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c
                                          · have p1050_0 := h1050c.1
                                            have p1050_1 := h1050c.2.1
                                            have p1050_2 := h1050c.2.2.1
                                            have p1050_3 := h1050c.2.2.2
                                            linarith only [hlam, p1050_0]
                                          · have p1050_0 := h1050c.1
                                            have p1050_1 := h1050c.2.1
                                            have p1050_2 := h1050c.2.2.1
                                            have p1050_3 := h1050c.2.2.2
                                            linarith only [h669, hc14, hc45, hlam, hphi, p1050_1]
                                          · have p1050_0 := h1050c.1
                                            have p1050_1 := h1050c.2.1
                                            have p1050_2 := h1050c.2.2.1
                                            have p1050_3 := h1050c.2.2.2
                                            linarith only [h669, hc45, hlam, hphi, ht23, ht34, p1050_1, u2ehi3]
                                          · have p1050_0 := h1050c.1
                                            have p1050_1 := h1050c.2.1
                                            have p1050_2 := h1050c.2.2.1
                                            have p1050_3 := h1050c.2.2.2
                                            linarith only [h669, hc34, hc45, hlam, hphi, p1050_1]
                                          · have p1050_0 := h1050c.1
                                            have p1050_1 := h1050c.2.1
                                            have p1050_2 := h1050c.2.2.1
                                            have p1050_3 := h1050c.2.2.2
                                            linarith only [h669, hlam, p1050_0]
                                          · have p1050_0 := h1050c.1
                                            have p1050_1 := h1050c.2.1
                                            have p1050_2 := h1050c.2.2.1
                                            have p1050_3 := h1050c.2.2.2
                                            linarith only [h664, hlam, p1050_1]
                                          · have p1050_0 := h1050c.1
                                            have p1050_1 := h1050c.2.1
                                            have p1050_2 := h1050c.2.2.1
                                            have p1050_3 := h1050c.2.2.2
                                            linarith only [hlam, p1050_0]
                                          · have p1050_0 := h1050c.1
                                            have p1050_1 := h1050c.2.1
                                            have p1050_2 := h1050c.2.2.1
                                            have p1050_3 := h1050c.2.2.2
                                            linarith only [h0, h664, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1050_1, u2ehi3]
                                          · have p1050_0 := h1050c.1
                                            have p1050_1 := h1050c.2.1
                                            have p1050_2 := h1050c.2.2.1
                                            have p1050_3 := h1050c.2.2.2
                                            linarith only [h0, h664, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1050_1]
                                          · have p1050_0 := h1050c.1
                                            have p1050_1 := h1050c.2.1
                                            have p1050_2 := h1050c.2.2.1
                                            have p1050_3 := h1050c.2.2.2
                                            linarith only [h928, hlam, p1050_0]
                                          · have p1050_0 := h1050c.1
                                            have p1050_1 := h1050c.2.1
                                            have p1050_2 := h1050c.2.2.1
                                            have p1050_3 := h1050c.2.2.2
                                            linarith only [h666, hlam, p1050_1]
                                          · have p1050_0 := h1050c.1
                                            have p1050_1 := h1050c.2.1
                                            have p1050_2 := h1050c.2.2.1
                                            have p1050_3 := h1050c.2.2.2
                                            linarith only [h925, hlam, p1050_1]
                                          · have p1050_0 := h1050c.1
                                            have p1050_1 := h1050c.2.1
                                            have p1050_2 := h1050c.2.2.1
                                            have p1050_3 := h1050c.2.2.2
                                            linarith only [hlam, p1050_0]
                                          · have p1050_0 := h1050c.1
                                            have p1050_1 := h1050c.2.1
                                            have p1050_2 := h1050c.2.2.1
                                            have p1050_3 := h1050c.2.2.2
                                            linarith only [h666, h669, hc34, hc45, hlam, hphi, p1050_1]
                                          · have p1050_0 := h1050c.1
                                            have p1050_1 := h1050c.2.1
                                            have p1050_2 := h1050c.2.2.1
                                            have p1050_3 := h1050c.2.2.2
                                            linarith only [h1017, hlam, p1050_0]
                                          · have p1050_0 := h1050c.1
                                            have p1050_1 := h1050c.2.1
                                            have p1050_2 := h1050c.2.2.1
                                            have p1050_3 := h1050c.2.2.2
                                            linarith only [h668, hlam, p1050_1]
                                          · have p1050_0 := h1050c.1
                                            have p1050_1 := h1050c.2.1
                                            have p1050_2 := h1050c.2.2.1
                                            have p1050_3 := h1050c.2.2.2
                                            linarith only [h927, hlam, p1050_0]
                                          · have p1050_0 := h1050c.1
                                            have p1050_1 := h1050c.2.1
                                            have p1050_2 := h1050c.2.2.1
                                            have p1050_3 := h1050c.2.2.2
                                            linarith only [h930, hlam, p1050_0]
                                          · have p1050_0 := h1050c.1
                                            have p1050_1 := h1050c.2.1
                                            have p1050_2 := h1050c.2.2.1
                                            have p1050_3 := h1050c.2.2.2
                                            linarith only [hlam, p1050_0]
                                          · have p1050_0 := h1050c.1
                                            have p1050_1 := h1050c.2.1
                                            have p1050_2 := h1050c.2.2.1
                                            have p1050_3 := h1050c.2.2.2
                                            linarith only [h1019, hlam, p1050_0]
                                          · have p1050_0 := h1050c.1
                                            have p1050_1 := h1050c.2.1
                                            have p1050_2 := h1050c.2.2.1
                                            have p1050_3 := h1050c.2.2.2
                                            linarith only [h666, hc45, hlam, hphi, ht23, ht34, p1050_1, u2ehi3]
                                          · have p1050_0 := h1050c.1
                                            have p1050_1 := h1050c.2.1
                                            have p1050_2 := h1050c.2.2.1
                                            have p1050_3 := h1050c.2.2.2
                                            linarith only [h925, hc45, hlam, hphi, ht23, ht34, p1050_1, u2ehi3]
                                          · have p1050_0 := h1050c.1
                                            have p1050_1 := h1050c.2.1
                                            have p1050_2 := h1050c.2.2.1
                                            have p1050_3 := h1050c.2.2.2
                                            linarith only [hc45, hlam, hphi, ht23, ht34, p1050_1, u2ehi3]
                                          · have p1050_0 := h1050c.1
                                            have p1050_1 := h1050c.2.1
                                            have p1050_2 := h1050c.2.2.1
                                            have p1050_3 := h1050c.2.2.2
                                            rcases p1050_3 (m.d 0 4) (by simp) with h1074 | h1074
                                            · linarith only [h1074, h669, hlam]
                                            · linarith only [h1074, h668, hlam]
                                          · have p1050_0 := h1050c.1
                                            have p1050_1 := h1050c.2.1
                                            have p1050_2 := h1050c.2.2.1
                                            have p1050_3 := h1050c.2.2.2
                                            linarith only [hlam, p1050_0]
                                  · linarith only [h1043, h926, hlam]
                                · linarith only [h1042, hlam, p1021_0]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [h0, h664, h925, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1021_1, u2ehi3]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [hlam, p1021_0]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                rcases p1021_3 (m.d 0 2) (by simp) with h1082 | h1082
                                · linarith only [h0, h1082, hlam]
                                · linarith only [h1082, h665, hlam]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                rcases p1021_3 (m.d 0 2) (by simp) with h1085 | h1085
                                · linarith only [h0, h1085, hlam]
                                · linarith only [h1085, h666, hlam]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                rcases p1021_3 (m.d 0 2) (by simp) with h1088 | h1088
                                · linarith only [h0, h1088, hlam]
                                · linarith only [h1088, h667, hlam]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [h665, hlam, p1021_0]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [h924, hlam, p1021_0]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [hlam, p1021_0]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [hc23, hlam, hphi, p1021_1, u2ehi3]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [h931, hlam, p1021_0]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [h666, hlam, p1021_0]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [h925, hlam, p1021_0]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [h930, hlam, p1021_1]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [hlam, p1021_0]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [h1017, hlam, p1021_1]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [h667, hlam, p1021_0]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [h926, hlam, p1021_0]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [hc25, hlam, hphi, p1021_1, u2ehi2]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [h667, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1021_1, u2ehi3]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [hlam, p1021_0]
                      · linarith only [h668, h669, h930, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h668, h669, h924, h927, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                · linarith only [h0, h667, h926, hlam]
              · linarith only [h0, h667, h925, hc24, hlam, hphi, u2ehi4]
            · linarith only [h0, h664, h666, h924, hc23, hlam, hphi, u2ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1111 | h1111
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1112 | h1112
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1113 | h1113
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1114 | h1114
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1115 | h1115
                  · linarith only [h0, h1115, h664, h665, h668, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1117 | h1117
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1118 | h1118
                      · linarith only [h1118, h665, h668, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1120 | h1120
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1121 | h1121
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1122 | h1122
                            · rcases h2bigk with h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c
                              · have p1123_0 := h1123c.1
                                have p1123_1 := h1123c.2.1
                                have p1123_2 := h1123c.2.2.1
                                have p1123_3 := h1123c.2.2.2
                                linarith only [hlam, p1123_0]
                              · have p1123_0 := h1123c.1
                                have p1123_1 := h1123c.2.1
                                have p1123_2 := h1123c.2.2.1
                                have p1123_3 := h1123c.2.2.2
                                linarith only [h0, hlam, p1123_1]
                              · have p1123_0 := h1123c.1
                                have p1123_1 := h1123c.2.1
                                have p1123_2 := h1123c.2.2.1
                                have p1123_3 := h1123c.2.2.2
                                rcases p1123_3 (m.d 0 2) (by simp) with h1126 | h1126
                                · rcases p1123_3 (m.d 1 2) (by simp) with h1127 | h1127
                                  · rcases p1123_3 (m.d 2 3) (by simp) with h1128 | h1128
                                    · linarith only [h1128, hlam, p1123_0]
                                    · rcases p1123_3 (m.d 2 4) (by simp) with h1130 | h1130
                                      · linarith only [h1130, h666, hlam]
                                      · linarith only [h1118, h1130, hlam]
                                  · linarith only [h1112, h1127, hlam]
                                · linarith only [h1126, hlam, p1123_0]
                              · have p1123_0 := h1123c.1
                                have p1123_1 := h1123c.2.1
                                have p1123_2 := h1123c.2.2.1
                                have p1123_3 := h1123c.2.2.2
                                rcases p1123_3 (m.d 0 2) (by simp) with h1135 | h1135
                                · rcases p1123_3 (m.d 1 2) (by simp) with h1136 | h1136
                                  · rcases p1123_3 (m.d 2 3) (by simp) with h1137 | h1137
                                    · linarith only [h1137, h665, hlam]
                                    · rcases p1123_3 (m.d 2 4) (by simp) with h1139 | h1139
                                      · linarith only [h1139, hlam, p1123_0]
                                      · rcases p1123_3 (m.d 2 5) (by simp) with h1141 | h1141
                                        · linarith only [h1141, h667, hlam]
                                        · rcases h4bigk with h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c
                                          · have p1143_0 := h1143c.1
                                            have p1143_1 := h1143c.2.1
                                            have p1143_2 := h1143c.2.2.1
                                            have p1143_3 := h1143c.2.2.2
                                            linarith only [hlam, p1143_0]
                                          · have p1143_0 := h1143c.1
                                            have p1143_1 := h1143c.2.1
                                            have p1143_2 := h1143c.2.2.1
                                            have p1143_3 := h1143c.2.2.2
                                            linarith only [h0, h1112, h1115, h1120, h664, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1143_1, u2ehi4]
                                          · have p1143_0 := h1143c.1
                                            have p1143_1 := h1143c.2.1
                                            have p1143_2 := h1143c.2.2.1
                                            have p1143_3 := h1143c.2.2.2
                                            linarith only [h0, h1118, h1120, h664, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1143_1, u2ehi4]
                                          · have p1143_0 := h1143c.1
                                            have p1143_1 := h1143c.2.1
                                            have p1143_2 := h1143c.2.2.1
                                            have p1143_3 := h1143c.2.2.2
                                            linarith only [h668, hlam, p1143_0]
                                          · have p1143_0 := h1143c.1
                                            have p1143_1 := h1143c.2.1
                                            have p1143_2 := h1143c.2.2.1
                                            have p1143_3 := h1143c.2.2.2
                                            rcases p1143_3 (m.d 0 4) (by simp) with h1148 | h1148
                                            · rcases p1143_3 (m.d 1 4) (by simp) with h1149 | h1149
                                              · linarith only [h1149, h664, hlam]
                                              · linarith only [h1117, h1149, hlam]
                                            · linarith only [h1148, hlam, p1143_0]
                                          · have p1143_0 := h1143c.1
                                            have p1143_1 := h1143c.2.1
                                            have p1143_2 := h1143c.2.2.1
                                            have p1143_3 := h1143c.2.2.2
                                            linarith only [h664, hlam, p1143_1]
                                          · have p1143_0 := h1143c.1
                                            have p1143_1 := h1143c.2.1
                                            have p1143_2 := h1143c.2.2.1
                                            have p1143_3 := h1143c.2.2.2
                                            linarith only [hlam, p1143_0]
                                          · have p1143_0 := h1143c.1
                                            have p1143_1 := h1143c.2.1
                                            have p1143_2 := h1143c.2.2.1
                                            have p1143_3 := h1143c.2.2.2
                                            linarith only [h0, h1118, h1120, h664, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1143_1, u2ehi4]
                                          · have p1143_0 := h1143c.1
                                            have p1143_1 := h1143c.2.1
                                            have p1143_2 := h1143c.2.2.1
                                            have p1143_3 := h1143c.2.2.2
                                            linarith only [h1115, hlam, p1143_1]
                                          · have p1143_0 := h1143c.1
                                            have p1143_1 := h1143c.2.1
                                            have p1143_2 := h1143c.2.2.1
                                            have p1143_3 := h1143c.2.2.2
                                            linarith only [h0, h664, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1143_1]
                                          · have p1143_0 := h1143c.1
                                            have p1143_1 := h1143c.2.1
                                            have p1143_2 := h1143c.2.2.1
                                            have p1143_3 := h1143c.2.2.2
                                            linarith only [h666, hlam, p1143_1]
                                          · have p1143_0 := h1143c.1
                                            have p1143_1 := h1143c.2.1
                                            have p1143_2 := h1143c.2.2.1
                                            have p1143_3 := h1143c.2.2.2
                                            linarith only [h1113, hlam, p1143_1]
                                          · have p1143_0 := h1143c.1
                                            have p1143_1 := h1143c.2.1
                                            have p1143_2 := h1143c.2.2.1
                                            have p1143_3 := h1143c.2.2.2
                                            linarith only [hlam, p1143_0]
                                          · have p1143_0 := h1143c.1
                                            have p1143_1 := h1143c.2.1
                                            have p1143_2 := h1143c.2.2.1
                                            have p1143_3 := h1143c.2.2.2
                                            linarith only [h1118, hlam, p1143_1]
                                          · have p1143_0 := h1143c.1
                                            have p1143_1 := h1143c.2.1
                                            have p1143_2 := h1143c.2.2.1
                                            have p1143_3 := h1143c.2.2.2
                                            linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1123_1, p1143_1]
                                          · have p1143_0 := h1143c.1
                                            have p1143_1 := h1143c.2.1
                                            have p1143_2 := h1143c.2.2.1
                                            have p1143_3 := h1143c.2.2.2
                                            linarith only [h666, hc34, hlam, hphi, ht23, p1143_1, u2ehi3]
                                          · have p1143_0 := h1143c.1
                                            have p1143_1 := h1143c.2.1
                                            have p1143_2 := h1143c.2.2.1
                                            have p1143_3 := h1143c.2.2.2
                                            linarith only [h1113, hc34, hlam, hphi, ht23, p1143_1, u2ehi3]
                                          · have p1143_0 := h1143c.1
                                            have p1143_1 := h1143c.2.1
                                            have p1143_2 := h1143c.2.2.1
                                            have p1143_3 := h1143c.2.2.2
                                            linarith only [hc34, hlam, hphi, ht23, p1143_1, u2ehi3]
                                          · have p1143_0 := h1143c.1
                                            have p1143_1 := h1143c.2.1
                                            have p1143_2 := h1143c.2.2.1
                                            have p1143_3 := h1143c.2.2.2
                                            linarith only [hlam, p1143_0]
                                          · have p1143_0 := h1143c.1
                                            have p1143_1 := h1143c.2.1
                                            have p1143_2 := h1143c.2.2.1
                                            have p1143_3 := h1143c.2.2.2
                                            rcases p1143_3 (m.d 0 4) (by simp) with h1167 | h1167
                                            · linarith only [h1167, h668, hlam]
                                            · linarith only [h1111, h1167, hlam]
                                          · have p1143_0 := h1143c.1
                                            have p1143_1 := h1143c.2.1
                                            have p1143_2 := h1143c.2.2.1
                                            have p1143_3 := h1143c.2.2.2
                                            linarith only [h1111, hlam, p1143_0]
                                          · have p1143_0 := h1143c.1
                                            have p1143_1 := h1143c.2.1
                                            have p1143_2 := h1143c.2.2.1
                                            have p1143_3 := h1143c.2.2.2
                                            linarith only [h1117, hlam, p1143_0]
                                          · have p1143_0 := h1143c.1
                                            have p1143_1 := h1143c.2.1
                                            have p1143_2 := h1143c.2.2.1
                                            have p1143_3 := h1143c.2.2.2
                                            linarith only [h1121, hlam, p1143_0]
                                          · have p1143_0 := h1143c.1
                                            have p1143_1 := h1143c.2.1
                                            have p1143_2 := h1143c.2.2.1
                                            have p1143_3 := h1143c.2.2.2
                                            linarith only [h1122, hlam, p1143_0]
                                          · have p1143_0 := h1143c.1
                                            have p1143_1 := h1143c.2.1
                                            have p1143_2 := h1143c.2.2.1
                                            have p1143_3 := h1143c.2.2.2
                                            linarith only [hlam, p1143_0]
                                  · linarith only [h1113, h1136, hlam]
                                · linarith only [h1135, hlam, p1123_0]
                              · have p1123_0 := h1123c.1
                                have p1123_1 := h1123c.2.1
                                have p1123_2 := h1123c.2.2.1
                                have p1123_3 := h1123c.2.2.2
                                rcases p1123_3 (m.d 0 2) (by simp) with h1177 | h1177
                                · rcases p1123_3 (m.d 1 2) (by simp) with h1178 | h1178
                                  · rcases p1123_3 (m.d 2 3) (by simp) with h1179 | h1179
                                    · linarith only [h1179, h665, hlam]
                                    · linarith only [h1120, h1179, hlam]
                                  · linarith only [h1114, h1178, hlam]
                                · linarith only [h1177, hlam, p1123_0]
                              · have p1123_0 := h1123c.1
                                have p1123_1 := h1123c.2.1
                                have p1123_2 := h1123c.2.2.1
                                have p1123_3 := h1123c.2.2.2
                                linarith only [h0, h1112, h1115, h1120, h664, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1123_1, u2ehi4]
                              · have p1123_0 := h1123c.1
                                have p1123_1 := h1123c.2.1
                                have p1123_2 := h1123c.2.2.1
                                have p1123_3 := h1123c.2.2.2
                                linarith only [hlam, p1123_0]
                              · have p1123_0 := h1123c.1
                                have p1123_1 := h1123c.2.1
                                have p1123_2 := h1123c.2.2.1
                                have p1123_3 := h1123c.2.2.2
                                rcases p1123_3 (m.d 0 2) (by simp) with h1186 | h1186
                                · linarith only [h0, h1186, hlam]
                                · linarith only [h1186, h665, hlam]
                              · have p1123_0 := h1123c.1
                                have p1123_1 := h1123c.2.1
                                have p1123_2 := h1123c.2.2.1
                                have p1123_3 := h1123c.2.2.2
                                rcases p1123_3 (m.d 0 2) (by simp) with h1189 | h1189
                                · linarith only [h0, h1189, hlam]
                                · linarith only [h1189, h666, hlam]
                              · have p1123_0 := h1123c.1
                                have p1123_1 := h1123c.2.1
                                have p1123_2 := h1123c.2.2.1
                                have p1123_3 := h1123c.2.2.2
                                rcases p1123_3 (m.d 0 2) (by simp) with h1192 | h1192
                                · linarith only [h0, h1192, hlam]
                                · linarith only [h1192, h667, hlam]
                              · have p1123_0 := h1123c.1
                                have p1123_1 := h1123c.2.1
                                have p1123_2 := h1123c.2.2.1
                                have p1123_3 := h1123c.2.2.2
                                linarith only [h665, hlam, p1123_0]
                              · have p1123_0 := h1123c.1
                                have p1123_1 := h1123c.2.1
                                have p1123_2 := h1123c.2.2.1
                                have p1123_3 := h1123c.2.2.2
                                linarith only [h1112, hlam, p1123_0]
                              · have p1123_0 := h1123c.1
                                have p1123_1 := h1123c.2.1
                                have p1123_2 := h1123c.2.2.1
                                have p1123_3 := h1123c.2.2.2
                                linarith only [hlam, p1123_0]
                              · have p1123_0 := h1123c.1
                                have p1123_1 := h1123c.2.1
                                have p1123_2 := h1123c.2.2.1
                                have p1123_3 := h1123c.2.2.2
                                linarith only [h1118, hlam, p1123_0]
                              · have p1123_0 := h1123c.1
                                have p1123_1 := h1123c.2.1
                                have p1123_2 := h1123c.2.2.1
                                have p1123_3 := h1123c.2.2.2
                                linarith only [h1112, h1115, h664, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1123_1, u2ehi4]
                              · have p1123_0 := h1123c.1
                                have p1123_1 := h1123c.2.1
                                have p1123_2 := h1123c.2.2.1
                                have p1123_3 := h1123c.2.2.2
                                linarith only [h666, hlam, p1123_0]
                              · have p1123_0 := h1123c.1
                                have p1123_1 := h1123c.2.1
                                have p1123_2 := h1123c.2.2.1
                                have p1123_3 := h1123c.2.2.2
                                linarith only [h1113, hlam, p1123_0]
                              · have p1123_0 := h1123c.1
                                have p1123_1 := h1123c.2.1
                                have p1123_2 := h1123c.2.2.1
                                have p1123_3 := h1123c.2.2.2
                                linarith only [hc24, hlam, hphi, p1123_1, u2ehi2]
                              · have p1123_0 := h1123c.1
                                have p1123_1 := h1123c.2.1
                                have p1123_2 := h1123c.2.2.1
                                have p1123_3 := h1123c.2.2.2
                                linarith only [hlam, p1123_0]
                              · have p1123_0 := h1123c.1
                                have p1123_1 := h1123c.2.1
                                have p1123_2 := h1123c.2.2.1
                                have p1123_3 := h1123c.2.2.2
                                linarith only [h0, h1113, h664, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1123_1, u2ehi4]
                              · have p1123_0 := h1123c.1
                                have p1123_1 := h1123c.2.1
                                have p1123_2 := h1123c.2.2.1
                                have p1123_3 := h1123c.2.2.2
                                linarith only [h667, hlam, p1123_0]
                              · have p1123_0 := h1123c.1
                                have p1123_1 := h1123c.2.1
                                have p1123_2 := h1123c.2.2.1
                                have p1123_3 := h1123c.2.2.2
                                linarith only [h1114, hlam, p1123_0]
                              · have p1123_0 := h1123c.1
                                have p1123_1 := h1123c.2.1
                                have p1123_2 := h1123c.2.2.1
                                have p1123_3 := h1123c.2.2.2
                                linarith only [h1120, hlam, p1123_1]
                              · have p1123_0 := h1123c.1
                                have p1123_1 := h1123c.2.1
                                have p1123_2 := h1123c.2.2.1
                                have p1123_3 := h1123c.2.2.2
                                linarith only [h1121, hlam, p1123_0]
                              · have p1123_0 := h1123c.1
                                have p1123_1 := h1123c.2.1
                                have p1123_2 := h1123c.2.2.1
                                have p1123_3 := h1123c.2.2.2
                                linarith only [hlam, p1123_0]
                            · linarith only [h1122, h665, h668, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                          · linarith only [h0, h1117, h1121, h664, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1212 | h1212
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1213 | h1213
                            · rcases h2bigk with h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c
                              · have p1214_0 := h1214c.1
                                have p1214_1 := h1214c.2.1
                                have p1214_2 := h1214c.2.2.1
                                have p1214_3 := h1214c.2.2.2
                                linarith only [hlam, p1214_0]
                              · have p1214_0 := h1214c.1
                                have p1214_1 := h1214c.2.1
                                have p1214_2 := h1214c.2.2.1
                                have p1214_3 := h1214c.2.2.2
                                linarith only [h0, hlam, p1214_1]
                              · have p1214_0 := h1214c.1
                                have p1214_1 := h1214c.2.1
                                have p1214_2 := h1214c.2.2.1
                                have p1214_3 := h1214c.2.2.2
                                rcases p1214_3 (m.d 0 2) (by simp) with h1217 | h1217
                                · rcases p1214_3 (m.d 1 2) (by simp) with h1218 | h1218
                                  · rcases p1214_3 (m.d 2 3) (by simp) with h1219 | h1219
                                    · linarith only [h1219, hlam, p1214_0]
                                    · rcases p1214_3 (m.d 2 4) (by simp) with h1221 | h1221
                                      · linarith only [h1221, h666, hlam]
                                      · linarith only [h1118, h1221, hlam]
                                  · linarith only [h1112, h1218, hlam]
                                · linarith only [h1217, hlam, p1214_0]
                              · have p1214_0 := h1214c.1
                                have p1214_1 := h1214c.2.1
                                have p1214_2 := h1214c.2.2.1
                                have p1214_3 := h1214c.2.2.2
                                rcases p1214_3 (m.d 0 2) (by simp) with h1226 | h1226
                                · rcases p1214_3 (m.d 1 2) (by simp) with h1227 | h1227
                                  · rcases p1214_3 (m.d 2 3) (by simp) with h1228 | h1228
                                    · linarith only [h1228, h665, hlam]
                                    · rcases p1214_3 (m.d 2 4) (by simp) with h1230 | h1230
                                      · linarith only [h1230, hlam, p1214_0]
                                      · rcases p1214_3 (m.d 2 5) (by simp) with h1232 | h1232
                                        · linarith only [h1232, h667, hlam]
                                        · rcases h4bigk with h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c
                                          · have p1234_0 := h1234c.1
                                            have p1234_1 := h1234c.2.1
                                            have p1234_2 := h1234c.2.2.1
                                            have p1234_3 := h1234c.2.2.2
                                            linarith only [hlam, p1234_0]
                                          · have p1234_0 := h1234c.1
                                            have p1234_1 := h1234c.2.1
                                            have p1234_2 := h1234c.2.2.1
                                            have p1234_3 := h1234c.2.2.2
                                            linarith only [h0, h1112, h1115, h664, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1234_1, u2ehi2]
                                          · have p1234_0 := h1234c.1
                                            have p1234_1 := h1234c.2.1
                                            have p1234_2 := h1234c.2.2.1
                                            have p1234_3 := h1234c.2.2.2
                                            linarith only [h0, h664, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1234_1, u2ehi3]
                                          · have p1234_0 := h1234c.1
                                            have p1234_1 := h1234c.2.1
                                            have p1234_2 := h1234c.2.2.1
                                            have p1234_3 := h1234c.2.2.2
                                            linarith only [h668, hlam, p1234_0]
                                          · have p1234_0 := h1234c.1
                                            have p1234_1 := h1234c.2.1
                                            have p1234_2 := h1234c.2.2.1
                                            have p1234_3 := h1234c.2.2.2
                                            rcases p1234_3 (m.d 0 4) (by simp) with h1239 | h1239
                                            · rcases p1234_3 (m.d 1 4) (by simp) with h1240 | h1240
                                              · linarith only [h1240, h664, hlam]
                                              · linarith only [h1117, h1240, hlam]
                                            · linarith only [h1239, hlam, p1234_0]
                                          · have p1234_0 := h1234c.1
                                            have p1234_1 := h1234c.2.1
                                            have p1234_2 := h1234c.2.2.1
                                            have p1234_3 := h1234c.2.2.2
                                            linarith only [h664, hlam, p1234_1]
                                          · have p1234_0 := h1234c.1
                                            have p1234_1 := h1234c.2.1
                                            have p1234_2 := h1234c.2.2.1
                                            have p1234_3 := h1234c.2.2.2
                                            linarith only [hlam, p1234_0]
                                          · have p1234_0 := h1234c.1
                                            have p1234_1 := h1234c.2.1
                                            have p1234_2 := h1234c.2.2.1
                                            have p1234_3 := h1234c.2.2.2
                                            linarith only [h0, h1120, h1212, h664, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1234_1, u2ehi2]
                                          · have p1234_0 := h1234c.1
                                            have p1234_1 := h1234c.2.1
                                            have p1234_2 := h1234c.2.2.1
                                            have p1234_3 := h1234c.2.2.2
                                            linarith only [h1115, hlam, p1234_1]
                                          · have p1234_0 := h1234c.1
                                            have p1234_1 := h1234c.2.1
                                            have p1234_2 := h1234c.2.2.1
                                            have p1234_3 := h1234c.2.2.2
                                            linarith only [h0, h664, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1234_1]
                                          · have p1234_0 := h1234c.1
                                            have p1234_1 := h1234c.2.1
                                            have p1234_2 := h1234c.2.2.1
                                            have p1234_3 := h1234c.2.2.2
                                            linarith only [h666, hlam, p1234_1]
                                          · have p1234_0 := h1234c.1
                                            have p1234_1 := h1234c.2.1
                                            have p1234_2 := h1234c.2.2.1
                                            have p1234_3 := h1234c.2.2.2
                                            linarith only [h1113, hlam, p1234_1]
                                          · have p1234_0 := h1234c.1
                                            have p1234_1 := h1234c.2.1
                                            have p1234_2 := h1234c.2.2.1
                                            have p1234_3 := h1234c.2.2.2
                                            linarith only [hlam, p1234_0]
                                          · have p1234_0 := h1234c.1
                                            have p1234_1 := h1234c.2.1
                                            have p1234_2 := h1234c.2.2.1
                                            have p1234_3 := h1234c.2.2.2
                                            linarith only [h1118, hlam, p1234_1]
                                          · have p1234_0 := h1234c.1
                                            have p1234_1 := h1234c.2.1
                                            have p1234_2 := h1234c.2.2.1
                                            have p1234_3 := h1234c.2.2.2
                                            linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1214_1, p1234_1]
                                          · have p1234_0 := h1234c.1
                                            have p1234_1 := h1234c.2.1
                                            have p1234_2 := h1234c.2.2.1
                                            have p1234_3 := h1234c.2.2.2
                                            linarith only [h666, hc34, hlam, hphi, ht23, p1234_1, u2ehi3]
                                          · have p1234_0 := h1234c.1
                                            have p1234_1 := h1234c.2.1
                                            have p1234_2 := h1234c.2.2.1
                                            have p1234_3 := h1234c.2.2.2
                                            linarith only [h1113, hc34, hlam, hphi, ht23, p1234_1, u2ehi3]
                                          · have p1234_0 := h1234c.1
                                            have p1234_1 := h1234c.2.1
                                            have p1234_2 := h1234c.2.2.1
                                            have p1234_3 := h1234c.2.2.2
                                            linarith only [hc34, hlam, hphi, ht23, p1234_1, u2ehi3]
                                          · have p1234_0 := h1234c.1
                                            have p1234_1 := h1234c.2.1
                                            have p1234_2 := h1234c.2.2.1
                                            have p1234_3 := h1234c.2.2.2
                                            linarith only [hlam, p1234_0]
                                          · have p1234_0 := h1234c.1
                                            have p1234_1 := h1234c.2.1
                                            have p1234_2 := h1234c.2.2.1
                                            have p1234_3 := h1234c.2.2.2
                                            rcases p1234_3 (m.d 0 4) (by simp) with h1258 | h1258
                                            · linarith only [h1258, h668, hlam]
                                            · linarith only [h1111, h1258, hlam]
                                          · have p1234_0 := h1234c.1
                                            have p1234_1 := h1234c.2.1
                                            have p1234_2 := h1234c.2.2.1
                                            have p1234_3 := h1234c.2.2.2
                                            linarith only [h1111, hlam, p1234_0]
                                          · have p1234_0 := h1234c.1
                                            have p1234_1 := h1234c.2.1
                                            have p1234_2 := h1234c.2.2.1
                                            have p1234_3 := h1234c.2.2.2
                                            linarith only [h1117, hlam, p1234_0]
                                          · have p1234_0 := h1234c.1
                                            have p1234_1 := h1234c.2.1
                                            have p1234_2 := h1234c.2.2.1
                                            have p1234_3 := h1234c.2.2.2
                                            linarith only [h1212, hlam, p1234_0]
                                          · have p1234_0 := h1234c.1
                                            have p1234_1 := h1234c.2.1
                                            have p1234_2 := h1234c.2.2.1
                                            have p1234_3 := h1234c.2.2.2
                                            linarith only [h1213, hlam, p1234_0]
                                          · have p1234_0 := h1234c.1
                                            have p1234_1 := h1234c.2.1
                                            have p1234_2 := h1234c.2.2.1
                                            have p1234_3 := h1234c.2.2.2
                                            linarith only [hlam, p1234_0]
                                  · linarith only [h1113, h1227, hlam]
                                · linarith only [h1226, hlam, p1214_0]
                              · have p1214_0 := h1214c.1
                                have p1214_1 := h1214c.2.1
                                have p1214_2 := h1214c.2.2.1
                                have p1214_3 := h1214c.2.2.2
                                rcases p1214_3 (m.d 0 2) (by simp) with h1268 | h1268
                                · rcases p1214_3 (m.d 1 2) (by simp) with h1269 | h1269
                                  · rcases p1214_3 (m.d 2 3) (by simp) with h1270 | h1270
                                    · linarith only [h1270, h665, hlam]
                                    · rcases p1214_3 (m.d 2 4) (by simp) with h1272 | h1272
                                      · linarith only [h1272, h666, hlam]
                                      · linarith only [h1212, h1272, hlam]
                                  · linarith only [h1114, h1269, hlam]
                                · linarith only [h1268, hlam, p1214_0]
                              · have p1214_0 := h1214c.1
                                have p1214_1 := h1214c.2.1
                                have p1214_2 := h1214c.2.2.1
                                have p1214_3 := h1214c.2.2.2
                                linarith only [h0, h1114, h1117, h1120, h664, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1214_1, u2ehi2]
                              · have p1214_0 := h1214c.1
                                have p1214_1 := h1214c.2.1
                                have p1214_2 := h1214c.2.2.1
                                have p1214_3 := h1214c.2.2.2
                                linarith only [hlam, p1214_0]
                              · have p1214_0 := h1214c.1
                                have p1214_1 := h1214c.2.1
                                have p1214_2 := h1214c.2.2.1
                                have p1214_3 := h1214c.2.2.2
                                rcases p1214_3 (m.d 0 2) (by simp) with h1279 | h1279
                                · linarith only [h0, h1279, hlam]
                                · linarith only [h1279, h665, hlam]
                              · have p1214_0 := h1214c.1
                                have p1214_1 := h1214c.2.1
                                have p1214_2 := h1214c.2.2.1
                                have p1214_3 := h1214c.2.2.2
                                rcases p1214_3 (m.d 0 2) (by simp) with h1282 | h1282
                                · linarith only [h0, h1282, hlam]
                                · linarith only [h1282, h666, hlam]
                              · have p1214_0 := h1214c.1
                                have p1214_1 := h1214c.2.1
                                have p1214_2 := h1214c.2.2.1
                                have p1214_3 := h1214c.2.2.2
                                rcases p1214_3 (m.d 0 2) (by simp) with h1285 | h1285
                                · linarith only [h0, h1285, hlam]
                                · linarith only [h1285, h667, hlam]
                              · have p1214_0 := h1214c.1
                                have p1214_1 := h1214c.2.1
                                have p1214_2 := h1214c.2.2.1
                                have p1214_3 := h1214c.2.2.2
                                linarith only [h665, hlam, p1214_0]
                              · have p1214_0 := h1214c.1
                                have p1214_1 := h1214c.2.1
                                have p1214_2 := h1214c.2.2.1
                                have p1214_3 := h1214c.2.2.2
                                linarith only [h1112, hlam, p1214_0]
                              · have p1214_0 := h1214c.1
                                have p1214_1 := h1214c.2.1
                                have p1214_2 := h1214c.2.2.1
                                have p1214_3 := h1214c.2.2.2
                                linarith only [hlam, p1214_0]
                              · have p1214_0 := h1214c.1
                                have p1214_1 := h1214c.2.1
                                have p1214_2 := h1214c.2.2.1
                                have p1214_3 := h1214c.2.2.2
                                linarith only [h1118, hlam, p1214_0]
                              · have p1214_0 := h1214c.1
                                have p1214_1 := h1214c.2.1
                                have p1214_2 := h1214c.2.2.1
                                have p1214_3 := h1214c.2.2.2
                                linarith only [h1120, hlam, p1214_0]
                              · have p1214_0 := h1214c.1
                                have p1214_1 := h1214c.2.1
                                have p1214_2 := h1214c.2.2.1
                                have p1214_3 := h1214c.2.2.2
                                linarith only [h666, hlam, p1214_0]
                              · have p1214_0 := h1214c.1
                                have p1214_1 := h1214c.2.1
                                have p1214_2 := h1214c.2.2.1
                                have p1214_3 := h1214c.2.2.2
                                linarith only [h1113, hlam, p1214_0]
                              · have p1214_0 := h1214c.1
                                have p1214_1 := h1214c.2.1
                                have p1214_2 := h1214c.2.2.1
                                have p1214_3 := h1214c.2.2.2
                                linarith only [hc24, hlam, hphi, p1214_1, u2ehi2]
                              · have p1214_0 := h1214c.1
                                have p1214_1 := h1214c.2.1
                                have p1214_2 := h1214c.2.2.1
                                have p1214_3 := h1214c.2.2.2
                                linarith only [hlam, p1214_0]
                              · have p1214_0 := h1214c.1
                                have p1214_1 := h1214c.2.1
                                have p1214_2 := h1214c.2.2.1
                                have p1214_3 := h1214c.2.2.2
                                linarith only [h0, h1113, h1120, h664, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1214_1, u2ehi2]
                              · have p1214_0 := h1214c.1
                                have p1214_1 := h1214c.2.1
                                have p1214_2 := h1214c.2.2.1
                                have p1214_3 := h1214c.2.2.2
                                linarith only [h667, hlam, p1214_0]
                              · have p1214_0 := h1214c.1
                                have p1214_1 := h1214c.2.1
                                have p1214_2 := h1214c.2.2.1
                                have p1214_3 := h1214c.2.2.2
                                linarith only [h1114, hlam, p1214_0]
                              · have p1214_0 := h1214c.1
                                have p1214_1 := h1214c.2.1
                                have p1214_2 := h1214c.2.2.1
                                have p1214_3 := h1214c.2.2.2
                                linarith only [hc25, hlam, hphi, p1214_1, u2ehi2]
                              · have p1214_0 := h1214c.1
                                have p1214_1 := h1214c.2.1
                                have p1214_2 := h1214c.2.2.1
                                have p1214_3 := h1214c.2.2.2
                                linarith only [h1212, hlam, p1214_0]
                              · have p1214_0 := h1214c.1
                                have p1214_1 := h1214c.2.1
                                have p1214_2 := h1214c.2.2.1
                                have p1214_3 := h1214c.2.2.2
                                linarith only [hlam, p1214_0]
                            · linarith only [h1213, h665, h668, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                          · linarith only [h0, h1117, h1212, h664, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h1111, h1113, h1117, h664, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                · linarith only [h0, h1113, h1114, h664, hc25, hlam, hphi, u2ehi3]
              · linarith only [h0, h1111, h1113, h664, h666, h667, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
            · linarith only [h0, h1111, h1112, h664, h667, hc23, hlam, hphi, u2ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1309 | h1309
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1310 | h1310
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1311 | h1311
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1312 | h1312
                  · linarith only [h0, h1312, h664, h665, h668, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1314 | h1314
                    · linarith only [h1111, h1314, h664, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1316 | h1316
                      · linarith only [h1316, h665, h668, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1318 | h1318
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1319 | h1319
                          · linarith only [h1111, h1309, h1312, h1318, h1319, h664, hc24, hlam, hphi, u2ehi4]
                          · linarith only [h1316, h1318, h1319, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1322 | h1322
                          · linarith only [h1111, h1322, h666, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1324 | h1324
                            · linarith only [h1111, h1309, h1312, h1324, h664, hc34, hlam, hphi, ht23, u2ehi2]
                            · linarith only [h1324, h665, h668, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                · linarith only [h0, h1311, h665, hc25, hlam, hphi, u2ehi2]
              · linarith only [h0, h1310, h665, hc24, hlam, hphi, u2ehi2]
            · linarith only [h0, h1309, h664, h665, h668, hlam]
      · linarith only [h665, h667, hc25, hlam, hphi, u2ehi2]
    · linarith only [h665, h666, hc24, hlam, hphi, u2ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1332 | h1332
    · linarith only [h1332, h665, hc23, hlam, hphi, u2ehi3]
    · linarith only [h0, h1332, h664, hlam]

end R2N4
