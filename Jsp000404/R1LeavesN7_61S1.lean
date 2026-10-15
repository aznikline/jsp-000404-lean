import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3258000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_R_M_IR_x1_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h328 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h460 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h563 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h632 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h633 | h633
  · rcases m.htr 0 2 5 (by decide) (by decide) with h634 | h634
    · rcases m.htr 0 3 4 (by decide) (by decide) with h635 | h635
      · rcases m.htr 0 3 5 (by decide) (by decide) with h636 | h636
        · rcases m.htr 0 4 5 (by decide) (by decide) with h637 | h637
          · rcases m.htr 1 2 3 (by decide) (by decide) with h638 | h638
            · rcases m.htr 1 2 4 (by decide) (by decide) with h639 | h639
              · rcases m.htr 1 2 5 (by decide) (by decide) with h640 | h640
                · rcases m.htr 1 3 4 (by decide) (by decide) with h641 | h641
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h642 | h642
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h643 | h643
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h644 | h644
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h645 | h645
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h646 | h646
                            · linarith only [h632, h643, h646, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · linarith only [h0, h632, h643, h645, h646, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h649 | h649
                            · linarith only [h645, h649, hc34, hlam, hphi, ht23, u2ehi3]
                            · rcases h0bigk with h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [hlam, p651_0]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [h0, hlam, p651_1]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [h328, hlam, p651_0]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [h460, hlam, p651_1]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [h563, hlam, p651_1]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                rcases p651_3 (m.d 0 1) (by simp) with h657 | h657
                                · linarith only [h0, h657, hlam]
                                · rcases p651_3 (m.d 0 2) (by simp) with h659 | h659
                                  · rcases p651_3 (m.d 0 3) (by simp) with h660 | h660
                                    · linarith only [h632, h660, hlam]
                                    · linarith only [h328, h660, hlam]
                                  · linarith only [h0, h659, hlam]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [hlam, p651_0]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [h0, h635, h637, h645, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p651_1, u2ehi3]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [h0, h637, h645, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p651_1, u2ehi3]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [h0, h637, h645, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p651_1, u2ehi3]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                rcases p651_3 (m.d 0 1) (by simp) with h668 | h668
                                · linarith only [h328, h668, hlam]
                                · rcases p651_3 (m.d 0 2) (by simp) with h670 | h670
                                  · rcases p651_3 (m.d 0 3) (by simp) with h671 | h671
                                    · rcases p651_3 (m.d 0 4) (by simp) with h672 | h672
                                      · linarith only [h635, h672, hlam]
                                      · linarith only [h460, h672, hlam]
                                    · linarith only [h328, h671, hlam]
                                  · linarith only [h0, h670, hlam]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [h632, hlam, p651_1]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [hlam, p651_0]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [h637, h645, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p651_1, u2ehi3]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [h328, h637, h638, h645, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p651_1, u2ehi3]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                rcases p651_3 (m.d 0 1) (by simp) with h681 | h681
                                · linarith only [h460, h681, hlam]
                                · rcases p651_3 (m.d 0 2) (by simp) with h683 | h683
                                  · rcases p651_3 (m.d 0 3) (by simp) with h684 | h684
                                    · rcases p651_3 (m.d 0 4) (by simp) with h685 | h685
                                      · rcases p651_3 (m.d 0 5) (by simp) with h686 | h686
                                        · linarith only [h637, h686, hlam]
                                        · linarith only [h563, h686, hlam]
                                      · linarith only [h460, h685, hlam]
                                    · linarith only [h328, h684, hlam]
                                  · linarith only [h0, h683, hlam]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [h633, hlam, p651_0]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [h635, hlam, p651_0]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [hlam, p651_0]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [h460, h637, h638, h641, h645, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p651_1, u2ehi3]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                rcases p651_3 (m.d 0 1) (by simp) with h696 | h696
                                · linarith only [h563, h696, hlam]
                                · rcases p651_3 (m.d 0 2) (by simp) with h698 | h698
                                  · rcases p651_3 (m.d 0 3) (by simp) with h699 | h699
                                    · rcases p651_3 (m.d 0 4) (by simp) with h700 | h700
                                      · rcases p651_3 (m.d 0 5) (by simp) with h701 | h701
                                        · rcases h0emax with h702 | h702 | h702 | h702 | h702
                                          · rcases h5bigk with h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c
                                            · have p703_0 := h703c.1
                                              have p703_1 := h703c.2.1
                                              have p703_2 := h703c.2.2.1
                                              have p703_3 := h703c.2.2.2
                                              linarith only [hlam, p703_0]
                                            · have p703_0 := h703c.1
                                              have p703_1 := h703c.2.1
                                              have p703_2 := h703c.2.2.1
                                              have p703_3 := h703c.2.2.2
                                              linarith only [h563, hlam, p703_1]
                                            · have p703_0 := h703c.1
                                              have p703_1 := h703c.2.1
                                              have p703_2 := h703c.2.2.1
                                              have p703_3 := h703c.2.2.2
                                              rcases p703_3 (m.d 0 5) (by simp) with h706 | h706
                                              · rcases p703_3 (m.d 1 5) (by simp) with h707 | h707
                                                · rcases p703_3 (m.d 2 5) (by simp) with h708 | h708
                                                  · linarith only [h634, h708, hlam]
                                                  · rcases p703_3 (m.d 3 5) (by simp) with h710 | h710
                                                    · linarith only [h636, h710, hlam]
                                                    · rcases p703_3 (m.d 4 5) (by simp) with h712 | h712
                                                      · linarith only [h637, h712, hlam]
                                                      · linarith only [h645, h712, hlam]
                                                · linarith only [h640, h707, hlam]
                                              · linarith only [h634, h706, hlam]
                                            · have p703_0 := h703c.1
                                              have p703_1 := h703c.2.1
                                              have p703_2 := h703c.2.2.1
                                              have p703_3 := h703c.2.2.2
                                              rcases p703_3 (m.d 0 5) (by simp) with h717 | h717
                                              · rcases p703_3 (m.d 1 5) (by simp) with h718 | h718
                                                · rcases p703_3 (m.d 2 5) (by simp) with h719 | h719
                                                  · linarith only [h634, h719, hlam]
                                                  · linarith only [h644, h719, hlam]
                                                · linarith only [h0, h563, h634, h644, h718, hc01, hc12, hlam, hphi, p651_1]
                                              · linarith only [h636, h717, hlam]
                                            · have p703_0 := h703c.1
                                              have p703_1 := h703c.2.1
                                              have p703_2 := h703c.2.2.1
                                              have p703_3 := h703c.2.2.2
                                              linarith only [h645, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p703_1, u2ehi3]
                                            · have p703_0 := h703c.1
                                              have p703_1 := h703c.2.1
                                              have p703_2 := h703c.2.2.1
                                              have p703_3 := h703c.2.2.2
                                              linarith only [hc01, hc15, hlam, hphi, p651_1, p703_1]
                                            · have p703_0 := h703c.1
                                              have p703_1 := h703c.2.1
                                              have p703_2 := h703c.2.2.1
                                              have p703_3 := h703c.2.2.2
                                              linarith only [hlam, p703_0]
                                            · have p703_0 := h703c.1
                                              have p703_1 := h703c.2.1
                                              have p703_2 := h703c.2.2.1
                                              have p703_3 := h703c.2.2.2
                                              rcases p703_3 (m.d 0 5) (by simp) with h727 | h727
                                              · linarith only [h563, h727, hlam]
                                              · linarith only [h634, h727, hlam]
                                            · have p703_0 := h703c.1
                                              have p703_1 := h703c.2.1
                                              have p703_2 := h703c.2.2.1
                                              have p703_3 := h703c.2.2.2
                                              rcases p703_3 (m.d 0 5) (by simp) with h730 | h730
                                              · linarith only [h563, h730, hlam]
                                              · linarith only [h636, h730, hlam]
                                            · have p703_0 := h703c.1
                                              have p703_1 := h703c.2.1
                                              have p703_2 := h703c.2.2.1
                                              have p703_3 := h703c.2.2.2
                                              linarith only [h638, h641, h642, h645, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p703_1, u2ehi3]
                                            · have p703_0 := h703c.1
                                              have p703_1 := h703c.2.1
                                              have p703_2 := h703c.2.2.1
                                              have p703_3 := h703c.2.2.2
                                              linarith only [h634, hlam, p703_1]
                                            · have p703_0 := h703c.1
                                              have p703_1 := h703c.2.1
                                              have p703_2 := h703c.2.2.1
                                              have p703_3 := h703c.2.2.2
                                              linarith only [h640, hlam, p703_1]
                                            · have p703_0 := h703c.1
                                              have p703_1 := h703c.2.1
                                              have p703_2 := h703c.2.2.1
                                              have p703_3 := h703c.2.2.2
                                              linarith only [hlam, p703_0]
                                            · have p703_0 := h703c.1
                                              have p703_1 := h703c.2.1
                                              have p703_2 := h703c.2.2.1
                                              have p703_3 := h703c.2.2.2
                                              linarith only [h0, h634, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p703_1, u3ehi4]
                                            · have p703_0 := h703c.1
                                              have p703_1 := h703c.2.1
                                              have p703_2 := h703c.2.2.1
                                              have p703_3 := h703c.2.2.2
                                              linarith only [h645, hlam, p703_1]
                                            · have p703_0 := h703c.1
                                              have p703_1 := h703c.2.1
                                              have p703_2 := h703c.2.2.1
                                              have p703_3 := h703c.2.2.2
                                              linarith only [h636, hlam, p703_0]
                                            · have p703_0 := h703c.1
                                              have p703_1 := h703c.2.1
                                              have p703_2 := h703c.2.2.1
                                              have p703_3 := h703c.2.2.2
                                              linarith only [h563, hc01, hc35, hlam, hphi, ht12, ht23, p703_1]
                                            · have p703_0 := h703c.1
                                              have p703_1 := h703c.2.1
                                              have p703_2 := h703c.2.2.1
                                              have p703_3 := h703c.2.2.2
                                              linarith only [h644, hlam, p703_0]
                                            · have p703_0 := h703c.1
                                              have p703_1 := h703c.2.1
                                              have p703_2 := h703c.2.2.1
                                              have p703_3 := h703c.2.2.2
                                              linarith only [hlam, p703_0]
                                            · have p703_0 := h703c.1
                                              have p703_1 := h703c.2.1
                                              have p703_2 := h703c.2.2.1
                                              have p703_3 := h703c.2.2.2
                                              linarith only [h649, hlam, p703_1]
                                            · have p703_0 := h703c.1
                                              have p703_1 := h703c.2.1
                                              have p703_2 := h703c.2.2.1
                                              have p703_3 := h703c.2.2.2
                                              linarith only [h637, hlam, p703_0]
                                            · have p703_0 := h703c.1
                                              have p703_1 := h703c.2.1
                                              have p703_2 := h703c.2.2.1
                                              have p703_3 := h703c.2.2.2
                                              linarith only [h642, hlam, p703_0]
                                            · have p703_0 := h703c.1
                                              have p703_1 := h703c.2.1
                                              have p703_2 := h703c.2.2.1
                                              have p703_3 := h703c.2.2.2
                                              linarith only [h460, h637, h638, h641, hc12, hlam, hphi, ht01, ht0b, ht5b, p703_1, u5ehi2]
                                            · have p703_0 := h703c.1
                                              have p703_1 := h703c.2.1
                                              have p703_2 := h703c.2.2.1
                                              have p703_3 := h703c.2.2.2
                                              linarith only [h460, h637, h638, h641, hc12, hlam, hphi, ht01, ht0b, ht5b, p703_1, u5ehi3]
                                            · have p703_0 := h703c.1
                                              have p703_1 := h703c.2.1
                                              have p703_2 := h703c.2.2.1
                                              have p703_3 := h703c.2.2.2
                                              linarith only [hlam, p703_0]
                                          · linarith only [h632, h702, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                                          · linarith only [h632, h644, h702, hlam, hphi, ht0b, ht5b, u5ehi3]
                                          · linarith only [h637, h702, hlam, hphi, ht0b, ht5b, u5ehi4]
                                          · linarith only [h702, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p651_1]
                                        · linarith only [h563, h701, hlam]
                                      · linarith only [h460, h700, hlam]
                                    · linarith only [h328, h699, hlam]
                                  · linarith only [h0, h698, hlam]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [h634, hlam, p651_1]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [h636, hlam, p651_0]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [h637, hlam, p651_1]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [hlam, p651_0]
                        · linarith only [h0, h632, h636, h643, h644, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h762 | h762
                        · linarith only [h0, h632, h635, h643, h762, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h764 | h764
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h765 | h765
                            · rcases h0bigk with h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [hlam, p766_0]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [h0, hlam, p766_1]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [h328, hlam, p766_0]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [h460, hlam, p766_1]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [h563, hlam, p766_1]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                rcases p766_3 (m.d 0 1) (by simp) with h772 | h772
                                · linarith only [h0, h772, hlam]
                                · rcases p766_3 (m.d 0 2) (by simp) with h774 | h774
                                  · rcases p766_3 (m.d 0 3) (by simp) with h775 | h775
                                    · linarith only [h632, h775, hlam]
                                    · linarith only [h328, h775, hlam]
                                  · linarith only [h0, h774, hlam]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [hlam, p766_0]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [h0, h635, h762, h765, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p766_1, u2ehi2]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [h0, h633, h764, hc12, hlam, hphi, ht01, ht0b, ht5b, p766_1, u5ehi4]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [h0, h636, h762, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p766_1, u2ehi2]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                rcases p766_3 (m.d 0 1) (by simp) with h783 | h783
                                · linarith only [h328, h783, hlam]
                                · rcases p766_3 (m.d 0 2) (by simp) with h785 | h785
                                  · rcases p766_3 (m.d 0 3) (by simp) with h786 | h786
                                    · rcases p766_3 (m.d 0 4) (by simp) with h787 | h787
                                      · linarith only [h635, h787, hlam]
                                      · linarith only [h460, h787, hlam]
                                    · linarith only [h328, h786, hlam]
                                  · linarith only [h0, h785, hlam]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [h632, hlam, p766_1]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [hlam, p766_0]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [h635, h762, h765, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p766_1, u2ehi2]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [h328, h636, h638, h762, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p766_1, u2ehi2]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                rcases p766_3 (m.d 0 1) (by simp) with h796 | h796
                                · linarith only [h460, h796, hlam]
                                · rcases p766_3 (m.d 0 2) (by simp) with h798 | h798
                                  · rcases p766_3 (m.d 0 3) (by simp) with h799 | h799
                                    · rcases p766_3 (m.d 0 4) (by simp) with h800 | h800
                                      · rcases p766_3 (m.d 0 5) (by simp) with h801 | h801
                                        · linarith only [h637, h801, hlam]
                                        · linarith only [h563, h801, hlam]
                                      · linarith only [h460, h800, hlam]
                                    · linarith only [h328, h799, hlam]
                                  · linarith only [h0, h798, hlam]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [h633, hlam, p766_0]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [h635, hlam, p766_0]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [hlam, p766_0]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [h636, h762, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p766_1, u2ehi2]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                rcases p766_3 (m.d 0 1) (by simp) with h811 | h811
                                · linarith only [h563, h811, hlam]
                                · rcases p766_3 (m.d 0 2) (by simp) with h813 | h813
                                  · rcases p766_3 (m.d 0 3) (by simp) with h814 | h814
                                    · rcases p766_3 (m.d 0 4) (by simp) with h815 | h815
                                      · rcases p766_3 (m.d 0 5) (by simp) with h816 | h816
                                        · rcases h0emax with h817 | h817 | h817 | h817 | h817
                                          · rcases h5bigk with h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c
                                            · have p818_0 := h818c.1
                                              have p818_1 := h818c.2.1
                                              have p818_2 := h818c.2.2.1
                                              have p818_3 := h818c.2.2.2
                                              linarith only [hlam, p818_0]
                                            · have p818_0 := h818c.1
                                              have p818_1 := h818c.2.1
                                              have p818_2 := h818c.2.2.1
                                              have p818_3 := h818c.2.2.2
                                              linarith only [h563, hlam, p818_1]
                                            · have p818_0 := h818c.1
                                              have p818_1 := h818c.2.1
                                              have p818_2 := h818c.2.2.1
                                              have p818_3 := h818c.2.2.2
                                              rcases p818_3 (m.d 0 5) (by simp) with h821 | h821
                                              · rcases p818_3 (m.d 1 5) (by simp) with h822 | h822
                                                · rcases p818_3 (m.d 2 5) (by simp) with h823 | h823
                                                  · linarith only [h634, h823, hlam]
                                                  · rcases p818_3 (m.d 3 5) (by simp) with h825 | h825
                                                    · linarith only [h636, h825, hlam]
                                                    · linarith only [h762, h825, hlam]
                                                · linarith only [h640, h822, hlam]
                                              · linarith only [h634, h821, hlam]
                                            · have p818_0 := h818c.1
                                              have p818_1 := h818c.2.1
                                              have p818_2 := h818c.2.2.1
                                              have p818_3 := h818c.2.2.2
                                              linarith only [h762, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p818_1, u2ehi2]
                                            · have p818_0 := h818c.1
                                              have p818_1 := h818c.2.1
                                              have p818_2 := h818c.2.2.1
                                              have p818_3 := h818c.2.2.2
                                              rcases p818_3 (m.d 0 5) (by simp) with h831 | h831
                                              · rcases p818_3 (m.d 1 5) (by simp) with h832 | h832
                                                · rcases p818_3 (m.d 2 5) (by simp) with h833 | h833
                                                  · linarith only [h634, h833, hlam]
                                                  · linarith only [h764, h833, hlam]
                                                · linarith only [h642, h832, hlam]
                                              · linarith only [h637, h831, hlam]
                                            · have p818_0 := h818c.1
                                              have p818_1 := h818c.2.1
                                              have p818_2 := h818c.2.2.1
                                              have p818_3 := h818c.2.2.2
                                              linarith only [h638, h641, h642, hc01, hc12, hlam, hphi, p766_1, p818_1]
                                            · have p818_0 := h818c.1
                                              have p818_1 := h818c.2.1
                                              have p818_2 := h818c.2.2.1
                                              have p818_3 := h818c.2.2.2
                                              linarith only [hlam, p818_0]
                                            · have p818_0 := h818c.1
                                              have p818_1 := h818c.2.1
                                              have p818_2 := h818c.2.2.1
                                              have p818_3 := h818c.2.2.2
                                              rcases p818_3 (m.d 0 5) (by simp) with h840 | h840
                                              · linarith only [h563, h840, hlam]
                                              · linarith only [h634, h840, hlam]
                                            · have p818_0 := h818c.1
                                              have p818_1 := h818c.2.1
                                              have p818_2 := h818c.2.2.1
                                              have p818_3 := h818c.2.2.2
                                              linarith only [h638, h641, h642, h762, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p818_1, u2ehi2]
                                            · have p818_0 := h818c.1
                                              have p818_1 := h818c.2.1
                                              have p818_2 := h818c.2.2.1
                                              have p818_3 := h818c.2.2.2
                                              rcases p818_3 (m.d 0 5) (by simp) with h844 | h844
                                              · linarith only [h563, h844, hlam]
                                              · linarith only [h637, h844, hlam]
                                            · have p818_0 := h818c.1
                                              have p818_1 := h818c.2.1
                                              have p818_2 := h818c.2.2.1
                                              have p818_3 := h818c.2.2.2
                                              linarith only [h634, hlam, p818_1]
                                            · have p818_0 := h818c.1
                                              have p818_1 := h818c.2.1
                                              have p818_2 := h818c.2.2.1
                                              have p818_3 := h818c.2.2.2
                                              linarith only [h640, hlam, p818_1]
                                            · have p818_0 := h818c.1
                                              have p818_1 := h818c.2.1
                                              have p818_2 := h818c.2.2.1
                                              have p818_3 := h818c.2.2.2
                                              linarith only [hlam, p818_0]
                                            · have p818_0 := h818c.1
                                              have p818_1 := h818c.2.1
                                              have p818_2 := h818c.2.2.1
                                              have p818_3 := h818c.2.2.2
                                              linarith only [h762, hlam, p818_1]
                                            · have p818_0 := h818c.1
                                              have p818_1 := h818c.2.1
                                              have p818_2 := h818c.2.2.1
                                              have p818_3 := h818c.2.2.2
                                              linarith only [h0, h634, hc12, hlam, hphi, ht01, ht0b, ht5b, p818_1, u5ehi4]
                                            · have p818_0 := h818c.1
                                              have p818_1 := h818c.2.1
                                              have p818_2 := h818c.2.2.1
                                              have p818_3 := h818c.2.2.2
                                              linarith only [h636, hlam, p818_0]
                                            · have p818_0 := h818c.1
                                              have p818_1 := h818c.2.1
                                              have p818_2 := h818c.2.2.1
                                              have p818_3 := h818c.2.2.2
                                              linarith only [h563, h765, hc01, hc34, hlam, hphi, ht12, ht23, p818_1]
                                            · have p818_0 := h818c.1
                                              have p818_1 := h818c.2.1
                                              have p818_2 := h818c.2.2.1
                                              have p818_3 := h818c.2.2.2
                                              linarith only [h328, h635, h638, h765, hc12, hlam, hphi, ht01, ht0b, ht5b, p818_1, u5ehi2]
                                            · have p818_0 := h818c.1
                                              have p818_1 := h818c.2.1
                                              have p818_2 := h818c.2.2.1
                                              have p818_3 := h818c.2.2.2
                                              linarith only [hlam, p818_0]
                                            · have p818_0 := h818c.1
                                              have p818_1 := h818c.2.1
                                              have p818_2 := h818c.2.2.1
                                              have p818_3 := h818c.2.2.2
                                              linarith only [h328, h635, h638, h765, hc12, hlam, hphi, ht01, ht0b, ht5b, p818_1, u5ehi4]
                                            · have p818_0 := h818c.1
                                              have p818_1 := h818c.2.1
                                              have p818_2 := h818c.2.2.1
                                              have p818_3 := h818c.2.2.2
                                              linarith only [h637, hlam, p818_0]
                                            · have p818_0 := h818c.1
                                              have p818_1 := h818c.2.1
                                              have p818_2 := h818c.2.2.1
                                              have p818_3 := h818c.2.2.2
                                              linarith only [h642, hlam, p818_0]
                                            · have p818_0 := h818c.1
                                              have p818_1 := h818c.2.1
                                              have p818_2 := h818c.2.2.1
                                              have p818_3 := h818c.2.2.2
                                              linarith only [h764, hlam, p818_0]
                                            · have p818_0 := h818c.1
                                              have p818_1 := h818c.2.1
                                              have p818_2 := h818c.2.2.1
                                              have p818_3 := h818c.2.2.2
                                              linarith only [h765, hlam, p818_0]
                                            · have p818_0 := h818c.1
                                              have p818_1 := h818c.2.1
                                              have p818_2 := h818c.2.2.1
                                              have p818_3 := h818c.2.2.2
                                              linarith only [hlam, p818_0]
                                          · linarith only [h632, h817, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                          · linarith only [h635, h765, h817, hlam, hphi, ht0b, ht5b, u5ehi3]
                                          · linarith only [h633, h764, h817, hlam, hphi, ht0b, ht5b, u5ehi4]
                                          · linarith only [h817, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p766_1]
                                        · linarith only [h563, h816, hlam]
                                      · linarith only [h460, h815, hlam]
                                    · linarith only [h328, h814, hlam]
                                  · linarith only [h0, h813, hlam]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [h634, hlam, p766_1]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [h636, hlam, p766_0]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [h637, hlam, p766_1]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [hlam, p766_0]
                            · linarith only [h0, h633, h764, h765, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h875 | h875
                            · linarith only [h328, h635, h638, h643, h764, h875, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · linarith only [h460, h637, h638, h641, h643, h875, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h460, h637, h642, hlam]
                  · linarith only [h328, h635, h641, hlam]
                · linarith only [h0, h632, h640, hc25, hlam, hphi, u2ehi2]
              · linarith only [h0, h633, h639, hlam]
            · linarith only [h0, h632, h638, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h883 | h883
            · rcases m.htr 1 2 4 (by decide) (by decide) with h884 | h884
              · rcases m.htr 1 2 5 (by decide) (by decide) with h885 | h885
                · rcases m.htr 1 3 4 (by decide) (by decide) with h886 | h886
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h887 | h887
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h888 | h888
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h889 | h889
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h890 | h890
                          · linarith only [h633, h637, h890, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h892 | h892
                            · linarith only [h632, h633, h637, h888, h892, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · rcases h0bigk with h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c
                              · have p894_0 := h894c.1
                                have p894_1 := h894c.2.1
                                have p894_2 := h894c.2.2.1
                                have p894_3 := h894c.2.2.2
                                linarith only [hlam, p894_0]
                              · have p894_0 := h894c.1
                                have p894_1 := h894c.2.1
                                have p894_2 := h894c.2.2.1
                                have p894_3 := h894c.2.2.2
                                linarith only [h0, hlam, p894_1]
                              · have p894_0 := h894c.1
                                have p894_1 := h894c.2.1
                                have p894_2 := h894c.2.2.1
                                have p894_3 := h894c.2.2.2
                                linarith only [h328, hlam, p894_0]
                              · have p894_0 := h894c.1
                                have p894_1 := h894c.2.1
                                have p894_2 := h894c.2.2.1
                                have p894_3 := h894c.2.2.2
                                linarith only [h460, hlam, p894_1]
                              · have p894_0 := h894c.1
                                have p894_1 := h894c.2.1
                                have p894_2 := h894c.2.2.1
                                have p894_3 := h894c.2.2.2
                                linarith only [h563, hlam, p894_1]
                              · have p894_0 := h894c.1
                                have p894_1 := h894c.2.1
                                have p894_2 := h894c.2.2.1
                                have p894_3 := h894c.2.2.2
                                rcases p894_3 (m.d 0 1) (by simp) with h900 | h900
                                · linarith only [h0, h900, hlam]
                                · rcases p894_3 (m.d 0 2) (by simp) with h902 | h902
                                  · rcases p894_3 (m.d 0 3) (by simp) with h903 | h903
                                    · linarith only [h632, h903, hlam]
                                    · linarith only [h328, h903, hlam]
                                  · linarith only [h0, h902, hlam]
                              · have p894_0 := h894c.1
                                have p894_1 := h894c.2.1
                                have p894_2 := h894c.2.2.1
                                have p894_3 := h894c.2.2.2
                                linarith only [hlam, p894_0]
                              · have p894_0 := h894c.1
                                have p894_1 := h894c.2.1
                                have p894_2 := h894c.2.2.1
                                have p894_3 := h894c.2.2.2
                                linarith only [h0, h632, h889, hc12, hlam, hphi, ht01, ht0b, ht5b, p894_1, u5ehi3]
                              · have p894_0 := h894c.1
                                have p894_1 := h894c.2.1
                                have p894_2 := h894c.2.2.1
                                have p894_3 := h894c.2.2.2
                                rcases p894_3 (m.d 0 1) (by simp) with h909 | h909
                                · linarith only [h0, h909, hlam]
                                · rcases p894_3 (m.d 0 2) (by simp) with h911 | h911
                                  · rcases p894_3 (m.d 0 3) (by simp) with h912 | h912
                                    · linarith only [h632, h912, hlam]
                                    · linarith only [h635, h912, hlam]
                                  · linarith only [h633, h911, hlam]
                              · have p894_0 := h894c.1
                                have p894_1 := h894c.2.1
                                have p894_2 := h894c.2.2.1
                                have p894_3 := h894c.2.2.2
                                rcases p894_3 (m.d 0 1) (by simp) with h916 | h916
                                · linarith only [h0, h916, hlam]
                                · rcases p894_3 (m.d 0 2) (by simp) with h918 | h918
                                  · rcases p894_3 (m.d 0 3) (by simp) with h919 | h919
                                    · linarith only [h632, h919, hlam]
                                    · linarith only [h636, h919, hlam]
                                  · linarith only [h634, h918, hlam]
                              · have p894_0 := h894c.1
                                have p894_1 := h894c.2.1
                                have p894_2 := h894c.2.2.1
                                have p894_3 := h894c.2.2.2
                                rcases p894_3 (m.d 0 1) (by simp) with h923 | h923
                                · linarith only [h328, h923, hlam]
                                · rcases p894_3 (m.d 0 2) (by simp) with h925 | h925
                                  · rcases p894_3 (m.d 0 3) (by simp) with h926 | h926
                                    · rcases p894_3 (m.d 0 4) (by simp) with h927 | h927
                                      · linarith only [h635, h927, hlam]
                                      · linarith only [h460, h927, hlam]
                                    · linarith only [h328, h926, hlam]
                                  · linarith only [h0, h925, hlam]
                              · have p894_0 := h894c.1
                                have p894_1 := h894c.2.1
                                have p894_2 := h894c.2.2.1
                                have p894_3 := h894c.2.2.2
                                linarith only [h632, hlam, p894_1]
                              · have p894_0 := h894c.1
                                have p894_1 := h894c.2.1
                                have p894_2 := h894c.2.2.1
                                have p894_3 := h894c.2.2.2
                                linarith only [hlam, p894_0]
                              · have p894_0 := h894c.1
                                have p894_1 := h894c.2.1
                                have p894_2 := h894c.2.2.1
                                have p894_3 := h894c.2.2.2
                                rcases p894_3 (m.d 0 1) (by simp) with h934 | h934
                                · linarith only [h328, h934, hlam]
                                · rcases p894_3 (m.d 0 2) (by simp) with h936 | h936
                                  · rcases p894_3 (m.d 0 3) (by simp) with h937 | h937
                                    · rcases p894_3 (m.d 0 4) (by simp) with h938 | h938
                                      · linarith only [h635, h938, hlam]
                                      · rcases p894_3 (m.d 0 5) (by simp) with h940 | h940
                                        · linarith only [h636, h940, hlam]
                                        · linarith only [h637, h940, hlam]
                                    · linarith only [h635, h937, hlam]
                                  · linarith only [h633, h936, hlam]
                              · have p894_0 := h894c.1
                                have p894_1 := h894c.2.1
                                have p894_2 := h894c.2.2.1
                                have p894_3 := h894c.2.2.2
                                rcases p894_3 (m.d 0 1) (by simp) with h945 | h945
                                · linarith only [h328, h945, hlam]
                                · rcases p894_3 (m.d 0 2) (by simp) with h947 | h947
                                  · rcases p894_3 (m.d 0 3) (by simp) with h948 | h948
                                    · rcases p894_3 (m.d 0 4) (by simp) with h949 | h949
                                      · linarith only [h635, h949, hlam]
                                      · rcases p894_3 (m.d 0 5) (by simp) with h951 | h951
                                        · linarith only [h636, h951, hlam]
                                        · rcases h0emax with h953 | h953 | h953 | h953 | h953
                                          · rcases h5bigk with h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c
                                            · have p954_0 := h954c.1
                                              have p954_1 := h954c.2.1
                                              have p954_2 := h954c.2.2.1
                                              have p954_3 := h954c.2.2.2
                                              linarith only [hlam, p954_0]
                                            · have p954_0 := h954c.1
                                              have p954_1 := h954c.2.1
                                              have p954_2 := h954c.2.2.1
                                              have p954_3 := h954c.2.2.2
                                              linarith only [h563, hlam, p954_1]
                                            · have p954_0 := h954c.1
                                              have p954_1 := h954c.2.1
                                              have p954_2 := h954c.2.2.1
                                              have p954_3 := h954c.2.2.2
                                              linarith only [h0, h632, hc12, hlam, hphi, ht01, ht0b, ht5b, p894_1, p954_1, u5ehi2]
                                            · have p954_0 := h954c.1
                                              have p954_1 := h954c.2.1
                                              have p954_2 := h954c.2.2.1
                                              have p954_3 := h954c.2.2.2
                                              linarith only [h0, h632, h892, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p894_1, p954_1, u3ehi3]
                                            · have p954_0 := h954c.1
                                              have p954_1 := h954c.2.1
                                              have p954_2 := h954c.2.2.1
                                              have p954_3 := h954c.2.2.2
                                              linarith only [h637, hlam, p954_1]
                                            · have p954_0 := h954c.1
                                              have p954_1 := h954c.2.1
                                              have p954_2 := h954c.2.2.1
                                              have p954_3 := h954c.2.2.2
                                              rcases p954_3 (m.d 0 5) (by simp) with h960 | h960
                                              · linarith only [h563, h960, hlam]
                                              · rcases p954_3 (m.d 1 5) (by simp) with h962 | h962
                                                · rcases p954_3 (m.d 2 5) (by simp) with h963 | h963
                                                  · linarith only [h885, h963, hlam]
                                                  · rcases p954_3 (m.d 3 5) (by simp) with h965 | h965
                                                    · linarith only [h889, h965, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p954_1, u5ehi0]
                                                    · rcases p954_3 (m.d 4 5) (by simp) with h967 | h967
                                                      · linarith only [h887, h967, hlam]
                                                      · linarith only [h637, h967, hlam]
                                                · linarith only [h563, h962, hlam]
                                            · have p954_0 := h954c.1
                                              have p954_1 := h954c.2.1
                                              have p954_2 := h954c.2.2.1
                                              have p954_3 := h954c.2.2.2
                                              linarith only [hlam, p954_0]
                                            · have p954_0 := h954c.1
                                              have p954_1 := h954c.2.1
                                              have p954_2 := h954c.2.2.1
                                              have p954_3 := h954c.2.2.2
                                              rcases p954_3 (m.d 0 5) (by simp) with h972 | h972
                                              · linarith only [h563, h972, hlam]
                                              · linarith only [h634, h972, hlam]
                                            · have p954_0 := h954c.1
                                              have p954_1 := h954c.2.1
                                              have p954_2 := h954c.2.2.1
                                              have p954_3 := h954c.2.2.2
                                              rcases p954_3 (m.d 0 5) (by simp) with h975 | h975
                                              · linarith only [h563, h975, hlam]
                                              · linarith only [h636, h975, hlam]
                                            · have p954_0 := h954c.1
                                              have p954_1 := h954c.2.1
                                              have p954_2 := h954c.2.2.1
                                              have p954_3 := h954c.2.2.2
                                              linarith only [h633, h637, h883, h886, h887, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p954_1, u2ehi3]
                                            · have p954_0 := h954c.1
                                              have p954_1 := h954c.2.1
                                              have p954_2 := h954c.2.2.1
                                              have p954_3 := h954c.2.2.2
                                              linarith only [h634, hlam, p954_1]
                                            · have p954_0 := h954c.1
                                              have p954_1 := h954c.2.1
                                              have p954_2 := h954c.2.2.1
                                              have p954_3 := h954c.2.2.2
                                              linarith only [h885, hlam, p954_1]
                                            · have p954_0 := h954c.1
                                              have p954_1 := h954c.2.1
                                              have p954_2 := h954c.2.2.1
                                              have p954_3 := h954c.2.2.2
                                              linarith only [hlam, p954_0]
                                            · have p954_0 := h954c.1
                                              have p954_1 := h954c.2.1
                                              have p954_2 := h954c.2.2.1
                                              have p954_3 := h954c.2.2.2
                                              linarith only [h632, h634, hc02, hlam, hphi, ht0b, ht5b, p894_1, p954_1, u5ehi3]
                                            · have p954_0 := h954c.1
                                              have p954_1 := h954c.2.1
                                              have p954_2 := h954c.2.2.1
                                              have p954_3 := h954c.2.2.2
                                              linarith only [h890, hlam, p954_1]
                                            · have p954_0 := h954c.1
                                              have p954_1 := h954c.2.1
                                              have p954_2 := h954c.2.2.1
                                              have p954_3 := h954c.2.2.2
                                              linarith only [h636, hlam, p954_0]
                                            · have p954_0 := h954c.1
                                              have p954_1 := h954c.2.1
                                              have p954_2 := h954c.2.2.1
                                              have p954_3 := h954c.2.2.2
                                              linarith only [h563, hc01, hc35, hlam, hphi, ht12, ht23, p954_1]
                                            · have p954_0 := h954c.1
                                              have p954_1 := h954c.2.1
                                              have p954_2 := h954c.2.2.1
                                              have p954_3 := h954c.2.2.2
                                              linarith only [h889, hlam, p954_0]
                                            · have p954_0 := h954c.1
                                              have p954_1 := h954c.2.1
                                              have p954_2 := h954c.2.2.1
                                              have p954_3 := h954c.2.2.2
                                              linarith only [hlam, p954_0]
                                            · have p954_0 := h954c.1
                                              have p954_1 := h954c.2.1
                                              have p954_2 := h954c.2.2.1
                                              have p954_3 := h954c.2.2.2
                                              linarith only [h892, hlam, p954_1]
                                            · have p954_0 := h954c.1
                                              have p954_1 := h954c.2.1
                                              have p954_2 := h954c.2.2.1
                                              have p954_3 := h954c.2.2.2
                                              linarith only [h634, hc45, hlam, hphi, ht23, ht34, p954_1, u2ehi4]
                                            · have p954_0 := h954c.1
                                              have p954_1 := h954c.2.1
                                              have p954_2 := h954c.2.2.1
                                              have p954_3 := h954c.2.2.2
                                              linarith only [h887, hlam, p954_0]
                                            · have p954_0 := h954c.1
                                              have p954_1 := h954c.2.1
                                              have p954_2 := h954c.2.2.1
                                              have p954_3 := h954c.2.2.2
                                              linarith only [h883, h886, h887, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p954_1, u2ehi4]
                                            · have p954_0 := h954c.1
                                              have p954_1 := h954c.2.1
                                              have p954_2 := h954c.2.2.1
                                              have p954_3 := h954c.2.2.2
                                              linarith only [h883, h886, h887, hc12, hlam, hphi, ht01, ht0b, ht5b, p954_1, u5ehi3]
                                            · have p954_0 := h954c.1
                                              have p954_1 := h954c.2.1
                                              have p954_2 := h954c.2.2.1
                                              have p954_3 := h954c.2.2.2
                                              linarith only [hlam, p954_0]
                                          · linarith only [h632, h953, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                                          · linarith only [h633, h637, h953, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p894_1, u2ehi3]
                                          · rcases h5bigk with h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c
                                            · have p996_0 := h996c.1
                                              have p996_1 := h996c.2.1
                                              have p996_2 := h996c.2.2.1
                                              have p996_3 := h996c.2.2.2
                                              linarith only [hlam, p996_0]
                                            · have p996_0 := h996c.1
                                              have p996_1 := h996c.2.1
                                              have p996_2 := h996c.2.2.1
                                              have p996_3 := h996c.2.2.2
                                              linarith only [h563, hlam, p996_1]
                                            · have p996_0 := h996c.1
                                              have p996_1 := h996c.2.1
                                              have p996_2 := h996c.2.2.1
                                              have p996_3 := h996c.2.2.2
                                              linarith only [h632, h890, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p894_1, p996_1, u2ehi3]
                                            · have p996_0 := h996c.1
                                              have p996_1 := h996c.2.1
                                              have p996_2 := h996c.2.2.1
                                              have p996_3 := h996c.2.2.2
                                              linarith only [h0, h632, h892, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p894_1, p996_1, u3ehi3]
                                            · have p996_0 := h996c.1
                                              have p996_1 := h996c.2.1
                                              have p996_2 := h996c.2.2.1
                                              have p996_3 := h996c.2.2.2
                                              linarith only [h637, hlam, p996_1]
                                            · have p996_0 := h996c.1
                                              have p996_1 := h996c.2.1
                                              have p996_2 := h996c.2.2.1
                                              have p996_3 := h996c.2.2.2
                                              rcases p996_3 (m.d 0 5) (by simp) with h1002 | h1002
                                              · linarith only [h1002, h563, hlam]
                                              · rcases p996_3 (m.d 1 5) (by simp) with h1004 | h1004
                                                · rcases p996_3 (m.d 2 5) (by simp) with h1005 | h1005
                                                  · linarith only [h1005, h885, hlam]
                                                  · rcases p996_3 (m.d 3 5) (by simp) with h1007 | h1007
                                                    · linarith only [h1007, h889, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p996_1, u5ehi0]
                                                    · rcases p996_3 (m.d 4 5) (by simp) with h1009 | h1009
                                                      · linarith only [h1009, h887, hlam]
                                                      · linarith only [h1009, h637, hlam]
                                                · linarith only [h1004, h563, hlam]
                                            · have p996_0 := h996c.1
                                              have p996_1 := h996c.2.1
                                              have p996_2 := h996c.2.2.1
                                              have p996_3 := h996c.2.2.2
                                              linarith only [hlam, p996_0]
                                            · have p996_0 := h996c.1
                                              have p996_1 := h996c.2.1
                                              have p996_2 := h996c.2.2.1
                                              have p996_3 := h996c.2.2.2
                                              rcases p996_3 (m.d 0 5) (by simp) with h1014 | h1014
                                              · linarith only [h1014, h563, hlam]
                                              · linarith only [h1014, h634, hlam]
                                            · have p996_0 := h996c.1
                                              have p996_1 := h996c.2.1
                                              have p996_2 := h996c.2.2.1
                                              have p996_3 := h996c.2.2.2
                                              rcases p996_3 (m.d 0 5) (by simp) with h1017 | h1017
                                              · linarith only [h1017, h563, hlam]
                                              · linarith only [h1017, h636, hlam]
                                            · have p996_0 := h996c.1
                                              have p996_1 := h996c.2.1
                                              have p996_2 := h996c.2.2.1
                                              have p996_3 := h996c.2.2.2
                                              linarith only [h633, h637, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p996_1, u2ehi3]
                                            · have p996_0 := h996c.1
                                              have p996_1 := h996c.2.1
                                              have p996_2 := h996c.2.2.1
                                              have p996_3 := h996c.2.2.2
                                              linarith only [h634, hlam, p996_1]
                                            · have p996_0 := h996c.1
                                              have p996_1 := h996c.2.1
                                              have p996_2 := h996c.2.2.1
                                              have p996_3 := h996c.2.2.2
                                              linarith only [h885, hlam, p996_1]
                                            · have p996_0 := h996c.1
                                              have p996_1 := h996c.2.1
                                              have p996_2 := h996c.2.2.1
                                              have p996_3 := h996c.2.2.2
                                              linarith only [hlam, p996_0]
                                            · have p996_0 := h996c.1
                                              have p996_1 := h996c.2.1
                                              have p996_2 := h996c.2.2.1
                                              have p996_3 := h996c.2.2.2
                                              linarith only [h0, h634, h892, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p996_1, u3ehi3]
                                            · have p996_0 := h996c.1
                                              have p996_1 := h996c.2.1
                                              have p996_2 := h996c.2.2.1
                                              have p996_3 := h996c.2.2.2
                                              linarith only [h890, hlam, p996_1]
                                            · have p996_0 := h996c.1
                                              have p996_1 := h996c.2.1
                                              have p996_2 := h996c.2.2.1
                                              have p996_3 := h996c.2.2.2
                                              linarith only [h636, hlam, p996_0]
                                            · have p996_0 := h996c.1
                                              have p996_1 := h996c.2.1
                                              have p996_2 := h996c.2.2.1
                                              have p996_3 := h996c.2.2.2
                                              linarith only [h889, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p996_1, u5ehi1]
                                            · have p996_0 := h996c.1
                                              have p996_1 := h996c.2.1
                                              have p996_2 := h996c.2.2.1
                                              have p996_3 := h996c.2.2.2
                                              linarith only [h889, hlam, p996_0]
                                            · have p996_0 := h996c.1
                                              have p996_1 := h996c.2.1
                                              have p996_2 := h996c.2.2.1
                                              have p996_3 := h996c.2.2.2
                                              linarith only [hlam, p996_0]
                                            · have p996_0 := h996c.1
                                              have p996_1 := h996c.2.1
                                              have p996_2 := h996c.2.2.1
                                              have p996_3 := h996c.2.2.2
                                              linarith only [h892, hlam, p996_1]
                                            · have p996_0 := h996c.1
                                              have p996_1 := h996c.2.1
                                              have p996_2 := h996c.2.2.1
                                              have p996_3 := h996c.2.2.2
                                              linarith only [h634, hc45, hlam, hphi, ht23, ht34, p996_1, u2ehi4]
                                            · have p996_0 := h996c.1
                                              have p996_1 := h996c.2.1
                                              have p996_2 := h996c.2.2.1
                                              have p996_3 := h996c.2.2.2
                                              linarith only [h887, hlam, p996_0]
                                            · have p996_0 := h996c.1
                                              have p996_1 := h996c.2.1
                                              have p996_2 := h996c.2.2.1
                                              have p996_3 := h996c.2.2.2
                                              linarith only [h883, h886, h887, hc12, hlam, hphi, ht01, ht0b, ht5b, p996_1, u5ehi2]
                                            · have p996_0 := h996c.1
                                              have p996_1 := h996c.2.1
                                              have p996_2 := h996c.2.2.1
                                              have p996_3 := h996c.2.2.2
                                              linarith only [h883, h886, h887, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p996_1, u3ehi4]
                                            · have p996_0 := h996c.1
                                              have p996_1 := h996c.2.1
                                              have p996_2 := h996c.2.2.1
                                              have p996_3 := h996c.2.2.2
                                              linarith only [hlam, p996_0]
                                          · rcases h5bigk with h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c
                                            · have p1036_0 := h1036c.1
                                              have p1036_1 := h1036c.2.1
                                              have p1036_2 := h1036c.2.2.1
                                              have p1036_3 := h1036c.2.2.2
                                              linarith only [hlam, p1036_0]
                                            · have p1036_0 := h1036c.1
                                              have p1036_1 := h1036c.2.1
                                              have p1036_2 := h1036c.2.2.1
                                              have p1036_3 := h1036c.2.2.2
                                              linarith only [h563, hlam, p1036_1]
                                            · have p1036_0 := h1036c.1
                                              have p1036_1 := h1036c.2.1
                                              have p1036_2 := h1036c.2.2.1
                                              have p1036_3 := h1036c.2.2.2
                                              linarith only [h0, h632, h890, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1036_1, p894_1, u2ehi3]
                                            · have p1036_0 := h1036c.1
                                              have p1036_1 := h1036c.2.1
                                              have p1036_2 := h1036c.2.2.1
                                              have p1036_3 := h1036c.2.2.2
                                              linarith only [h0, h632, h892, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1036_1, p894_1, u3ehi3]
                                            · have p1036_0 := h1036c.1
                                              have p1036_1 := h1036c.2.1
                                              have p1036_2 := h1036c.2.2.1
                                              have p1036_3 := h1036c.2.2.2
                                              linarith only [h637, hlam, p1036_1]
                                            · have p1036_0 := h1036c.1
                                              have p1036_1 := h1036c.2.1
                                              have p1036_2 := h1036c.2.2.1
                                              have p1036_3 := h1036c.2.2.2
                                              rcases p1036_3 (m.d 0 5) (by simp) with h1042 | h1042
                                              · linarith only [h1042, h563, hlam]
                                              · rcases p1036_3 (m.d 1 5) (by simp) with h1044 | h1044
                                                · rcases p1036_3 (m.d 2 5) (by simp) with h1045 | h1045
                                                  · linarith only [h1045, h885, hlam]
                                                  · rcases p1036_3 (m.d 3 5) (by simp) with h1047 | h1047
                                                    · linarith only [h1047, h633, h637, hc35, hlam, hphi, ht23, p1036_1, u2ehi3]
                                                    · rcases p1036_3 (m.d 4 5) (by simp) with h1049 | h1049
                                                      · linarith only [h1049, h887, hlam]
                                                      · linarith only [h1049, h637, hlam]
                                                · linarith only [h1044, h563, hlam]
                                            · have p1036_0 := h1036c.1
                                              have p1036_1 := h1036c.2.1
                                              have p1036_2 := h1036c.2.2.1
                                              have p1036_3 := h1036c.2.2.2
                                              linarith only [hlam, p1036_0]
                                            · have p1036_0 := h1036c.1
                                              have p1036_1 := h1036c.2.1
                                              have p1036_2 := h1036c.2.2.1
                                              have p1036_3 := h1036c.2.2.2
                                              rcases p1036_3 (m.d 0 5) (by simp) with h1054 | h1054
                                              · linarith only [h1054, h563, hlam]
                                              · linarith only [h1054, h634, hlam]
                                            · have p1036_0 := h1036c.1
                                              have p1036_1 := h1036c.2.1
                                              have p1036_2 := h1036c.2.2.1
                                              have p1036_3 := h1036c.2.2.2
                                              rcases p1036_3 (m.d 0 5) (by simp) with h1057 | h1057
                                              · linarith only [h1057, h563, hlam]
                                              · linarith only [h1057, h636, hlam]
                                            · have p1036_0 := h1036c.1
                                              have p1036_1 := h1036c.2.1
                                              have p1036_2 := h1036c.2.2.1
                                              have p1036_3 := h1036c.2.2.2
                                              linarith only [h633, h637, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1036_1, u2ehi3]
                                            · have p1036_0 := h1036c.1
                                              have p1036_1 := h1036c.2.1
                                              have p1036_2 := h1036c.2.2.1
                                              have p1036_3 := h1036c.2.2.2
                                              linarith only [h634, hlam, p1036_1]
                                            · have p1036_0 := h1036c.1
                                              have p1036_1 := h1036c.2.1
                                              have p1036_2 := h1036c.2.2.1
                                              have p1036_3 := h1036c.2.2.2
                                              linarith only [h885, hlam, p1036_1]
                                            · have p1036_0 := h1036c.1
                                              have p1036_1 := h1036c.2.1
                                              have p1036_2 := h1036c.2.2.1
                                              have p1036_3 := h1036c.2.2.2
                                              linarith only [hlam, p1036_0]
                                            · have p1036_0 := h1036c.1
                                              have p1036_1 := h1036c.2.1
                                              have p1036_2 := h1036c.2.2.1
                                              have p1036_3 := h1036c.2.2.2
                                              linarith only [h0, h634, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1036_1, u3ehi4]
                                            · have p1036_0 := h1036c.1
                                              have p1036_1 := h1036c.2.1
                                              have p1036_2 := h1036c.2.2.1
                                              have p1036_3 := h1036c.2.2.2
                                              linarith only [h890, hlam, p1036_1]
                                            · have p1036_0 := h1036c.1
                                              have p1036_1 := h1036c.2.1
                                              have p1036_2 := h1036c.2.2.1
                                              have p1036_3 := h1036c.2.2.2
                                              linarith only [h636, hlam, p1036_0]
                                            · have p1036_0 := h1036c.1
                                              have p1036_1 := h1036c.2.1
                                              have p1036_2 := h1036c.2.2.1
                                              have p1036_3 := h1036c.2.2.2
                                              linarith only [h563, hc01, hc35, hlam, hphi, ht12, ht23, p1036_1]
                                            · have p1036_0 := h1036c.1
                                              have p1036_1 := h1036c.2.1
                                              have p1036_2 := h1036c.2.2.1
                                              have p1036_3 := h1036c.2.2.2
                                              linarith only [h889, hlam, p1036_0]
                                            · have p1036_0 := h1036c.1
                                              have p1036_1 := h1036c.2.1
                                              have p1036_2 := h1036c.2.2.1
                                              have p1036_3 := h1036c.2.2.2
                                              linarith only [hlam, p1036_0]
                                            · have p1036_0 := h1036c.1
                                              have p1036_1 := h1036c.2.1
                                              have p1036_2 := h1036c.2.2.1
                                              have p1036_3 := h1036c.2.2.2
                                              linarith only [h892, hlam, p1036_1]
                                            · have p1036_0 := h1036c.1
                                              have p1036_1 := h1036c.2.1
                                              have p1036_2 := h1036c.2.2.1
                                              have p1036_3 := h1036c.2.2.2
                                              linarith only [h634, hc45, hlam, hphi, ht23, ht34, p1036_1, u2ehi4]
                                            · have p1036_0 := h1036c.1
                                              have p1036_1 := h1036c.2.1
                                              have p1036_2 := h1036c.2.2.1
                                              have p1036_3 := h1036c.2.2.2
                                              linarith only [h887, hlam, p1036_0]
                                            · have p1036_0 := h1036c.1
                                              have p1036_1 := h1036c.2.1
                                              have p1036_2 := h1036c.2.2.1
                                              have p1036_3 := h1036c.2.2.2
                                              linarith only [h883, h886, h887, hc12, hlam, hphi, ht01, ht0b, ht5b, p1036_1, u5ehi2]
                                            · have p1036_0 := h1036c.1
                                              have p1036_1 := h1036c.2.1
                                              have p1036_2 := h1036c.2.2.1
                                              have p1036_3 := h1036c.2.2.2
                                              linarith only [h883, h886, h887, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1036_1, u3ehi4]
                                            · have p1036_0 := h1036c.1
                                              have p1036_1 := h1036c.2.1
                                              have p1036_2 := h1036c.2.2.1
                                              have p1036_3 := h1036c.2.2.2
                                              linarith only [hlam, p1036_0]
                                    · linarith only [h636, h948, hlam]
                                  · linarith only [h634, h947, hlam]
                              · have p894_0 := h894c.1
                                have p894_1 := h894c.2.1
                                have p894_2 := h894c.2.2.1
                                have p894_3 := h894c.2.2.2
                                linarith only [h637, h883, h886, h887, hc01, hc12, hlam, hphi, p894_1]
                              · have p894_0 := h894c.1
                                have p894_1 := h894c.2.1
                                have p894_2 := h894c.2.2.1
                                have p894_3 := h894c.2.2.2
                                linarith only [h633, hlam, p894_0]
                              · have p894_0 := h894c.1
                                have p894_1 := h894c.2.1
                                have p894_2 := h894c.2.2.1
                                have p894_3 := h894c.2.2.2
                                linarith only [h635, hlam, p894_0]
                              · have p894_0 := h894c.1
                                have p894_1 := h894c.2.1
                                have p894_2 := h894c.2.2.1
                                have p894_3 := h894c.2.2.2
                                linarith only [hlam, p894_0]
                              · have p894_0 := h894c.1
                                have p894_1 := h894c.2.1
                                have p894_2 := h894c.2.2.1
                                have p894_3 := h894c.2.2.2
                                linarith only [h637, hlam, p894_0]
                              · have p894_0 := h894c.1
                                have p894_1 := h894c.2.1
                                have p894_2 := h894c.2.2.1
                                have p894_3 := h894c.2.2.2
                                linarith only [h637, h883, h886, h887, hc01, hc12, hlam, hphi, p894_1]
                              · have p894_0 := h894c.1
                                have p894_1 := h894c.2.1
                                have p894_2 := h894c.2.2.1
                                have p894_3 := h894c.2.2.2
                                linarith only [h634, hlam, p894_1]
                              · have p894_0 := h894c.1
                                have p894_1 := h894c.2.1
                                have p894_2 := h894c.2.2.1
                                have p894_3 := h894c.2.2.2
                                linarith only [h636, hlam, p894_0]
                              · have p894_0 := h894c.1
                                have p894_1 := h894c.2.1
                                have p894_2 := h894c.2.2.1
                                have p894_3 := h894c.2.2.2
                                linarith only [h633, h637, h883, h886, h887, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p894_1, u2ehi3]
                              · have p894_0 := h894c.1
                                have p894_1 := h894c.2.1
                                have p894_2 := h894c.2.2.1
                                have p894_3 := h894c.2.2.2
                                linarith only [hlam, p894_0]
                        · linarith only [h636, h637, h883, h886, h887, h888, h889, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h635, h637, h883, h886, h887, h888, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1090 | h1090
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1091 | h1091
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1092 | h1092
                          · linarith only [h1092, h460, h633, h887, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1094 | h1094
                            · linarith only [h1090, h1094, h460, h633, h887, hlam]
                            · rcases h0bigk with h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [hlam, p1096_0]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [h0, hlam, p1096_1]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [h328, hlam, p1096_0]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [h460, hlam, p1096_1]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [h563, hlam, p1096_1]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                rcases p1096_3 (m.d 0 1) (by simp) with h1102 | h1102
                                · linarith only [h0, h1102, hlam]
                                · rcases p1096_3 (m.d 0 2) (by simp) with h1104 | h1104
                                  · rcases p1096_3 (m.d 0 3) (by simp) with h1105 | h1105
                                    · linarith only [h1105, h632, hlam]
                                    · linarith only [h1105, h328, hlam]
                                  · linarith only [h0, h1104, hlam]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [hlam, p1096_0]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [h0, h1091, h632, hc12, hlam, hphi, ht01, ht0b, ht5b, p1096_1, u5ehi3]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                rcases p1096_3 (m.d 0 1) (by simp) with h1111 | h1111
                                · linarith only [h0, h1111, hlam]
                                · rcases p1096_3 (m.d 0 2) (by simp) with h1113 | h1113
                                  · rcases p1096_3 (m.d 0 3) (by simp) with h1114 | h1114
                                    · linarith only [h1114, h632, hlam]
                                    · linarith only [h1114, h635, hlam]
                                  · linarith only [h1113, h633, hlam]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                rcases p1096_3 (m.d 0 1) (by simp) with h1118 | h1118
                                · linarith only [h0, h1118, hlam]
                                · rcases p1096_3 (m.d 0 2) (by simp) with h1120 | h1120
                                  · rcases p1096_3 (m.d 0 3) (by simp) with h1121 | h1121
                                    · linarith only [h1121, h632, hlam]
                                    · linarith only [h1121, h636, hlam]
                                  · linarith only [h1120, h634, hlam]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                rcases p1096_3 (m.d 0 1) (by simp) with h1125 | h1125
                                · linarith only [h1125, h328, hlam]
                                · rcases p1096_3 (m.d 0 2) (by simp) with h1127 | h1127
                                  · rcases p1096_3 (m.d 0 3) (by simp) with h1128 | h1128
                                    · rcases p1096_3 (m.d 0 4) (by simp) with h1129 | h1129
                                      · linarith only [h1129, h635, hlam]
                                      · linarith only [h1129, h460, hlam]
                                    · linarith only [h1128, h328, hlam]
                                  · linarith only [h0, h1127, hlam]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [h632, hlam, p1096_1]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [hlam, p1096_0]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                rcases p1096_3 (m.d 0 1) (by simp) with h1136 | h1136
                                · linarith only [h1136, h328, hlam]
                                · rcases p1096_3 (m.d 0 2) (by simp) with h1138 | h1138
                                  · rcases p1096_3 (m.d 0 3) (by simp) with h1139 | h1139
                                    · rcases p1096_3 (m.d 0 4) (by simp) with h1140 | h1140
                                      · linarith only [h1140, h635, hlam]
                                      · rcases p1096_3 (m.d 0 5) (by simp) with h1142 | h1142
                                        · linarith only [h1142, h636, hlam]
                                        · linarith only [h1142, h637, hlam]
                                    · linarith only [h1139, h635, hlam]
                                  · linarith only [h1138, h633, hlam]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                rcases p1096_3 (m.d 0 1) (by simp) with h1147 | h1147
                                · linarith only [h1147, h328, hlam]
                                · rcases p1096_3 (m.d 0 2) (by simp) with h1149 | h1149
                                  · rcases p1096_3 (m.d 0 3) (by simp) with h1150 | h1150
                                    · rcases p1096_3 (m.d 0 4) (by simp) with h1151 | h1151
                                      · linarith only [h1151, h635, hlam]
                                      · rcases p1096_3 (m.d 0 5) (by simp) with h1153 | h1153
                                        · linarith only [h1153, h636, hlam]
                                        · rcases h0emax with h1155 | h1155 | h1155 | h1155 | h1155
                                          · rcases h5bigk with h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c
                                            · have p1156_0 := h1156c.1
                                              have p1156_1 := h1156c.2.1
                                              have p1156_2 := h1156c.2.2.1
                                              have p1156_3 := h1156c.2.2.2
                                              linarith only [hlam, p1156_0]
                                            · have p1156_0 := h1156c.1
                                              have p1156_1 := h1156c.2.1
                                              have p1156_2 := h1156c.2.2.1
                                              have p1156_3 := h1156c.2.2.2
                                              linarith only [h563, hlam, p1156_1]
                                            · have p1156_0 := h1156c.1
                                              have p1156_1 := h1156c.2.1
                                              have p1156_2 := h1156c.2.2.1
                                              have p1156_3 := h1156c.2.2.2
                                              linarith only [h328, h883, hc12, hlam, hphi, ht01, ht0b, ht5b, p1096_1, p1156_1, u5ehi2]
                                            · have p1156_0 := h1156c.1
                                              have p1156_1 := h1156c.2.1
                                              have p1156_2 := h1156c.2.2.1
                                              have p1156_3 := h1156c.2.2.2
                                              linarith only [h1094, h328, h883, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1096_1, p1156_1]
                                            · have p1156_0 := h1156c.1
                                              have p1156_1 := h1156c.2.1
                                              have p1156_2 := h1156c.2.2.1
                                              have p1156_3 := h1156c.2.2.2
                                              linarith only [h637, hlam, p1156_1]
                                            · have p1156_0 := h1156c.1
                                              have p1156_1 := h1156c.2.1
                                              have p1156_2 := h1156c.2.2.1
                                              have p1156_3 := h1156c.2.2.2
                                              linarith only [h633, h637, h887, hc45, hlam, hphi, ht23, ht34, p1156_1, u2ehi3]
                                            · have p1156_0 := h1156c.1
                                              have p1156_1 := h1156c.2.1
                                              have p1156_2 := h1156c.2.2.1
                                              have p1156_3 := h1156c.2.2.2
                                              linarith only [hlam, p1156_0]
                                            · have p1156_0 := h1156c.1
                                              have p1156_1 := h1156c.2.1
                                              have p1156_2 := h1156c.2.2.1
                                              have p1156_3 := h1156c.2.2.2
                                              linarith only [h887, hc45, hlam, hphi, ht23, ht34, p1156_1, u2ehi4]
                                            · have p1156_0 := h1156c.1
                                              have p1156_1 := h1156c.2.1
                                              have p1156_2 := h1156c.2.2.1
                                              have p1156_3 := h1156c.2.2.2
                                              linarith only [h1094, h887, hc45, hlam, hphi, ht34, p1156_1, u3ehi3]
                                            · have p1156_0 := h1156c.1
                                              have p1156_1 := h1156c.2.1
                                              have p1156_2 := h1156c.2.2.1
                                              have p1156_3 := h1156c.2.2.2
                                              linarith only [h887, hlam, p1156_1]
                                            · have p1156_0 := h1156c.1
                                              have p1156_1 := h1156c.2.1
                                              have p1156_2 := h1156c.2.2.1
                                              have p1156_3 := h1156c.2.2.2
                                              linarith only [h634, hlam, p1156_1]
                                            · have p1156_0 := h1156c.1
                                              have p1156_1 := h1156c.2.1
                                              have p1156_2 := h1156c.2.2.1
                                              have p1156_3 := h1156c.2.2.2
                                              linarith only [h885, hlam, p1156_1]
                                            · have p1156_0 := h1156c.1
                                              have p1156_1 := h1156c.2.1
                                              have p1156_2 := h1156c.2.2.1
                                              have p1156_3 := h1156c.2.2.2
                                              linarith only [hlam, p1156_0]
                                            · have p1156_0 := h1156c.1
                                              have p1156_1 := h1156c.2.1
                                              have p1156_2 := h1156c.2.2.1
                                              have p1156_3 := h1156c.2.2.2
                                              linarith only [h1094, h634, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1156_1, u3ehi3]
                                            · have p1156_0 := h1156c.1
                                              have p1156_1 := h1156c.2.1
                                              have p1156_2 := h1156c.2.2.1
                                              have p1156_3 := h1156c.2.2.2
                                              linarith only [h1092, hlam, p1156_1]
                                            · have p1156_0 := h1156c.1
                                              have p1156_1 := h1156c.2.1
                                              have p1156_2 := h1156c.2.2.1
                                              have p1156_3 := h1156c.2.2.2
                                              linarith only [h636, hlam, p1156_0]
                                            · have p1156_0 := h1156c.1
                                              have p1156_1 := h1156c.2.1
                                              have p1156_2 := h1156c.2.2.1
                                              have p1156_3 := h1156c.2.2.2
                                              linarith only [h1091, h328, h633, h637, h883, hc12, hc23, hlam, hphi, ht01, ht0b, ht5b, p1096_1, p1156_1, u2ehi3, u5ehi1]
                                            · have p1156_0 := h1156c.1
                                              have p1156_1 := h1156c.2.1
                                              have p1156_2 := h1156c.2.2.1
                                              have p1156_3 := h1156c.2.2.2
                                              linarith only [h1091, hlam, p1156_0]
                                            · have p1156_0 := h1156c.1
                                              have p1156_1 := h1156c.2.1
                                              have p1156_2 := h1156c.2.2.1
                                              have p1156_3 := h1156c.2.2.2
                                              linarith only [hlam, p1156_0]
                                            · have p1156_0 := h1156c.1
                                              have p1156_1 := h1156c.2.1
                                              have p1156_2 := h1156c.2.2.1
                                              have p1156_3 := h1156c.2.2.2
                                              linarith only [h1094, hlam, p1156_1]
                                            · have p1156_0 := h1156c.1
                                              have p1156_1 := h1156c.2.1
                                              have p1156_2 := h1156c.2.2.1
                                              have p1156_3 := h1156c.2.2.2
                                              linarith only [h633, h637, hc45, hlam, hphi, ht23, ht34, p1156_1, u2ehi3]
                                            · have p1156_0 := h1156c.1
                                              have p1156_1 := h1156c.2.1
                                              have p1156_2 := h1156c.2.2.1
                                              have p1156_3 := h1156c.2.2.2
                                              linarith only [h328, h563, h633, h637, h883, hc01, hc12, hc45, hlam, hphi, ht23, ht34, p1096_1, p1156_1, u2ehi3]
                                            · have p1156_0 := h1156c.1
                                              have p1156_1 := h1156c.2.1
                                              have p1156_2 := h1156c.2.2.1
                                              have p1156_3 := h1156c.2.2.2
                                              linarith only [hc45, hlam, hphi, ht23, ht34, p1156_1, u2ehi4]
                                            · have p1156_0 := h1156c.1
                                              have p1156_1 := h1156c.2.1
                                              have p1156_2 := h1156c.2.2.1
                                              have p1156_3 := h1156c.2.2.2
                                              linarith only [hc45, hlam, hphi, ht34, p1156_1, u3ehi4]
                                            · have p1156_0 := h1156c.1
                                              have p1156_1 := h1156c.2.1
                                              have p1156_2 := h1156c.2.2.1
                                              have p1156_3 := h1156c.2.2.2
                                              linarith only [hlam, p1156_0]
                                          · linarith only [h1091, h1094, h1155, h632, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                          · linarith only [h1155, h633, h637, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1096_1, u2ehi3]
                                          · rcases h5bigk with h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c
                                            · have p1184_0 := h1184c.1
                                              have p1184_1 := h1184c.2.1
                                              have p1184_2 := h1184c.2.2.1
                                              have p1184_3 := h1184c.2.2.2
                                              linarith only [hlam, p1184_0]
                                            · have p1184_0 := h1184c.1
                                              have p1184_1 := h1184c.2.1
                                              have p1184_2 := h1184c.2.2.1
                                              have p1184_3 := h1184c.2.2.2
                                              linarith only [h563, hlam, p1184_1]
                                            · have p1184_0 := h1184c.1
                                              have p1184_1 := h1184c.2.1
                                              have p1184_2 := h1184c.2.2.1
                                              have p1184_3 := h1184c.2.2.2
                                              linarith only [h1092, h328, h883, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1096_1, p1184_1, u2ehi3]
                                            · have p1184_0 := h1184c.1
                                              have p1184_1 := h1184c.2.1
                                              have p1184_2 := h1184c.2.2.1
                                              have p1184_3 := h1184c.2.2.2
                                              linarith only [h1094, h328, h883, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1096_1, p1184_1, u3ehi3]
                                            · have p1184_0 := h1184c.1
                                              have p1184_1 := h1184c.2.1
                                              have p1184_2 := h1184c.2.2.1
                                              have p1184_3 := h1184c.2.2.2
                                              linarith only [h637, hlam, p1184_1]
                                            · have p1184_0 := h1184c.1
                                              have p1184_1 := h1184c.2.1
                                              have p1184_2 := h1184c.2.2.1
                                              have p1184_3 := h1184c.2.2.2
                                              linarith only [h1092, h634, h887, hc45, hlam, hphi, ht23, ht34, p1184_1, u2ehi3]
                                            · have p1184_0 := h1184c.1
                                              have p1184_1 := h1184c.2.1
                                              have p1184_2 := h1184c.2.2.1
                                              have p1184_3 := h1184c.2.2.2
                                              linarith only [hlam, p1184_0]
                                            · have p1184_0 := h1184c.1
                                              have p1184_1 := h1184c.2.1
                                              have p1184_2 := h1184c.2.2.1
                                              have p1184_3 := h1184c.2.2.2
                                              linarith only [h1092, h887, hc45, hlam, hphi, ht23, ht34, p1184_1, u2ehi3]
                                            · have p1184_0 := h1184c.1
                                              have p1184_1 := h1184c.2.1
                                              have p1184_2 := h1184c.2.2.1
                                              have p1184_3 := h1184c.2.2.2
                                              linarith only [h1094, h887, hc45, hlam, hphi, ht34, p1184_1, u3ehi3]
                                            · have p1184_0 := h1184c.1
                                              have p1184_1 := h1184c.2.1
                                              have p1184_2 := h1184c.2.2.1
                                              have p1184_3 := h1184c.2.2.2
                                              linarith only [h887, hlam, p1184_1]
                                            · have p1184_0 := h1184c.1
                                              have p1184_1 := h1184c.2.1
                                              have p1184_2 := h1184c.2.2.1
                                              have p1184_3 := h1184c.2.2.2
                                              linarith only [h634, hlam, p1184_1]
                                            · have p1184_0 := h1184c.1
                                              have p1184_1 := h1184c.2.1
                                              have p1184_2 := h1184c.2.2.1
                                              have p1184_3 := h1184c.2.2.2
                                              linarith only [h885, hlam, p1184_1]
                                            · have p1184_0 := h1184c.1
                                              have p1184_1 := h1184c.2.1
                                              have p1184_2 := h1184c.2.2.1
                                              have p1184_3 := h1184c.2.2.2
                                              linarith only [hlam, p1184_0]
                                            · have p1184_0 := h1184c.1
                                              have p1184_1 := h1184c.2.1
                                              have p1184_2 := h1184c.2.2.1
                                              have p1184_3 := h1184c.2.2.2
                                              linarith only [h1094, h563, h634, h887, hc45, hlam, hphi, ht34, p1184_1, u3ehi3]
                                            · have p1184_0 := h1184c.1
                                              have p1184_1 := h1184c.2.1
                                              have p1184_2 := h1184c.2.2.1
                                              have p1184_3 := h1184c.2.2.2
                                              linarith only [h1092, hlam, p1184_1]
                                            · have p1184_0 := h1184c.1
                                              have p1184_1 := h1184c.2.1
                                              have p1184_2 := h1184c.2.2.1
                                              have p1184_3 := h1184c.2.2.2
                                              linarith only [h636, hlam, p1184_0]
                                            · have p1184_0 := h1184c.1
                                              have p1184_1 := h1184c.2.1
                                              have p1184_2 := h1184c.2.2.1
                                              have p1184_3 := h1184c.2.2.2
                                              linarith only [h1091, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1184_1, u5ehi1]
                                            · have p1184_0 := h1184c.1
                                              have p1184_1 := h1184c.2.1
                                              have p1184_2 := h1184c.2.2.1
                                              have p1184_3 := h1184c.2.2.2
                                              linarith only [h1091, hlam, p1184_0]
                                            · have p1184_0 := h1184c.1
                                              have p1184_1 := h1184c.2.1
                                              have p1184_2 := h1184c.2.2.1
                                              have p1184_3 := h1184c.2.2.2
                                              linarith only [hlam, p1184_0]
                                            · have p1184_0 := h1184c.1
                                              have p1184_1 := h1184c.2.1
                                              have p1184_2 := h1184c.2.2.1
                                              have p1184_3 := h1184c.2.2.2
                                              linarith only [h1094, hlam, p1184_1]
                                            · have p1184_0 := h1184c.1
                                              have p1184_1 := h1184c.2.1
                                              have p1184_2 := h1184c.2.2.1
                                              have p1184_3 := h1184c.2.2.2
                                              linarith only [h634, hc45, hlam, hphi, ht23, ht34, p1184_1, u2ehi4]
                                            · have p1184_0 := h1184c.1
                                              have p1184_1 := h1184c.2.1
                                              have p1184_2 := h1184c.2.2.1
                                              have p1184_3 := h1184c.2.2.2
                                              linarith only [h563, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1184_1]
                                            · have p1184_0 := h1184c.1
                                              have p1184_1 := h1184c.2.1
                                              have p1184_2 := h1184c.2.2.1
                                              have p1184_3 := h1184c.2.2.2
                                              linarith only [hc45, hlam, hphi, ht23, ht34, p1184_1, u2ehi4]
                                            · have p1184_0 := h1184c.1
                                              have p1184_1 := h1184c.2.1
                                              have p1184_2 := h1184c.2.2.1
                                              have p1184_3 := h1184c.2.2.2
                                              linarith only [hc45, hlam, hphi, ht34, p1184_1, u3ehi4]
                                            · have p1184_0 := h1184c.1
                                              have p1184_1 := h1184c.2.1
                                              have p1184_2 := h1184c.2.2.1
                                              have p1184_3 := h1184c.2.2.2
                                              linarith only [hlam, p1184_0]
                                          · rcases h5bigk with h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c
                                            · have p1210_0 := h1210c.1
                                              have p1210_1 := h1210c.2.1
                                              have p1210_2 := h1210c.2.2.1
                                              have p1210_3 := h1210c.2.2.2
                                              linarith only [hlam, p1210_0]
                                            · have p1210_0 := h1210c.1
                                              have p1210_1 := h1210c.2.1
                                              have p1210_2 := h1210c.2.2.1
                                              have p1210_3 := h1210c.2.2.2
                                              linarith only [h563, hlam, p1210_1]
                                            · have p1210_0 := h1210c.1
                                              have p1210_1 := h1210c.2.1
                                              have p1210_2 := h1210c.2.2.1
                                              have p1210_3 := h1210c.2.2.2
                                              linarith only [h1092, h328, h883, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1096_1, p1210_1, u2ehi3]
                                            · have p1210_0 := h1210c.1
                                              have p1210_1 := h1210c.2.1
                                              have p1210_2 := h1210c.2.2.1
                                              have p1210_3 := h1210c.2.2.2
                                              linarith only [h1094, h328, h883, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1096_1, p1210_1, u3ehi3]
                                            · have p1210_0 := h1210c.1
                                              have p1210_1 := h1210c.2.1
                                              have p1210_2 := h1210c.2.2.1
                                              have p1210_3 := h1210c.2.2.2
                                              linarith only [h637, hlam, p1210_1]
                                            · have p1210_0 := h1210c.1
                                              have p1210_1 := h1210c.2.1
                                              have p1210_2 := h1210c.2.2.1
                                              have p1210_3 := h1210c.2.2.2
                                              linarith only [h633, h637, h887, hc45, hlam, hphi, ht23, ht34, p1210_1, u2ehi3]
                                            · have p1210_0 := h1210c.1
                                              have p1210_1 := h1210c.2.1
                                              have p1210_2 := h1210c.2.2.1
                                              have p1210_3 := h1210c.2.2.2
                                              linarith only [hlam, p1210_0]
                                            · have p1210_0 := h1210c.1
                                              have p1210_1 := h1210c.2.1
                                              have p1210_2 := h1210c.2.2.1
                                              have p1210_3 := h1210c.2.2.2
                                              linarith only [h1092, h887, hc45, hlam, hphi, ht23, ht34, p1210_1, u2ehi3]
                                            · have p1210_0 := h1210c.1
                                              have p1210_1 := h1210c.2.1
                                              have p1210_2 := h1210c.2.2.1
                                              have p1210_3 := h1210c.2.2.2
                                              linarith only [h1094, h887, hc45, hlam, hphi, ht34, p1210_1, u3ehi3]
                                            · have p1210_0 := h1210c.1
                                              have p1210_1 := h1210c.2.1
                                              have p1210_2 := h1210c.2.2.1
                                              have p1210_3 := h1210c.2.2.2
                                              linarith only [h887, hlam, p1210_1]
                                            · have p1210_0 := h1210c.1
                                              have p1210_1 := h1210c.2.1
                                              have p1210_2 := h1210c.2.2.1
                                              have p1210_3 := h1210c.2.2.2
                                              linarith only [h634, hlam, p1210_1]
                                            · have p1210_0 := h1210c.1
                                              have p1210_1 := h1210c.2.1
                                              have p1210_2 := h1210c.2.2.1
                                              have p1210_3 := h1210c.2.2.2
                                              linarith only [h885, hlam, p1210_1]
                                            · have p1210_0 := h1210c.1
                                              have p1210_1 := h1210c.2.1
                                              have p1210_2 := h1210c.2.2.1
                                              have p1210_3 := h1210c.2.2.2
                                              linarith only [hlam, p1210_0]
                                            · have p1210_0 := h1210c.1
                                              have p1210_1 := h1210c.2.1
                                              have p1210_2 := h1210c.2.2.1
                                              have p1210_3 := h1210c.2.2.2
                                              linarith only [h0, h1094, h634, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1210_1, u3ehi3]
                                            · have p1210_0 := h1210c.1
                                              have p1210_1 := h1210c.2.1
                                              have p1210_2 := h1210c.2.2.1
                                              have p1210_3 := h1210c.2.2.2
                                              linarith only [h1092, hlam, p1210_1]
                                            · have p1210_0 := h1210c.1
                                              have p1210_1 := h1210c.2.1
                                              have p1210_2 := h1210c.2.2.1
                                              have p1210_3 := h1210c.2.2.2
                                              linarith only [h636, hlam, p1210_0]
                                            · have p1210_0 := h1210c.1
                                              have p1210_1 := h1210c.2.1
                                              have p1210_2 := h1210c.2.2.1
                                              have p1210_3 := h1210c.2.2.2
                                              linarith only [h563, hc01, hc35, hlam, hphi, ht12, ht23, p1210_1]
                                            · have p1210_0 := h1210c.1
                                              have p1210_1 := h1210c.2.1
                                              have p1210_2 := h1210c.2.2.1
                                              have p1210_3 := h1210c.2.2.2
                                              linarith only [h1091, hlam, p1210_0]
                                            · have p1210_0 := h1210c.1
                                              have p1210_1 := h1210c.2.1
                                              have p1210_2 := h1210c.2.2.1
                                              have p1210_3 := h1210c.2.2.2
                                              linarith only [hlam, p1210_0]
                                            · have p1210_0 := h1210c.1
                                              have p1210_1 := h1210c.2.1
                                              have p1210_2 := h1210c.2.2.1
                                              have p1210_3 := h1210c.2.2.2
                                              linarith only [h1094, hlam, p1210_1]
                                            · have p1210_0 := h1210c.1
                                              have p1210_1 := h1210c.2.1
                                              have p1210_2 := h1210c.2.2.1
                                              have p1210_3 := h1210c.2.2.2
                                              linarith only [h634, hc45, hlam, hphi, ht23, ht34, p1210_1, u2ehi4]
                                            · have p1210_0 := h1210c.1
                                              have p1210_1 := h1210c.2.1
                                              have p1210_2 := h1210c.2.2.1
                                              have p1210_3 := h1210c.2.2.2
                                              linarith only [h563, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1210_1]
                                            · have p1210_0 := h1210c.1
                                              have p1210_1 := h1210c.2.1
                                              have p1210_2 := h1210c.2.2.1
                                              have p1210_3 := h1210c.2.2.2
                                              linarith only [hc45, hlam, hphi, ht23, ht34, p1210_1, u2ehi4]
                                            · have p1210_0 := h1210c.1
                                              have p1210_1 := h1210c.2.1
                                              have p1210_2 := h1210c.2.2.1
                                              have p1210_3 := h1210c.2.2.2
                                              linarith only [hc45, hlam, hphi, ht34, p1210_1, u3ehi4]
                                            · have p1210_0 := h1210c.1
                                              have p1210_1 := h1210c.2.1
                                              have p1210_2 := h1210c.2.2.1
                                              have p1210_3 := h1210c.2.2.2
                                              linarith only [hlam, p1210_0]
                                    · linarith only [h1150, h636, hlam]
                                  · linarith only [h1149, h634, hlam]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [h637, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1096_1]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [h633, hlam, p1096_0]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [h635, hlam, p1096_0]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [hlam, p1096_0]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [h637, hlam, p1096_0]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                rcases p1096_3 (m.d 0 1) (by simp) with h1243 | h1243
                                · linarith only [h1243, h563, hlam]
                                · rcases p1096_3 (m.d 0 2) (by simp) with h1245 | h1245
                                  · rcases p1096_3 (m.d 0 3) (by simp) with h1246 | h1246
                                    · rcases p1096_3 (m.d 0 4) (by simp) with h1247 | h1247
                                      · linarith only [h1247, h637, hlam]
                                      · linarith only [h1247, h460, hlam]
                                    · linarith only [h1246, h328, hlam]
                                  · linarith only [h0, h1245, hlam]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [h634, hlam, p1096_1]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [h636, hlam, p1096_0]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [h633, h637, hc45, hlam, hphi, ht23, ht34, p1096_1, u2ehi3]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [hlam, p1096_0]
                        · linarith only [h1090, h1091, h328, h636, h883, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1090, h460, h635, h887, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h328, h635, h637, h886, hc45, hlam, hphi, ht34, u3ehi0]
                · linarith only [h0, h632, h885, hc25, hlam, hphi, u2ehi2]
              · linarith only [h0, h632, h884, hc24, hlam, hphi, u2ehi2]
            · linarith only [h0, h632, h883, hlam]
        · linarith only [h635, h636, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1263 | h1263
        · linarith only [h1263, h635, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1265 | h1265
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1266 | h1266
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1267 | h1267
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1268 | h1268
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1269 | h1269
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1270 | h1270
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1271 | h1271
                      · linarith only [h1271, h632, h635, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1273 | h1273
                        · linarith only [h1263, h1273, h632, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1275 | h1275
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1276 | h1276
                            · rcases h0bigk with h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c
                              · have p1277_0 := h1277c.1
                                have p1277_1 := h1277c.2.1
                                have p1277_2 := h1277c.2.2.1
                                have p1277_3 := h1277c.2.2.2
                                linarith only [hlam, p1277_0]
                              · have p1277_0 := h1277c.1
                                have p1277_1 := h1277c.2.1
                                have p1277_2 := h1277c.2.2.1
                                have p1277_3 := h1277c.2.2.2
                                linarith only [h0, hlam, p1277_1]
                              · have p1277_0 := h1277c.1
                                have p1277_1 := h1277c.2.1
                                have p1277_2 := h1277c.2.2.1
                                have p1277_3 := h1277c.2.2.2
                                linarith only [h328, hlam, p1277_0]
                              · have p1277_0 := h1277c.1
                                have p1277_1 := h1277c.2.1
                                have p1277_2 := h1277c.2.2.1
                                have p1277_3 := h1277c.2.2.2
                                linarith only [h460, hlam, p1277_1]
                              · have p1277_0 := h1277c.1
                                have p1277_1 := h1277c.2.1
                                have p1277_2 := h1277c.2.2.1
                                have p1277_3 := h1277c.2.2.2
                                linarith only [h563, hlam, p1277_1]
                              · have p1277_0 := h1277c.1
                                have p1277_1 := h1277c.2.1
                                have p1277_2 := h1277c.2.2.1
                                have p1277_3 := h1277c.2.2.2
                                rcases p1277_3 (m.d 0 1) (by simp) with h1283 | h1283
                                · linarith only [h0, h1283, hlam]
                                · rcases p1277_3 (m.d 0 2) (by simp) with h1285 | h1285
                                  · rcases p1277_3 (m.d 0 3) (by simp) with h1286 | h1286
                                    · linarith only [h1286, h632, hlam]
                                    · linarith only [h1286, h328, hlam]
                                  · linarith only [h0, h1285, hlam]
                              · have p1277_0 := h1277c.1
                                have p1277_1 := h1277c.2.1
                                have p1277_2 := h1277c.2.2.1
                                have p1277_3 := h1277c.2.2.2
                                linarith only [hlam, p1277_0]
                              · have p1277_0 := h1277c.1
                                have p1277_1 := h1277c.2.1
                                have p1277_2 := h1277c.2.2.1
                                have p1277_3 := h1277c.2.2.2
                                rcases p1277_3 (m.d 0 1) (by simp) with h1291 | h1291
                                · linarith only [h0, h1291, hlam]
                                · rcases p1277_3 (m.d 0 2) (by simp) with h1293 | h1293
                                  · rcases p1277_3 (m.d 0 3) (by simp) with h1294 | h1294
                                    · linarith only [h1294, h632, hlam]
                                    · rcases p1277_3 (m.d 0 4) (by simp) with h1296 | h1296
                                      · linarith only [h1296, h633, hlam]
                                      · linarith only [h1296, h635, hlam]
                                  · linarith only [h1293, h632, hlam]
                              · have p1277_0 := h1277c.1
                                have p1277_1 := h1277c.2.1
                                have p1277_2 := h1277c.2.2.1
                                have p1277_3 := h1277c.2.2.2
                                linarith only [h0, h1275, h633, hc12, hlam, hphi, ht01, ht0b, ht5b, p1277_1, u5ehi4]
                              · have p1277_0 := h1277c.1
                                have p1277_1 := h1277c.2.1
                                have p1277_2 := h1277c.2.2.1
                                have p1277_3 := h1277c.2.2.2
                                rcases p1277_3 (m.d 0 1) (by simp) with h1301 | h1301
                                · linarith only [h0, h1301, hlam]
                                · rcases p1277_3 (m.d 0 2) (by simp) with h1303 | h1303
                                  · rcases p1277_3 (m.d 0 3) (by simp) with h1304 | h1304
                                    · linarith only [h1304, h632, hlam]
                                    · rcases p1277_3 (m.d 0 4) (by simp) with h1306 | h1306
                                      · linarith only [h1306, h633, hlam]
                                      · linarith only [h1265, h1306, hlam]
                                  · linarith only [h1303, h634, hlam]
                              · have p1277_0 := h1277c.1
                                have p1277_1 := h1277c.2.1
                                have p1277_2 := h1277c.2.2.1
                                have p1277_3 := h1277c.2.2.2
                                linarith only [h1263, h1266, h1269, h1276, hc01, hc12, hlam, hphi, p1277_1]
                              · have p1277_0 := h1277c.1
                                have p1277_1 := h1277c.2.1
                                have p1277_2 := h1277c.2.2.1
                                have p1277_3 := h1277c.2.2.2
                                linarith only [h632, hlam, p1277_1]
                              · have p1277_0 := h1277c.1
                                have p1277_1 := h1277c.2.1
                                have p1277_2 := h1277c.2.2.1
                                have p1277_3 := h1277c.2.2.2
                                linarith only [hlam, p1277_0]
                              · have p1277_0 := h1277c.1
                                have p1277_1 := h1277c.2.1
                                have p1277_2 := h1277c.2.2.1
                                have p1277_3 := h1277c.2.2.2
                                linarith only [h635, hlam, p1277_1]
                              · have p1277_0 := h1277c.1
                                have p1277_1 := h1277c.2.1
                                have p1277_2 := h1277c.2.2.1
                                have p1277_3 := h1277c.2.2.2
                                linarith only [h1263, hlam, p1277_1]
                              · have p1277_0 := h1277c.1
                                have p1277_1 := h1277c.2.1
                                have p1277_2 := h1277c.2.2.1
                                have p1277_3 := h1277c.2.2.2
                                linarith only [h1266, h1269, h635, hc01, hc12, hlam, hphi, p1277_1]
                              · have p1277_0 := h1277c.1
                                have p1277_1 := h1277c.2.1
                                have p1277_2 := h1277c.2.2.1
                                have p1277_3 := h1277c.2.2.2
                                linarith only [h633, hlam, p1277_0]
                              · have p1277_0 := h1277c.1
                                have p1277_1 := h1277c.2.1
                                have p1277_2 := h1277c.2.2.1
                                have p1277_3 := h1277c.2.2.2
                                linarith only [h1266, h1269, h632, h635, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1277_1, u2ehi2]
                              · have p1277_0 := h1277c.1
                                have p1277_1 := h1277c.2.1
                                have p1277_2 := h1277c.2.2.1
                                have p1277_3 := h1277c.2.2.2
                                linarith only [hlam, p1277_0]
                              · have p1277_0 := h1277c.1
                                have p1277_1 := h1277c.2.1
                                have p1277_2 := h1277c.2.2.1
                                have p1277_3 := h1277c.2.2.2
                                linarith only [h1266, h1269, h635, hc12, hlam, hphi, ht01, ht0b, ht5b, p1277_1, u5ehi0]
                              · have p1277_0 := h1277c.1
                                have p1277_1 := h1277c.2.1
                                have p1277_2 := h1277c.2.2.1
                                have p1277_3 := h1277c.2.2.2
                                linarith only [h1263, h1266, h1269, h1276, hc01, hc12, hlam, hphi, p1277_1]
                              · have p1277_0 := h1277c.1
                                have p1277_1 := h1277c.2.1
                                have p1277_2 := h1277c.2.2.1
                                have p1277_3 := h1277c.2.2.2
                                linarith only [h634, hlam, p1277_1]
                              · have p1277_0 := h1277c.1
                                have p1277_1 := h1277c.2.1
                                have p1277_2 := h1277c.2.2.1
                                have p1277_3 := h1277c.2.2.2
                                linarith only [h1263, h1266, h1269, h1276, h632, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1277_1, u2ehi2]
                              · have p1277_0 := h1277c.1
                                have p1277_1 := h1277c.2.1
                                have p1277_2 := h1277c.2.2.1
                                have p1277_3 := h1277c.2.2.2
                                linarith only [h1265, hlam, p1277_1]
                              · have p1277_0 := h1277c.1
                                have p1277_1 := h1277c.2.1
                                have p1277_2 := h1277c.2.2.1
                                have p1277_3 := h1277c.2.2.2
                                linarith only [hlam, p1277_0]
                            · linarith only [h0, h1275, h1276, h633, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h1265, h1269, h1271, h1275, h635, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h1265, h1269, h1270, h635, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1328 | h1328
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1329 | h1329
                      · linarith only [h1269, h1329, h328, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1331 | h1331
                        · linarith only [h1263, h1331, h632, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1333 | h1333
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1334 | h1334
                            · rcases h0bigk with h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c
                              · have p1335_0 := h1335c.1
                                have p1335_1 := h1335c.2.1
                                have p1335_2 := h1335c.2.2.1
                                have p1335_3 := h1335c.2.2.2
                                linarith only [hlam, p1335_0]
                              · have p1335_0 := h1335c.1
                                have p1335_1 := h1335c.2.1
                                have p1335_2 := h1335c.2.2.1
                                have p1335_3 := h1335c.2.2.2
                                linarith only [h0, hlam, p1335_1]
                              · have p1335_0 := h1335c.1
                                have p1335_1 := h1335c.2.1
                                have p1335_2 := h1335c.2.2.1
                                have p1335_3 := h1335c.2.2.2
                                linarith only [h328, hlam, p1335_0]
                              · have p1335_0 := h1335c.1
                                have p1335_1 := h1335c.2.1
                                have p1335_2 := h1335c.2.2.1
                                have p1335_3 := h1335c.2.2.2
                                linarith only [h460, hlam, p1335_1]
                              · have p1335_0 := h1335c.1
                                have p1335_1 := h1335c.2.1
                                have p1335_2 := h1335c.2.2.1
                                have p1335_3 := h1335c.2.2.2
                                linarith only [h563, hlam, p1335_1]
                              · have p1335_0 := h1335c.1
                                have p1335_1 := h1335c.2.1
                                have p1335_2 := h1335c.2.2.1
                                have p1335_3 := h1335c.2.2.2
                                rcases p1335_3 (m.d 0 1) (by simp) with h1341 | h1341
                                · linarith only [h0, h1341, hlam]
                                · rcases p1335_3 (m.d 0 2) (by simp) with h1343 | h1343
                                  · rcases p1335_3 (m.d 0 3) (by simp) with h1344 | h1344
                                    · linarith only [h1344, h632, hlam]
                                    · linarith only [h1344, h328, hlam]
                                  · linarith only [h0, h1343, hlam]
                              · have p1335_0 := h1335c.1
                                have p1335_1 := h1335c.2.1
                                have p1335_2 := h1335c.2.2.1
                                have p1335_3 := h1335c.2.2.2
                                linarith only [hlam, p1335_0]
                              · have p1335_0 := h1335c.1
                                have p1335_1 := h1335c.2.1
                                have p1335_2 := h1335c.2.2.1
                                have p1335_3 := h1335c.2.2.2
                                rcases p1335_3 (m.d 0 1) (by simp) with h1349 | h1349
                                · linarith only [h0, h1349, hlam]
                                · rcases p1335_3 (m.d 0 2) (by simp) with h1351 | h1351
                                  · rcases p1335_3 (m.d 0 3) (by simp) with h1352 | h1352
                                    · linarith only [h1352, h632, hlam]
                                    · rcases p1335_3 (m.d 0 4) (by simp) with h1354 | h1354
                                      · linarith only [h1354, h633, hlam]
                                      · linarith only [h1354, h635, hlam]
                                  · linarith only [h1351, h632, hlam]
                              · have p1335_0 := h1335c.1
                                have p1335_1 := h1335c.2.1
                                have p1335_2 := h1335c.2.2.1
                                have p1335_3 := h1335c.2.2.2
                                linarith only [h0, h1333, h633, hc12, hlam, hphi, ht01, ht0b, ht5b, p1335_1, u5ehi4]
                              · have p1335_0 := h1335c.1
                                have p1335_1 := h1335c.2.1
                                have p1335_2 := h1335c.2.2.1
                                have p1335_3 := h1335c.2.2.2
                                rcases p1335_3 (m.d 0 1) (by simp) with h1359 | h1359
                                · linarith only [h0, h1359, hlam]
                                · rcases p1335_3 (m.d 0 2) (by simp) with h1361 | h1361
                                  · rcases p1335_3 (m.d 0 3) (by simp) with h1362 | h1362
                                    · linarith only [h1362, h632, hlam]
                                    · rcases p1335_3 (m.d 0 4) (by simp) with h1364 | h1364
                                      · linarith only [h1364, h633, hlam]
                                      · linarith only [h1265, h1364, hlam]
                                  · linarith only [h1361, h634, hlam]
                              · have p1335_0 := h1335c.1
                                have p1335_1 := h1335c.2.1
                                have p1335_2 := h1335c.2.2.1
                                have p1335_3 := h1335c.2.2.2
                                linarith only [h1263, hc01, hc35, hlam, hphi, ht12, ht23, p1335_1]
                              · have p1335_0 := h1335c.1
                                have p1335_1 := h1335c.2.1
                                have p1335_2 := h1335c.2.2.1
                                have p1335_3 := h1335c.2.2.2
                                linarith only [h632, hlam, p1335_1]
                              · have p1335_0 := h1335c.1
                                have p1335_1 := h1335c.2.1
                                have p1335_2 := h1335c.2.2.1
                                have p1335_3 := h1335c.2.2.2
                                linarith only [hlam, p1335_0]
                              · have p1335_0 := h1335c.1
                                have p1335_1 := h1335c.2.1
                                have p1335_2 := h1335c.2.2.1
                                have p1335_3 := h1335c.2.2.2
                                linarith only [h635, hlam, p1335_1]
                              · have p1335_0 := h1335c.1
                                have p1335_1 := h1335c.2.1
                                have p1335_2 := h1335c.2.2.1
                                have p1335_3 := h1335c.2.2.2
                                linarith only [h1263, hlam, p1335_1]
                              · have p1335_0 := h1335c.1
                                have p1335_1 := h1335c.2.1
                                have p1335_2 := h1335c.2.2.1
                                have p1335_3 := h1335c.2.2.2
                                rcases p1335_3 (m.d 0 1) (by simp) with h1373 | h1373
                                · linarith only [h1373, h460, hlam]
                                · rcases p1335_3 (m.d 0 2) (by simp) with h1375 | h1375
                                  · rcases p1335_3 (m.d 0 3) (by simp) with h1376 | h1376
                                    · linarith only [h1376, h635, hlam]
                                    · linarith only [h1376, h328, hlam]
                                  · linarith only [h0, h1375, hlam]
                              · have p1335_0 := h1335c.1
                                have p1335_1 := h1335c.2.1
                                have p1335_2 := h1335c.2.2.1
                                have p1335_3 := h1335c.2.2.2
                                linarith only [h633, hlam, p1335_0]
                              · have p1335_0 := h1335c.1
                                have p1335_1 := h1335c.2.1
                                have p1335_2 := h1335c.2.2.1
                                have p1335_3 := h1335c.2.2.2
                                linarith only [h1269, h460, hc34, hlam, hphi, p1335_1, u3ehi0]
                              · have p1335_0 := h1335c.1
                                have p1335_1 := h1335c.2.1
                                have p1335_2 := h1335c.2.2.1
                                have p1335_3 := h1335c.2.2.2
                                linarith only [hlam, p1335_0]
                              · have p1335_0 := h1335c.1
                                have p1335_1 := h1335c.2.1
                                have p1335_2 := h1335c.2.2.1
                                have p1335_3 := h1335c.2.2.2
                                linarith only [h1263, h1269, h460, h632, hc34, hlam, hphi, ht23, p1335_1, u2ehi2]
                              · have p1335_0 := h1335c.1
                                have p1335_1 := h1335c.2.1
                                have p1335_2 := h1335c.2.2.1
                                have p1335_3 := h1335c.2.2.2
                                rcases p1335_3 (m.d 0 1) (by simp) with h1384 | h1384
                                · linarith only [h1384, h563, hlam]
                                · rcases p1335_3 (m.d 0 2) (by simp) with h1386 | h1386
                                  · rcases p1335_3 (m.d 0 3) (by simp) with h1387 | h1387
                                    · linarith only [h1263, h1387, hlam]
                                    · linarith only [h1387, h328, hlam]
                                  · linarith only [h0, h1386, hlam]
                              · have p1335_0 := h1335c.1
                                have p1335_1 := h1335c.2.1
                                have p1335_2 := h1335c.2.2.1
                                have p1335_3 := h1335c.2.2.2
                                linarith only [h634, hlam, p1335_1]
                              · have p1335_0 := h1335c.1
                                have p1335_1 := h1335c.2.1
                                have p1335_2 := h1335c.2.2.1
                                have p1335_3 := h1335c.2.2.2
                                linarith only [h1263, h632, hc35, hlam, hphi, ht23, p1335_1, u2ehi2]
                              · have p1335_0 := h1335c.1
                                have p1335_1 := h1335c.2.1
                                have p1335_2 := h1335c.2.2.1
                                have p1335_3 := h1335c.2.2.2
                                linarith only [h1265, hlam, p1335_1]
                              · have p1335_0 := h1335c.1
                                have p1335_1 := h1335c.2.1
                                have p1335_2 := h1335c.2.2.1
                                have p1335_3 := h1335c.2.2.2
                                linarith only [hlam, p1335_0]
                            · linarith only [h1269, h1333, h1334, h460, hc01, hc24, hlam, hphi, ht12]
                          · linarith only [h1265, h1333, h635, hc34, hlam, hphi, ht23, u2ehi3]
                    · linarith only [h1265, h1328, h460, hlam]
                · linarith only [h0, h1268, h632, hc25, hlam, hphi, u2ehi2]
              · linarith only [h0, h1267, h634, hc24, hlam, hphi, u2ehi4]
            · linarith only [h0, h1266, h634, hc23, hlam, hphi, u2ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1401 | h1401
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1402 | h1402
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1403 | h1403
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1404 | h1404
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1405 | h1405
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1406 | h1406
                      · linarith only [h1265, h1401, h1404, h1405, h1406, h632, h635, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1408 | h1408
                        · linarith only [h1265, h1401, h1404, h1405, h1408, h632, h635, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1410 | h1410
                          · linarith only [h1265, h1410, h633, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1412 | h1412
                            · linarith only [h1265, h1412, h635, hc34, hlam, hphi, u3ehi0]
                            · linarith only [h1401, h1404, h1405, h1412, h632, h635, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h1404, h1405, h632, h635, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1416 | h1416
                    · linarith only [h1265, h1404, h1416, h632, h635, hc34, hlam, hphi, ht23, u2ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1418 | h1418
                      · linarith only [h1263, h1418, h632, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1420 | h1420
                        · linarith only [h1263, h1420, h632, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1422 | h1422
                          · linarith only [h1404, h1416, h1422, h328, h632, hc24, hlam, hphi, u2ehi2]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1424 | h1424
                            · linarith only [h1404, h1416, h1424, h328, h632, hc34, hlam, hphi, ht23, u2ehi2]
                            · linarith only [h1424, h632, h635, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                · linarith only [h0, h1403, h632, hc25, hlam, hphi, u2ehi2]
              · linarith only [h0, h1402, h633, hlam]
            · linarith only [h0, h1401, h632, h634, h635, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
    · linarith only [h633, h634, hc25, hlam, hphi, u2ehi3]
  · linarith only [h632, h633, hc24, hlam, hphi, u2ehi2]

end R2N4
