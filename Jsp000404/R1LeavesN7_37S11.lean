import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_37S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7332000 in
set_option maxHeartbeats 7332000 in
theorem r1l7_22_14_M_LI_L_I_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h4bigk := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h659 | h659
  · rcases m.htr 1 2 3 (by decide) (by decide) with h660 | h660
    · rcases m.htr 1 2 4 (by decide) (by decide) with h661 | h661
      · rcases m.htr 1 2 5 (by decide) (by decide) with h662 | h662
        · rcases m.htr 1 3 4 (by decide) (by decide) with h663 | h663
          · linarith only [h1, h6, h663, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h665 | h665
            · rcases m.htr 1 4 5 (by decide) (by decide) with h666 | h666
              · rcases m.htr 2 3 4 (by decide) (by decide) with h667 | h667
                · linarith only [h1, h6, h660, h665, h667, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h669 | h669
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h670 | h670
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h671 | h671
                      · rcases h2bigk with h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c | h672c
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [hlam, p672_0]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h661, h667, h669, h671, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p672_1, u2elo0]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h669, h671, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p672_1, u2elo0]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h667, h669, h671, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p672_1, u2elo0]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          rcases p672_3 (m.d 0 2) (by simp) with h677 | h677
                          · rcases p672_3 (m.d 1 2) (by simp) with h678 | h678
                            · linarith only [h0, h678, hlam]
                            · linarith only [h662, h678, hlam]
                          · linarith only [h677, hlam, p672_0]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h0, hlam, p672_0]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [hlam, p672_0]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h669, h671, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p672_1, u2elo1]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h0, h667, h669, h671, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p672_1, u2elo0]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          rcases p672_3 (m.d 0 2) (by simp) with h686 | h686
                          · rcases p672_3 (m.d 1 2) (by simp) with h687 | h687
                            · rcases p672_3 (m.d 2 3) (by simp) with h688 | h688
                              · linarith only [h660, h688, hlam]
                              · linarith only [h669, h688, hlam]
                            · linarith only [h687, hlam, p672_0]
                          · linarith only [h0, h686, hlam, p672_1]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h4, hlam, p672_0]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h660, hlam, p672_0]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [hlam, p672_0]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h667, hlam, p672_0]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p672_1, u2elo0]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h5, hlam, p672_0]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h661, hlam, p672_0]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h669, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p672_1, u2elo3]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [hlam, p672_0]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h5, h669, h671, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p672_1, u2elo0]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [hc02, hlam, hphi, p672_1, u2elo4]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h662, hlam, p672_0]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h669, hlam, p672_1]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [h670, hlam, p672_0]
                        · have p672_0 := h672c.1
                          have p672_1 := h672c.2.1
                          have p672_2 := h672c.2.2.1
                          have p672_3 := h672c.2.2.2
                          linarith only [hlam, p672_0]
                      · linarith only [h1, h6, h659, h660, h669, h671, hc04, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h5, h659, h667, h669, h670, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                  · linarith only [h1, h6, h665, h669, hc23, hc34, hlam, hphi]
              · linarith only [h5, h659, h663, h665, h666, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h712 | h712
              · rcases m.htr 2 3 4 (by decide) (by decide) with h713 | h713
                · linarith only [h6, h660, h665, h713, hc03, hc35, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h715 | h715
                  · linarith only [h0, h661, h665, h713, h715, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h717 | h717
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h718 | h718
                      · rcases h2bigk with h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c
                        · have p719_0 := h719c.1
                          have p719_1 := h719c.2.1
                          have p719_2 := h719c.2.2.1
                          have p719_3 := h719c.2.2.2
                          linarith only [hlam, p719_0]
                        · have p719_0 := h719c.1
                          have p719_1 := h719c.2.1
                          have p719_2 := h719c.2.2.1
                          have p719_3 := h719c.2.2.2
                          linarith only [hc12, hlam, hphi, p719_1, u2elo0]
                        · have p719_0 := h719c.1
                          have p719_1 := h719c.2.1
                          have p719_2 := h719c.2.2.1
                          have p719_3 := h719c.2.2.2
                          rcases p719_3 (m.d 0 2) (by simp) with h722 | h722
                          · rcases p719_3 (m.d 1 2) (by simp) with h723 | h723
                            · linarith only [h0, h723, hlam]
                            · linarith only [h660, h723, hlam]
                          · linarith only [h722, hlam, p719_0]
                        · have p719_0 := h719c.1
                          have p719_1 := h719c.2.1
                          have p719_2 := h719c.2.2.1
                          have p719_3 := h719c.2.2.2
                          linarith only [h717, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p719_1, u2elo0]
                        · have p719_0 := h719c.1
                          have p719_1 := h719c.2.1
                          have p719_2 := h719c.2.2.1
                          have p719_3 := h719c.2.2.2
                          rcases p719_3 (m.d 0 2) (by simp) with h728 | h728
                          · rcases p719_3 (m.d 1 2) (by simp) with h729 | h729
                            · linarith only [h0, h729, hlam]
                            · linarith only [h662, h729, hlam]
                          · linarith only [h728, hlam, p719_0]
                        · have p719_0 := h719c.1
                          have p719_1 := h719c.2.1
                          have p719_2 := h719c.2.2.1
                          have p719_3 := h719c.2.2.2
                          linarith only [h0, hlam, p719_0]
                        · have p719_0 := h719c.1
                          have p719_1 := h719c.2.1
                          have p719_2 := h719c.2.2.1
                          have p719_3 := h719c.2.2.2
                          linarith only [hlam, p719_0]
                        · have p719_0 := h719c.1
                          have p719_1 := h719c.2.1
                          have p719_2 := h719c.2.2.1
                          have p719_3 := h719c.2.2.2
                          rcases p719_3 (m.d 0 2) (by simp) with h735 | h735
                          · rcases p719_3 (m.d 1 2) (by simp) with h736 | h736
                            · rcases p719_3 (m.d 2 3) (by simp) with h737 | h737
                              · linarith only [h737, hlam, p719_0]
                              · rcases p719_3 (m.d 2 4) (by simp) with h739 | h739
                                · linarith only [h661, h739, hlam]
                                · linarith only [h713, h739, hlam]
                            · linarith only [h736, hlam, p719_0]
                          · linarith only [h4, h735, hlam]
                        · have p719_0 := h719c.1
                          have p719_1 := h719c.2.1
                          have p719_2 := h719c.2.2.1
                          have p719_3 := h719c.2.2.2
                          linarith only [h717, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p719_1, u2elo1]
                        · have p719_0 := h719c.1
                          have p719_1 := h719c.2.1
                          have p719_2 := h719c.2.2.1
                          have p719_3 := h719c.2.2.2
                          rcases p719_3 (m.d 0 2) (by simp) with h745 | h745
                          · rcases p719_3 (m.d 1 2) (by simp) with h746 | h746
                            · rcases p719_3 (m.d 2 3) (by simp) with h747 | h747
                              · linarith only [h660, h747, hlam]
                              · rcases p719_3 (m.d 2 4) (by simp) with h749 | h749
                                · linarith only [h661, h749, hlam]
                                · linarith only [h717, h749, hlam]
                            · linarith only [h746, hlam, p719_0]
                          · linarith only [h3, h5, h659, h662, h745, hlam]
                        · have p719_0 := h719c.1
                          have p719_1 := h719c.2.1
                          have p719_2 := h719c.2.2.1
                          have p719_3 := h719c.2.2.2
                          linarith only [h4, hlam, p719_0]
                        · have p719_0 := h719c.1
                          have p719_1 := h719c.2.1
                          have p719_2 := h719c.2.2.1
                          have p719_3 := h719c.2.2.2
                          linarith only [h660, hlam, p719_0]
                        · have p719_0 := h719c.1
                          have p719_1 := h719c.2.1
                          have p719_2 := h719c.2.2.1
                          have p719_3 := h719c.2.2.2
                          linarith only [hlam, p719_0]
                        · have p719_0 := h719c.1
                          have p719_1 := h719c.2.1
                          have p719_2 := h719c.2.2.1
                          have p719_3 := h719c.2.2.2
                          linarith only [h713, hlam, p719_0]
                        · have p719_0 := h719c.1
                          have p719_1 := h719c.2.1
                          have p719_2 := h719c.2.2.1
                          have p719_3 := h719c.2.2.2
                          linarith only [h715, hlam, p719_0]
                        · have p719_0 := h719c.1
                          have p719_1 := h719c.2.1
                          have p719_2 := h719c.2.2.1
                          have p719_3 := h719c.2.2.2
                          linarith only [h5, hlam, p719_0]
                        · have p719_0 := h719c.1
                          have p719_1 := h719c.2.1
                          have p719_2 := h719c.2.2.1
                          have p719_3 := h719c.2.2.2
                          linarith only [h661, hlam, p719_0]
                        · have p719_0 := h719c.1
                          have p719_1 := h719c.2.1
                          have p719_2 := h719c.2.2.1
                          have p719_3 := h719c.2.2.2
                          linarith only [h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p719_1, u2elo0]
                        · have p719_0 := h719c.1
                          have p719_1 := h719c.2.1
                          have p719_2 := h719c.2.2.1
                          have p719_3 := h719c.2.2.2
                          linarith only [hlam, p719_0]
                        · have p719_0 := h719c.1
                          have p719_1 := h719c.2.1
                          have p719_2 := h719c.2.2.1
                          have p719_3 := h719c.2.2.2
                          linarith only [h0, h661, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p719_1, u2elo0]
                        · have p719_0 := h719c.1
                          have p719_1 := h719c.2.1
                          have p719_2 := h719c.2.2.1
                          have p719_3 := h719c.2.2.2
                          linarith only [hc02, hlam, hphi, p719_1, u2elo4]
                        · have p719_0 := h719c.1
                          have p719_1 := h719c.2.1
                          have p719_2 := h719c.2.2.1
                          have p719_3 := h719c.2.2.2
                          linarith only [h662, hlam, p719_0]
                        · have p719_0 := h719c.1
                          have p719_1 := h719c.2.1
                          have p719_2 := h719c.2.2.1
                          have p719_3 := h719c.2.2.2
                          linarith only [h0, h662, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p719_1, u2elo0]
                        · have p719_0 := h719c.1
                          have p719_1 := h719c.2.1
                          have p719_2 := h719c.2.2.1
                          have p719_3 := h719c.2.2.2
                          linarith only [h717, hlam, p719_0]
                        · have p719_0 := h719c.1
                          have p719_1 := h719c.2.1
                          have p719_2 := h719c.2.2.1
                          have p719_3 := h719c.2.2.2
                          linarith only [hlam, p719_0]
                      · linarith only [h1, h6, h660, h717, h718, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h770 | h770
                      · rcases h2bigk with h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c
                        · have p771_0 := h771c.1
                          have p771_1 := h771c.2.1
                          have p771_2 := h771c.2.2.1
                          have p771_3 := h771c.2.2.2
                          linarith only [hlam, p771_0]
                        · have p771_0 := h771c.1
                          have p771_1 := h771c.2.1
                          have p771_2 := h771c.2.2.1
                          have p771_3 := h771c.2.2.2
                          linarith only [hc12, hlam, hphi, p771_1, u2elo0]
                        · have p771_0 := h771c.1
                          have p771_1 := h771c.2.1
                          have p771_2 := h771c.2.2.1
                          have p771_3 := h771c.2.2.2
                          rcases p771_3 (m.d 0 2) (by simp) with h774 | h774
                          · rcases p771_3 (m.d 1 2) (by simp) with h775 | h775
                            · linarith only [h0, h775, hlam]
                            · linarith only [h660, h775, hlam]
                          · linarith only [h774, hlam, p771_0]
                        · have p771_0 := h771c.1
                          have p771_1 := h771c.2.1
                          have p771_2 := h771c.2.2.1
                          have p771_3 := h771c.2.2.2
                          rcases p771_3 (m.d 0 2) (by simp) with h779 | h779
                          · rcases p771_3 (m.d 1 2) (by simp) with h780 | h780
                            · linarith only [h0, h780, hlam]
                            · linarith only [h661, h780, hlam]
                          · linarith only [h779, hlam, p771_0]
                        · have p771_0 := h771c.1
                          have p771_1 := h771c.2.1
                          have p771_2 := h771c.2.2.1
                          have p771_3 := h771c.2.2.2
                          rcases p771_3 (m.d 0 2) (by simp) with h784 | h784
                          · rcases p771_3 (m.d 1 2) (by simp) with h785 | h785
                            · linarith only [h0, h785, hlam]
                            · linarith only [h662, h785, hlam]
                          · linarith only [h784, hlam, p771_0]
                        · have p771_0 := h771c.1
                          have p771_1 := h771c.2.1
                          have p771_2 := h771c.2.2.1
                          have p771_3 := h771c.2.2.2
                          linarith only [h0, hlam, p771_0]
                        · have p771_0 := h771c.1
                          have p771_1 := h771c.2.1
                          have p771_2 := h771c.2.2.1
                          have p771_3 := h771c.2.2.2
                          linarith only [hlam, p771_0]
                        · have p771_0 := h771c.1
                          have p771_1 := h771c.2.1
                          have p771_2 := h771c.2.2.1
                          have p771_3 := h771c.2.2.2
                          rcases p771_3 (m.d 0 2) (by simp) with h791 | h791
                          · rcases p771_3 (m.d 1 2) (by simp) with h792 | h792
                            · rcases p771_3 (m.d 2 3) (by simp) with h793 | h793
                              · linarith only [h793, hlam, p771_0]
                              · rcases p771_3 (m.d 2 4) (by simp) with h795 | h795
                                · linarith only [h661, h795, hlam]
                                · linarith only [h713, h795, hlam]
                            · linarith only [h792, hlam, p771_0]
                          · linarith only [h4, h791, hlam]
                        · have p771_0 := h771c.1
                          have p771_1 := h771c.2.1
                          have p771_2 := h771c.2.2.1
                          have p771_3 := h771c.2.2.2
                          rcases p771_3 (m.d 0 2) (by simp) with h800 | h800
                          · rcases p771_3 (m.d 1 2) (by simp) with h801 | h801
                            · rcases p771_3 (m.d 2 3) (by simp) with h802 | h802
                              · linarith only [h660, h802, hlam]
                              · rcases p771_3 (m.d 2 4) (by simp) with h804 | h804
                                · linarith only [h804, hlam, p771_0]
                                · rcases p771_3 (m.d 2 5) (by simp) with h806 | h806
                                  · linarith only [h662, h806, hlam]
                                  · linarith only [h717, h806, hlam]
                            · linarith only [h801, hlam, p771_0]
                          · linarith only [h5, h800, hlam]
                        · have p771_0 := h771c.1
                          have p771_1 := h771c.2.1
                          have p771_2 := h771c.2.2.1
                          have p771_3 := h771c.2.2.2
                          rcases p771_3 (m.d 0 2) (by simp) with h811 | h811
                          · rcases p771_3 (m.d 1 2) (by simp) with h812 | h812
                            · rcases p771_3 (m.d 2 3) (by simp) with h813 | h813
                              · linarith only [h660, h813, hlam]
                              · rcases p771_3 (m.d 2 4) (by simp) with h815 | h815
                                · linarith only [h661, h815, hlam]
                                · rcases p771_3 (m.d 2 5) (by simp) with h817 | h817
                                  · linarith only [h817, hlam, p771_0]
                                  · rcases h4bigk with h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c
                                    · have p819_0 := h819c.1
                                      have p819_1 := h819c.2.1
                                      have p819_2 := h819c.2.2.1
                                      have p819_3 := h819c.2.2.2
                                      linarith only [hlam, p819_0]
                                    · have p819_0 := h819c.1
                                      have p819_1 := h819c.2.1
                                      have p819_2 := h819c.2.2.1
                                      have p819_3 := h819c.2.2.2
                                      linarith only [h5, h712, h717, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p819_1, u2elo0]
                                    · have p819_0 := h819c.1
                                      have p819_1 := h819c.2.1
                                      have p819_2 := h819c.2.2.1
                                      have p819_3 := h819c.2.2.2
                                      rcases p819_3 (m.d 0 4) (by simp) with h822 | h822
                                      · rcases p819_3 (m.d 1 4) (by simp) with h823 | h823
                                        · linarith only [h2, h823, hlam]
                                        · linarith only [h661, h823, hlam]
                                      · linarith only [h5, h822, hlam]
                                    · have p819_0 := h819c.1
                                      have p819_1 := h819c.2.1
                                      have p819_2 := h819c.2.2.1
                                      have p819_3 := h819c.2.2.2
                                      linarith only [h6, hlam, p819_0]
                                    · have p819_0 := h819c.1
                                      have p819_1 := h819c.2.1
                                      have p819_2 := h819c.2.2.1
                                      have p819_3 := h819c.2.2.2
                                      linarith only [h5, h713, h717, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p819_1, u2elo0]
                                    · have p819_0 := h819c.1
                                      have p819_1 := h819c.2.1
                                      have p819_2 := h819c.2.2.1
                                      have p819_3 := h819c.2.2.2
                                      linarith only [h2, hlam, p819_1]
                                    · have p819_0 := h819c.1
                                      have p819_1 := h819c.2.1
                                      have p819_2 := h819c.2.2.1
                                      have p819_3 := h819c.2.2.2
                                      linarith only [hlam, p819_0]
                                    · have p819_0 := h819c.1
                                      have p819_1 := h819c.2.1
                                      have p819_2 := h819c.2.2.1
                                      have p819_3 := h819c.2.2.2
                                      rcases p819_3 (m.d 0 4) (by simp) with h831 | h831
                                      · rcases p819_3 (m.d 1 4) (by simp) with h832 | h832
                                        · rcases p819_3 (m.d 2 4) (by simp) with h833 | h833
                                          · linarith only [h661, h833, hlam]
                                          · rcases p819_3 (m.d 3 4) (by simp) with h835 | h835
                                            · rcases p819_3 (m.d 4 5) (by simp) with h836 | h836
                                              · linarith only [h712, h836, hlam]
                                              · linarith only [h717, h836, hlam]
                                            · linarith only [h713, h835, hlam]
                                        · linarith only [h661, h832, hlam]
                                      · linarith only [h5, h831, hlam]
                                    · have p819_0 := h819c.1
                                      have p819_1 := h819c.2.1
                                      have p819_2 := h819c.2.2.1
                                      have p819_3 := h819c.2.2.2
                                      linarith only [h663, hlam, p819_1]
                                    · have p819_0 := h819c.1
                                      have p819_1 := h819c.2.1
                                      have p819_2 := h819c.2.2.1
                                      have p819_3 := h819c.2.2.2
                                      linarith only [h661, h713, h717, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p819_1, u2elo1]
                                    · have p819_0 := h819c.1
                                      have p819_1 := h819c.2.1
                                      have p819_2 := h819c.2.2.1
                                      have p819_3 := h819c.2.2.2
                                      linarith only [h5, hlam, p819_1]
                                    · have p819_0 := h819c.1
                                      have p819_1 := h819c.2.1
                                      have p819_2 := h819c.2.2.1
                                      have p819_3 := h819c.2.2.2
                                      linarith only [h661, hlam, p819_1]
                                    · have p819_0 := h819c.1
                                      have p819_1 := h819c.2.1
                                      have p819_2 := h819c.2.2.1
                                      have p819_3 := h819c.2.2.2
                                      linarith only [hlam, p819_0]
                                    · have p819_0 := h819c.1
                                      have p819_1 := h819c.2.1
                                      have p819_2 := h819c.2.2.1
                                      have p819_3 := h819c.2.2.2
                                      linarith only [h713, hlam, p819_1]
                                    · have p819_0 := h819c.1
                                      have p819_1 := h819c.2.1
                                      have p819_2 := h819c.2.2.1
                                      have p819_3 := h819c.2.2.2
                                      linarith only [h717, hlam, p819_0]
                                    · have p819_0 := h819c.1
                                      have p819_1 := h819c.2.1
                                      have p819_2 := h819c.2.2.1
                                      have p819_3 := h819c.2.2.2
                                      linarith only [h659, h713, h717, hc23, hc34, hlam, hphi, p819_1]
                                    · have p819_0 := h819c.1
                                      have p819_1 := h819c.2.1
                                      have p819_2 := h819c.2.2.1
                                      have p819_3 := h819c.2.2.2
                                      linarith only [h712, h713, h717, hc23, hc34, hlam, hphi, p819_1]
                                    · have p819_0 := h819c.1
                                      have p819_1 := h819c.2.1
                                      have p819_2 := h819c.2.2.1
                                      have p819_3 := h819c.2.2.2
                                      rcases p819_3 (m.d 0 4) (by simp) with h851 | h851
                                      · linarith only [h6, h851, hlam]
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
                                      linarith only [h713, h717, hc23, hc34, hlam, hphi, p819_1]
                                    · have p819_0 := h819c.1
                                      have p819_1 := h819c.2.1
                                      have p819_2 := h819c.2.2.1
                                      have p819_3 := h819c.2.2.2
                                      linarith only [h659, hlam, p819_0]
                                    · have p819_0 := h819c.1
                                      have p819_1 := h819c.2.1
                                      have p819_2 := h819c.2.2.1
                                      have p819_3 := h819c.2.2.2
                                      linarith only [h712, hlam, p819_0]
                                    · have p819_0 := h819c.1
                                      have p819_1 := h819c.2.1
                                      have p819_2 := h819c.2.2.1
                                      have p819_3 := h819c.2.2.2
                                      linarith only [h2, h712, h713, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p819_1]
                                    · have p819_0 := h819c.1
                                      have p819_1 := h819c.2.1
                                      have p819_2 := h819c.2.2.1
                                      have p819_3 := h819c.2.2.2
                                      linarith only [h770, hlam, p819_0]
                                    · have p819_0 := h819c.1
                                      have p819_1 := h819c.2.1
                                      have p819_2 := h819c.2.2.1
                                      have p819_3 := h819c.2.2.2
                                      linarith only [hlam, p819_0]
                            · linarith only [h812, hlam, p771_0]
                          · linarith only [h0, h811, hlam, p771_1]
                        · have p771_0 := h771c.1
                          have p771_1 := h771c.2.1
                          have p771_2 := h771c.2.2.1
                          have p771_3 := h771c.2.2.2
                          linarith only [h4, hlam, p771_0]
                        · have p771_0 := h771c.1
                          have p771_1 := h771c.2.1
                          have p771_2 := h771c.2.2.1
                          have p771_3 := h771c.2.2.2
                          linarith only [h660, hlam, p771_0]
                        · have p771_0 := h771c.1
                          have p771_1 := h771c.2.1
                          have p771_2 := h771c.2.2.1
                          have p771_3 := h771c.2.2.2
                          linarith only [hlam, p771_0]
                        · have p771_0 := h771c.1
                          have p771_1 := h771c.2.1
                          have p771_2 := h771c.2.2.1
                          have p771_3 := h771c.2.2.2
                          linarith only [h713, hlam, p771_0]
                        · have p771_0 := h771c.1
                          have p771_1 := h771c.2.1
                          have p771_2 := h771c.2.2.1
                          have p771_3 := h771c.2.2.2
                          linarith only [h715, hlam, p771_0]
                        · have p771_0 := h771c.1
                          have p771_1 := h771c.2.1
                          have p771_2 := h771c.2.2.1
                          have p771_3 := h771c.2.2.2
                          linarith only [h5, hlam, p771_0]
                        · have p771_0 := h771c.1
                          have p771_1 := h771c.2.1
                          have p771_2 := h771c.2.2.1
                          have p771_3 := h771c.2.2.2
                          linarith only [h661, hlam, p771_0]
                        · have p771_0 := h771c.1
                          have p771_1 := h771c.2.1
                          have p771_2 := h771c.2.2.1
                          have p771_3 := h771c.2.2.2
                          linarith only [h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p771_1, u2elo0]
                        · have p771_0 := h771c.1
                          have p771_1 := h771c.2.1
                          have p771_2 := h771c.2.2.1
                          have p771_3 := h771c.2.2.2
                          linarith only [hlam, p771_0]
                        · have p771_0 := h771c.1
                          have p771_1 := h771c.2.1
                          have p771_2 := h771c.2.2.1
                          have p771_3 := h771c.2.2.2
                          linarith only [h717, hlam, p771_1]
                        · have p771_0 := h771c.1
                          have p771_1 := h771c.2.1
                          have p771_2 := h771c.2.2.1
                          have p771_3 := h771c.2.2.2
                          linarith only [h2, h5, h712, h717, hlam, p771_1]
                        · have p771_0 := h771c.1
                          have p771_1 := h771c.2.1
                          have p771_2 := h771c.2.2.1
                          have p771_3 := h771c.2.2.2
                          linarith only [h662, hlam, p771_0]
                        · have p771_0 := h771c.1
                          have p771_1 := h771c.2.1
                          have p771_2 := h771c.2.2.1
                          have p771_3 := h771c.2.2.2
                          linarith only [h2, h5, h712, h717, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p771_1, u2elo0]
                        · have p771_0 := h771c.1
                          have p771_1 := h771c.2.1
                          have p771_2 := h771c.2.2.1
                          have p771_3 := h771c.2.2.2
                          linarith only [h2, h5, h712, h717, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p771_1, u2elo0]
                        · have p771_0 := h771c.1
                          have p771_1 := h771c.2.1
                          have p771_2 := h771c.2.2.1
                          have p771_3 := h771c.2.2.2
                          linarith only [hlam, p771_0]
                      · linarith only [h1, h2, h5, h6, h660, h712, h770, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h879 | h879
                · linarith only [h6, h659, h712, h879, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h881 | h881
                  · linarith only [h5, h659, h660, h663, h712, h881, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h883 | h883
                    · linarith only [h5, h663, h712, h883, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h885 | h885
                      · rcases h2bigk with h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [hlam, p886_0]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [hc12, hlam, hphi, p886_1, u2elo0]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          rcases p886_3 (m.d 0 2) (by simp) with h889 | h889
                          · rcases p886_3 (m.d 1 2) (by simp) with h890 | h890
                            · linarith only [h0, h890, hlam]
                            · linarith only [h660, h890, hlam]
                          · linarith only [h889, hlam, p886_0]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          rcases p886_3 (m.d 0 2) (by simp) with h894 | h894
                          · rcases p886_3 (m.d 1 2) (by simp) with h895 | h895
                            · linarith only [h0, h895, hlam]
                            · linarith only [h661, h895, hlam]
                          · linarith only [h894, hlam, p886_0]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          rcases p886_3 (m.d 0 2) (by simp) with h899 | h899
                          · rcases p886_3 (m.d 1 2) (by simp) with h900 | h900
                            · linarith only [h0, h900, hlam]
                            · linarith only [h662, h900, hlam]
                          · linarith only [h899, hlam, p886_0]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [h0, hlam, p886_0]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [hlam, p886_0]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          rcases p886_3 (m.d 0 2) (by simp) with h906 | h906
                          · rcases p886_3 (m.d 1 2) (by simp) with h907 | h907
                            · rcases p886_3 (m.d 2 3) (by simp) with h908 | h908
                              · linarith only [h908, hlam, p886_0]
                              · rcases p886_3 (m.d 2 4) (by simp) with h910 | h910
                                · linarith only [h661, h910, hlam]
                                · linarith only [h879, h910, hlam]
                            · linarith only [h907, hlam, p886_0]
                          · linarith only [h4, h906, hlam]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          rcases p886_3 (m.d 0 2) (by simp) with h915 | h915
                          · rcases p886_3 (m.d 1 2) (by simp) with h916 | h916
                            · rcases p886_3 (m.d 2 3) (by simp) with h917 | h917
                              · linarith only [h660, h917, hlam]
                              · rcases p886_3 (m.d 2 4) (by simp) with h919 | h919
                                · linarith only [h919, hlam, p886_0]
                                · rcases p886_3 (m.d 2 5) (by simp) with h921 | h921
                                  · linarith only [h662, h921, hlam]
                                  · linarith only [h883, h921, hlam]
                            · linarith only [h916, hlam, p886_0]
                          · linarith only [h5, h915, hlam]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          rcases p886_3 (m.d 0 2) (by simp) with h926 | h926
                          · rcases p886_3 (m.d 1 2) (by simp) with h927 | h927
                            · rcases p886_3 (m.d 2 3) (by simp) with h928 | h928
                              · linarith only [h660, h928, hlam]
                              · rcases p886_3 (m.d 2 4) (by simp) with h930 | h930
                                · linarith only [h661, h930, hlam]
                                · rcases p886_3 (m.d 2 5) (by simp) with h932 | h932
                                  · linarith only [h932, hlam, p886_0]
                                  · rcases h4bigk with h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c
                                    · have p934_0 := h934c.1
                                      have p934_1 := h934c.2.1
                                      have p934_2 := h934c.2.2.1
                                      have p934_3 := h934c.2.2.2
                                      linarith only [hlam, p934_0]
                                    · have p934_0 := h934c.1
                                      have p934_1 := h934c.2.1
                                      have p934_2 := h934c.2.2.1
                                      have p934_3 := h934c.2.2.2
                                      rcases p934_3 (m.d 0 4) (by simp) with h936 | h936
                                      · rcases p934_3 (m.d 1 4) (by simp) with h937 | h937
                                        · linarith only [h2, h937, hlam]
                                        · rcases p934_3 (m.d 2 4) (by simp) with h939 | h939
                                          · linarith only [h5, h939, hlam]
                                          · rcases p934_3 (m.d 3 4) (by simp) with h941 | h941
                                            · rcases p934_3 (m.d 4 5) (by simp) with h942 | h942
                                              · linarith only [h659, h942, hlam]
                                              · linarith only [h712, h942, hlam]
                                            · linarith only [h663, h941, hlam]
                                      · linarith only [h2, h936, hlam]
                                    · have p934_0 := h934c.1
                                      have p934_1 := h934c.2.1
                                      have p934_2 := h934c.2.2.1
                                      have p934_3 := h934c.2.2.2
                                      rcases p934_3 (m.d 0 4) (by simp) with h947 | h947
                                      · rcases p934_3 (m.d 1 4) (by simp) with h948 | h948
                                        · linarith only [h2, h948, hlam]
                                        · linarith only [h661, h948, hlam]
                                      · linarith only [h5, h947, hlam]
                                    · have p934_0 := h934c.1
                                      have p934_1 := h934c.2.1
                                      have p934_2 := h934c.2.2.1
                                      have p934_3 := h934c.2.2.2
                                      linarith only [h6, hlam, p934_0]
                                    · have p934_0 := h934c.1
                                      have p934_1 := h934c.2.1
                                      have p934_2 := h934c.2.2.1
                                      have p934_3 := h934c.2.2.2
                                      linarith only [h6, h660, h663, h712, hc23, hc34, hlam, hphi, p934_1]
                                    · have p934_0 := h934c.1
                                      have p934_1 := h934c.2.1
                                      have p934_2 := h934c.2.2.1
                                      have p934_3 := h934c.2.2.2
                                      linarith only [h2, hlam, p934_1]
                                    · have p934_0 := h934c.1
                                      have p934_1 := h934c.2.1
                                      have p934_2 := h934c.2.2.1
                                      have p934_3 := h934c.2.2.2
                                      linarith only [hlam, p934_0]
                                    · have p934_0 := h934c.1
                                      have p934_1 := h934c.2.1
                                      have p934_2 := h934c.2.2.1
                                      have p934_3 := h934c.2.2.2
                                      linarith only [h712, h879, h885, hc23, hc35, hlam, hphi, p934_1]
                                    · have p934_0 := h934c.1
                                      have p934_1 := h934c.2.1
                                      have p934_2 := h934c.2.2.1
                                      have p934_3 := h934c.2.2.2
                                      linarith only [h663, hlam, p934_1]
                                    · have p934_0 := h934c.1
                                      have p934_1 := h934c.2.1
                                      have p934_2 := h934c.2.2.1
                                      have p934_3 := h934c.2.2.2
                                      linarith only [h712, hlam, p934_0]
                                    · have p934_0 := h934c.1
                                      have p934_1 := h934c.2.1
                                      have p934_2 := h934c.2.2.1
                                      have p934_3 := h934c.2.2.2
                                      linarith only [h5, hlam, p934_1]
                                    · have p934_0 := h934c.1
                                      have p934_1 := h934c.2.1
                                      have p934_2 := h934c.2.2.1
                                      have p934_3 := h934c.2.2.2
                                      linarith only [h661, hlam, p934_1]
                                    · have p934_0 := h934c.1
                                      have p934_1 := h934c.2.1
                                      have p934_2 := h934c.2.2.1
                                      have p934_3 := h934c.2.2.2
                                      linarith only [hlam, p934_0]
                                    · have p934_0 := h934c.1
                                      have p934_1 := h934c.2.1
                                      have p934_2 := h934c.2.2.1
                                      have p934_3 := h934c.2.2.2
                                      linarith only [h879, hlam, p934_1]
                                    · have p934_0 := h934c.1
                                      have p934_1 := h934c.2.1
                                      have p934_2 := h934c.2.2.1
                                      have p934_3 := h934c.2.2.2
                                      linarith only [h883, hlam, p934_0]
                                    · have p934_0 := h934c.1
                                      have p934_1 := h934c.2.1
                                      have p934_2 := h934c.2.2.1
                                      have p934_3 := h934c.2.2.2
                                      linarith only [h659, h712, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p934_1]
                                    · have p934_0 := h934c.1
                                      have p934_1 := h934c.2.1
                                      have p934_2 := h934c.2.2.1
                                      have p934_3 := h934c.2.2.2
                                      rcases p934_3 (m.d 0 4) (by simp) with h965 | h965
                                      · linarith only [h6, h965, hlam]
                                      · linarith only [h2, h965, hlam]
                                    · have p934_0 := h934c.1
                                      have p934_1 := h934c.2.1
                                      have p934_2 := h934c.2.2.1
                                      have p934_3 := h934c.2.2.2
                                      rcases p934_3 (m.d 0 4) (by simp) with h968 | h968
                                      · linarith only [h6, h968, hlam]
                                      · linarith only [h5, h968, hlam]
                                    · have p934_0 := h934c.1
                                      have p934_1 := h934c.2.1
                                      have p934_2 := h934c.2.2.1
                                      have p934_3 := h934c.2.2.2
                                      linarith only [hlam, p934_0]
                                    · have p934_0 := h934c.1
                                      have p934_1 := h934c.2.1
                                      have p934_2 := h934c.2.2.1
                                      have p934_3 := h934c.2.2.2
                                      linarith only [h661, h712, h879, hc23, hc34, hlam, hphi, p934_1]
                                    · have p934_0 := h934c.1
                                      have p934_1 := h934c.2.1
                                      have p934_2 := h934c.2.2.1
                                      have p934_3 := h934c.2.2.2
                                      linarith only [h659, hlam, p934_0]
                                    · have p934_0 := h934c.1
                                      have p934_1 := h934c.2.1
                                      have p934_2 := h934c.2.2.1
                                      have p934_3 := h934c.2.2.2
                                      linarith only [h5, h659, h661, h879, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p934_1, u2elo0]
                                    · have p934_0 := h934c.1
                                      have p934_1 := h934c.2.1
                                      have p934_2 := h934c.2.2.1
                                      have p934_3 := h934c.2.2.2
                                      linarith only [h5, h659, h879, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p934_1, u2elo0]
                                    · have p934_0 := h934c.1
                                      have p934_1 := h934c.2.1
                                      have p934_2 := h934c.2.2.1
                                      have p934_3 := h934c.2.2.2
                                      linarith only [h885, hlam, p934_0]
                                    · have p934_0 := h934c.1
                                      have p934_1 := h934c.2.1
                                      have p934_2 := h934c.2.2.1
                                      have p934_3 := h934c.2.2.2
                                      linarith only [hlam, p934_0]
                            · linarith only [h927, hlam, p886_0]
                          · linarith only [h926, hc02, hlam, hphi, p886_1, u2elo1]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [h4, hlam, p886_0]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [h660, hlam, p886_0]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [hlam, p886_0]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [h879, hlam, p886_0]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [h881, hlam, p886_0]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [h5, hlam, p886_0]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [h661, hlam, p886_0]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p886_1, u2elo0]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [hlam, p886_0]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [h883, hlam, p886_1]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [hc02, hlam, hphi, p886_1, u2elo4]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [h662, hlam, p886_0]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [h662, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p886_1, u2elo1]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [h0, h662, h879, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p886_1, u2elo0]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [hlam, p886_0]
                      · linarith only [h1, h5, h6, h659, h660, h885, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h996 | h996
          · linarith only [h1, h6, h996, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h998 | h998
            · linarith only [h660, h662, h998, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1000 | h1000
              · linarith only [h1000, h661, h662, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1002 | h1002
                · linarith only [h1000, h1002, h5, h6, h659, h660, h996, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1004 | h1004
                  · linarith only [h1004, h4, h662, h998, hc12, hlam, hphi, u2elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1006 | h1006
                    · linarith only [h1000, h1006, h661, h662, h996, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · linarith only [h1006, h5, h659, h662, hc12, hlam, hphi, u2elo0]
      · linarith only [h5, h660, h661, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
    · linarith only [h4, h660, hc12, hlam, hphi, u2elo0]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1011 | h1011
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1012 | h1012
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1013 | h1013
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1014 | h1014
          · linarith only [h1, h1014, h6, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1016 | h1016
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1017 | h1017
              · linarith only [h1017, h2, h659, hlam]
              · linarith only [h1014, h1016, h1017, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1020 | h1020
              · linarith only [h1020, h2, h659, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1022 | h1022
                · linarith only [h1, h1011, h1022, h6, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1024 | h1024
                  · linarith only [h1011, h1016, h1024, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1026 | h1026
                    · linarith only [h0, h1012, h1026, h6, h659, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1028 | h1028
                      · rcases h2bigk with h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c
                        · have p1029_0 := h1029c.1
                          have p1029_1 := h1029c.2.1
                          have p1029_2 := h1029c.2.2.1
                          have p1029_3 := h1029c.2.2.2
                          linarith only [hlam, p1029_0]
                        · have p1029_0 := h1029c.1
                          have p1029_1 := h1029c.2.1
                          have p1029_2 := h1029c.2.2.1
                          have p1029_3 := h1029c.2.2.2
                          linarith only [hc12, hlam, hphi, p1029_1, u2elo0]
                        · have p1029_0 := h1029c.1
                          have p1029_1 := h1029c.2.1
                          have p1029_2 := h1029c.2.2.1
                          have p1029_3 := h1029c.2.2.2
                          rcases p1029_3 (m.d 0 2) (by simp) with h1032 | h1032
                          · rcases p1029_3 (m.d 1 2) (by simp) with h1033 | h1033
                            · linarith only [h0, h1033, hlam]
                            · linarith only [h1011, h1033, hlam]
                          · linarith only [h1032, hlam, p1029_0]
                        · have p1029_0 := h1029c.1
                          have p1029_1 := h1029c.2.1
                          have p1029_2 := h1029c.2.2.1
                          have p1029_3 := h1029c.2.2.2
                          rcases p1029_3 (m.d 0 2) (by simp) with h1037 | h1037
                          · rcases p1029_3 (m.d 1 2) (by simp) with h1038 | h1038
                            · linarith only [h0, h1038, hlam]
                            · linarith only [h1012, h1038, hlam]
                          · linarith only [h1037, hlam, p1029_0]
                        · have p1029_0 := h1029c.1
                          have p1029_1 := h1029c.2.1
                          have p1029_2 := h1029c.2.2.1
                          have p1029_3 := h1029c.2.2.2
                          rcases p1029_3 (m.d 0 2) (by simp) with h1042 | h1042
                          · rcases p1029_3 (m.d 1 2) (by simp) with h1043 | h1043
                            · linarith only [h0, h1043, hlam]
                            · linarith only [h1013, h1043, hlam]
                          · linarith only [h1042, hlam, p1029_0]
                        · have p1029_0 := h1029c.1
                          have p1029_1 := h1029c.2.1
                          have p1029_2 := h1029c.2.2.1
                          have p1029_3 := h1029c.2.2.2
                          linarith only [h0, hlam, p1029_0]
                        · have p1029_0 := h1029c.1
                          have p1029_1 := h1029c.2.1
                          have p1029_2 := h1029c.2.2.1
                          have p1029_3 := h1029c.2.2.2
                          linarith only [hlam, p1029_0]
                        · have p1029_0 := h1029c.1
                          have p1029_1 := h1029c.2.1
                          have p1029_2 := h1029c.2.2.1
                          have p1029_3 := h1029c.2.2.2
                          rcases p1029_3 (m.d 0 2) (by simp) with h1049 | h1049
                          · rcases p1029_3 (m.d 1 2) (by simp) with h1050 | h1050
                            · rcases p1029_3 (m.d 2 3) (by simp) with h1051 | h1051
                              · linarith only [h1051, hlam, p1029_0]
                              · rcases p1029_3 (m.d 2 4) (by simp) with h1053 | h1053
                                · linarith only [h1012, h1053, hlam]
                                · linarith only [h1022, h1053, hlam]
                            · linarith only [h1050, hlam, p1029_0]
                          · linarith only [h1049, h4, hlam]
                        · have p1029_0 := h1029c.1
                          have p1029_1 := h1029c.2.1
                          have p1029_2 := h1029c.2.2.1
                          have p1029_3 := h1029c.2.2.2
                          rcases p1029_3 (m.d 0 2) (by simp) with h1058 | h1058
                          · rcases p1029_3 (m.d 1 2) (by simp) with h1059 | h1059
                            · rcases p1029_3 (m.d 2 3) (by simp) with h1060 | h1060
                              · linarith only [h1011, h1060, hlam]
                              · rcases p1029_3 (m.d 2 4) (by simp) with h1062 | h1062
                                · linarith only [h1062, hlam, p1029_0]
                                · rcases p1029_3 (m.d 2 5) (by simp) with h1064 | h1064
                                  · linarith only [h1013, h1064, hlam]
                                  · linarith only [h1026, h1064, hlam]
                            · linarith only [h1059, hlam, p1029_0]
                          · linarith only [h1058, h5, hlam]
                        · have p1029_0 := h1029c.1
                          have p1029_1 := h1029c.2.1
                          have p1029_2 := h1029c.2.2.1
                          have p1029_3 := h1029c.2.2.2
                          rcases p1029_3 (m.d 0 2) (by simp) with h1069 | h1069
                          · rcases p1029_3 (m.d 1 2) (by simp) with h1070 | h1070
                            · rcases p1029_3 (m.d 2 3) (by simp) with h1071 | h1071
                              · linarith only [h1011, h1071, hlam]
                              · rcases p1029_3 (m.d 2 4) (by simp) with h1073 | h1073
                                · linarith only [h1012, h1073, hlam]
                                · rcases p1029_3 (m.d 2 5) (by simp) with h1075 | h1075
                                  · linarith only [h1075, hlam, p1029_0]
                                  · rcases h4bigk with h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c
                                    · have p1077_0 := h1077c.1
                                      have p1077_1 := h1077c.2.1
                                      have p1077_2 := h1077c.2.2.1
                                      have p1077_3 := h1077c.2.2.2
                                      linarith only [hlam, p1077_0]
                                    · have p1077_0 := h1077c.1
                                      have p1077_1 := h1077c.2.1
                                      have p1077_2 := h1077c.2.2.1
                                      have p1077_3 := h1077c.2.2.2
                                      linarith only [h1011, h1014, h1028, h659, hc23, hc34, hlam, hphi, p1077_1]
                                    · have p1077_0 := h1077c.1
                                      have p1077_1 := h1077c.2.1
                                      have p1077_2 := h1077c.2.2.1
                                      have p1077_3 := h1077c.2.2.2
                                      linarith only [h1022, h1028, h659, hc23, hc34, hlam, hphi, p1077_1]
                                    · have p1077_0 := h1077c.1
                                      have p1077_1 := h1077c.2.1
                                      have p1077_2 := h1077c.2.2.1
                                      have p1077_3 := h1077c.2.2.2
                                      linarith only [h6, hlam, p1077_0]
                                    · have p1077_0 := h1077c.1
                                      have p1077_1 := h1077c.2.1
                                      have p1077_2 := h1077c.2.2.1
                                      have p1077_3 := h1077c.2.2.2
                                      linarith only [h659, hlam, p1077_0]
                                    · have p1077_0 := h1077c.1
                                      have p1077_1 := h1077c.2.1
                                      have p1077_2 := h1077c.2.2.1
                                      have p1077_3 := h1077c.2.2.2
                                      linarith only [h2, hlam, p1077_1]
                                    · have p1077_0 := h1077c.1
                                      have p1077_1 := h1077c.2.1
                                      have p1077_2 := h1077c.2.2.1
                                      have p1077_3 := h1077c.2.2.2
                                      linarith only [hlam, p1077_0]
                                    · have p1077_0 := h1077c.1
                                      have p1077_1 := h1077c.2.1
                                      have p1077_2 := h1077c.2.2.1
                                      have p1077_3 := h1077c.2.2.2
                                      linarith only [h1022, h1028, h2, h659, hc23, hc34, hlam, hphi, p1077_1]
                                    · have p1077_0 := h1077c.1
                                      have p1077_1 := h1077c.2.1
                                      have p1077_2 := h1077c.2.2.1
                                      have p1077_3 := h1077c.2.2.2
                                      linarith only [h1014, hlam, p1077_1]
                                    · have p1077_0 := h1077c.1
                                      have p1077_1 := h1077c.2.1
                                      have p1077_2 := h1077c.2.2.1
                                      have p1077_3 := h1077c.2.2.2
                                      linarith only [h1020, hlam, p1077_0]
                                    · have p1077_0 := h1077c.1
                                      have p1077_1 := h1077c.2.1
                                      have p1077_2 := h1077c.2.2.1
                                      have p1077_3 := h1077c.2.2.2
                                      linarith only [h5, hlam, p1077_1]
                                    · have p1077_0 := h1077c.1
                                      have p1077_1 := h1077c.2.1
                                      have p1077_2 := h1077c.2.2.1
                                      have p1077_3 := h1077c.2.2.2
                                      linarith only [h1012, hlam, p1077_1]
                                    · have p1077_0 := h1077c.1
                                      have p1077_1 := h1077c.2.1
                                      have p1077_2 := h1077c.2.2.1
                                      have p1077_3 := h1077c.2.2.2
                                      linarith only [hlam, p1077_0]
                                    · have p1077_0 := h1077c.1
                                      have p1077_1 := h1077c.2.1
                                      have p1077_2 := h1077c.2.2.1
                                      have p1077_3 := h1077c.2.2.2
                                      linarith only [h1022, hlam, p1077_1]
                                    · have p1077_0 := h1077c.1
                                      have p1077_1 := h1077c.2.1
                                      have p1077_2 := h1077c.2.2.1
                                      have p1077_3 := h1077c.2.2.2
                                      linarith only [h1026, hlam, p1077_0]
                                    · have p1077_0 := h1077c.1
                                      have p1077_1 := h1077c.2.1
                                      have p1077_2 := h1077c.2.2.1
                                      have p1077_3 := h1077c.2.2.2
                                      rcases p1077_3 (m.d 0 4) (by simp) with h1093 | h1093
                                      · linarith only [h1093, h6, hlam]
                                      · rcases p1077_3 (m.d 1 4) (by simp) with h1095 | h1095
                                        · linarith only [h1014, h1095, hlam]
                                        · rcases p1077_3 (m.d 2 4) (by simp) with h1097 | h1097
                                          · linarith only [h1022, h1097, hlam]
                                          · rcases p1077_3 (m.d 3 4) (by simp) with h1099 | h1099
                                            · rcases p1077_3 (m.d 4 5) (by simp) with h1100 | h1100
                                              · linarith only [h1028, h1100, hlam]
                                              · linarith only [h1100, h659, hlam]
                                            · linarith only [h1099, h6, hlam]
                                    · have p1077_0 := h1077c.1
                                      have p1077_1 := h1077c.2.1
                                      have p1077_2 := h1077c.2.2.1
                                      have p1077_3 := h1077c.2.2.2
                                      rcases p1077_3 (m.d 0 4) (by simp) with h1104 | h1104
                                      · linarith only [h1104, h6, hlam]
                                      · linarith only [h1104, h2, hlam]
                                    · have p1077_0 := h1077c.1
                                      have p1077_1 := h1077c.2.1
                                      have p1077_2 := h1077c.2.2.1
                                      have p1077_3 := h1077c.2.2.2
                                      rcases p1077_3 (m.d 0 4) (by simp) with h1107 | h1107
                                      · linarith only [h1107, h6, hlam]
                                      · linarith only [h1107, h5, hlam]
                                    · have p1077_0 := h1077c.1
                                      have p1077_1 := h1077c.2.1
                                      have p1077_2 := h1077c.2.2.1
                                      have p1077_3 := h1077c.2.2.2
                                      linarith only [hlam, p1077_0]
                                    · have p1077_0 := h1077c.1
                                      have p1077_1 := h1077c.2.1
                                      have p1077_2 := h1077c.2.2.1
                                      have p1077_3 := h1077c.2.2.2
                                      linarith only [h1022, h5, h659, hc23, hc34, hlam, hphi, p1077_1]
                                    · have p1077_0 := h1077c.1
                                      have p1077_1 := h1077c.2.1
                                      have p1077_2 := h1077c.2.2.1
                                      have p1077_3 := h1077c.2.2.2
                                      linarith only [h1, h1011, h1028, h6, hc23, hc34, hlam, hphi, p1077_1]
                                    · have p1077_0 := h1077c.1
                                      have p1077_1 := h1077c.2.1
                                      have p1077_2 := h1077c.2.2.1
                                      have p1077_3 := h1077c.2.2.2
                                      linarith only [h1011, h1014, h1028, hc23, hc34, hlam, hphi, p1077_1]
                                    · have p1077_0 := h1077c.1
                                      have p1077_1 := h1077c.2.1
                                      have p1077_2 := h1077c.2.2.1
                                      have p1077_3 := h1077c.2.2.2
                                      linarith only [h1022, h1028, hc23, hc34, hlam, hphi, p1077_1]
                                    · have p1077_0 := h1077c.1
                                      have p1077_1 := h1077c.2.1
                                      have p1077_2 := h1077c.2.2.1
                                      have p1077_3 := h1077c.2.2.2
                                      linarith only [h1028, hlam, p1077_0]
                                    · have p1077_0 := h1077c.1
                                      have p1077_1 := h1077c.2.1
                                      have p1077_2 := h1077c.2.2.1
                                      have p1077_3 := h1077c.2.2.2
                                      linarith only [hlam, p1077_0]
                            · linarith only [h1070, hlam, p1029_0]
                          · linarith only [h0, h1069, hlam, p1029_1]
                        · have p1029_0 := h1029c.1
                          have p1029_1 := h1029c.2.1
                          have p1029_2 := h1029c.2.2.1
                          have p1029_3 := h1029c.2.2.2
                          linarith only [h4, hlam, p1029_0]
                        · have p1029_0 := h1029c.1
                          have p1029_1 := h1029c.2.1
                          have p1029_2 := h1029c.2.2.1
                          have p1029_3 := h1029c.2.2.2
                          linarith only [h1011, hlam, p1029_0]
                        · have p1029_0 := h1029c.1
                          have p1029_1 := h1029c.2.1
                          have p1029_2 := h1029c.2.2.1
                          have p1029_3 := h1029c.2.2.2
                          linarith only [hlam, p1029_0]
                        · have p1029_0 := h1029c.1
                          have p1029_1 := h1029c.2.1
                          have p1029_2 := h1029c.2.2.1
                          have p1029_3 := h1029c.2.2.2
                          linarith only [h1022, hlam, p1029_0]
                        · have p1029_0 := h1029c.1
                          have p1029_1 := h1029c.2.1
                          have p1029_2 := h1029c.2.2.1
                          have p1029_3 := h1029c.2.2.2
                          linarith only [h1024, hlam, p1029_0]
                        · have p1029_0 := h1029c.1
                          have p1029_1 := h1029c.2.1
                          have p1029_2 := h1029c.2.2.1
                          have p1029_3 := h1029c.2.2.2
                          linarith only [h5, hlam, p1029_0]
                        · have p1029_0 := h1029c.1
                          have p1029_1 := h1029c.2.1
                          have p1029_2 := h1029c.2.2.1
                          have p1029_3 := h1029c.2.2.2
                          linarith only [h1012, hlam, p1029_0]
                        · have p1029_0 := h1029c.1
                          have p1029_1 := h1029c.2.1
                          have p1029_2 := h1029c.2.2.1
                          have p1029_3 := h1029c.2.2.2
                          linarith only [h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1029_1, u2elo0]
                        · have p1029_0 := h1029c.1
                          have p1029_1 := h1029c.2.1
                          have p1029_2 := h1029c.2.2.1
                          have p1029_3 := h1029c.2.2.2
                          linarith only [hlam, p1029_0]
                        · have p1029_0 := h1029c.1
                          have p1029_1 := h1029c.2.1
                          have p1029_2 := h1029c.2.2.1
                          have p1029_3 := h1029c.2.2.2
                          linarith only [h1026, hlam, p1029_1]
                        · have p1029_0 := h1029c.1
                          have p1029_1 := h1029c.2.1
                          have p1029_2 := h1029c.2.2.1
                          have p1029_3 := h1029c.2.2.2
                          linarith only [hc02, hlam, hphi, p1029_1, u2elo4]
                        · have p1029_0 := h1029c.1
                          have p1029_1 := h1029c.2.1
                          have p1029_2 := h1029c.2.2.1
                          have p1029_3 := h1029c.2.2.2
                          linarith only [h1013, hlam, p1029_0]
                        · have p1029_0 := h1029c.1
                          have p1029_1 := h1029c.2.1
                          have p1029_2 := h1029c.2.2.1
                          have p1029_3 := h1029c.2.2.2
                          linarith only [h1013, h1028, h3, h659, hc23, hc34, hlam, hphi, p1029_1]
                        · have p1029_0 := h1029c.1
                          have p1029_1 := h1029c.2.1
                          have p1029_2 := h1029c.2.2.1
                          have p1029_3 := h1029c.2.2.2
                          linarith only [h0, h1013, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1029_1, u2elo0]
                        · have p1029_0 := h1029c.1
                          have p1029_1 := h1029c.2.1
                          have p1029_2 := h1029c.2.2.1
                          have p1029_3 := h1029c.2.2.2
                          linarith only [hlam, p1029_0]
                      · rcases h2bigk with h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c
                        · have p1134_0 := h1134c.1
                          have p1134_1 := h1134c.2.1
                          have p1134_2 := h1134c.2.2.1
                          have p1134_3 := h1134c.2.2.2
                          linarith only [hlam, p1134_0]
                        · have p1134_0 := h1134c.1
                          have p1134_1 := h1134c.2.1
                          have p1134_2 := h1134c.2.2.1
                          have p1134_3 := h1134c.2.2.2
                          linarith only [hc12, hlam, hphi, p1134_1, u2elo0]
                        · have p1134_0 := h1134c.1
                          have p1134_1 := h1134c.2.1
                          have p1134_2 := h1134c.2.2.1
                          have p1134_3 := h1134c.2.2.2
                          rcases p1134_3 (m.d 0 2) (by simp) with h1137 | h1137
                          · rcases p1134_3 (m.d 1 2) (by simp) with h1138 | h1138
                            · linarith only [h0, h1138, hlam]
                            · linarith only [h1011, h1138, hlam]
                          · linarith only [h1137, hlam, p1134_0]
                        · have p1134_0 := h1134c.1
                          have p1134_1 := h1134c.2.1
                          have p1134_2 := h1134c.2.2.1
                          have p1134_3 := h1134c.2.2.2
                          rcases p1134_3 (m.d 0 2) (by simp) with h1142 | h1142
                          · rcases p1134_3 (m.d 1 2) (by simp) with h1143 | h1143
                            · linarith only [h0, h1143, hlam]
                            · linarith only [h1012, h1143, hlam]
                          · linarith only [h1142, hlam, p1134_0]
                        · have p1134_0 := h1134c.1
                          have p1134_1 := h1134c.2.1
                          have p1134_2 := h1134c.2.2.1
                          have p1134_3 := h1134c.2.2.2
                          rcases p1134_3 (m.d 0 2) (by simp) with h1147 | h1147
                          · rcases p1134_3 (m.d 1 2) (by simp) with h1148 | h1148
                            · linarith only [h0, h1148, hlam]
                            · linarith only [h1013, h1148, hlam]
                          · linarith only [h1147, hlam, p1134_0]
                        · have p1134_0 := h1134c.1
                          have p1134_1 := h1134c.2.1
                          have p1134_2 := h1134c.2.2.1
                          have p1134_3 := h1134c.2.2.2
                          linarith only [h0, hlam, p1134_0]
                        · have p1134_0 := h1134c.1
                          have p1134_1 := h1134c.2.1
                          have p1134_2 := h1134c.2.2.1
                          have p1134_3 := h1134c.2.2.2
                          linarith only [hlam, p1134_0]
                        · have p1134_0 := h1134c.1
                          have p1134_1 := h1134c.2.1
                          have p1134_2 := h1134c.2.2.1
                          have p1134_3 := h1134c.2.2.2
                          rcases p1134_3 (m.d 0 2) (by simp) with h1154 | h1154
                          · rcases p1134_3 (m.d 1 2) (by simp) with h1155 | h1155
                            · rcases p1134_3 (m.d 2 3) (by simp) with h1156 | h1156
                              · linarith only [h1156, hlam, p1134_0]
                              · rcases p1134_3 (m.d 2 4) (by simp) with h1158 | h1158
                                · linarith only [h1012, h1158, hlam]
                                · linarith only [h1022, h1158, hlam]
                            · linarith only [h1155, hlam, p1134_0]
                          · linarith only [h1154, h4, hlam]
                        · have p1134_0 := h1134c.1
                          have p1134_1 := h1134c.2.1
                          have p1134_2 := h1134c.2.2.1
                          have p1134_3 := h1134c.2.2.2
                          rcases p1134_3 (m.d 0 2) (by simp) with h1163 | h1163
                          · rcases p1134_3 (m.d 1 2) (by simp) with h1164 | h1164
                            · rcases p1134_3 (m.d 2 3) (by simp) with h1165 | h1165
                              · linarith only [h1011, h1165, hlam]
                              · rcases p1134_3 (m.d 2 4) (by simp) with h1167 | h1167
                                · linarith only [h1167, hlam, p1134_0]
                                · rcases p1134_3 (m.d 2 5) (by simp) with h1169 | h1169
                                  · linarith only [h1013, h1169, hlam]
                                  · linarith only [h1026, h1169, hlam]
                            · linarith only [h1164, hlam, p1134_0]
                          · linarith only [h1163, h5, hlam]
                        · have p1134_0 := h1134c.1
                          have p1134_1 := h1134c.2.1
                          have p1134_2 := h1134c.2.2.1
                          have p1134_3 := h1134c.2.2.2
                          rcases p1134_3 (m.d 0 2) (by simp) with h1174 | h1174
                          · rcases p1134_3 (m.d 1 2) (by simp) with h1175 | h1175
                            · rcases p1134_3 (m.d 2 3) (by simp) with h1176 | h1176
                              · linarith only [h1011, h1176, hlam]
                              · rcases p1134_3 (m.d 2 4) (by simp) with h1178 | h1178
                                · linarith only [h1012, h1178, hlam]
                                · rcases p1134_3 (m.d 2 5) (by simp) with h1180 | h1180
                                  · linarith only [h1180, hlam, p1134_0]
                                  · rcases h4bigk with h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c
                                    · have p1182_0 := h1182c.1
                                      have p1182_1 := h1182c.2.1
                                      have p1182_2 := h1182c.2.2.1
                                      have p1182_3 := h1182c.2.2.2
                                      linarith only [hlam, p1182_0]
                                    · have p1182_0 := h1182c.1
                                      have p1182_1 := h1182c.2.1
                                      have p1182_2 := h1182c.2.2.1
                                      have p1182_3 := h1182c.2.2.2
                                      linarith only [h1011, h1014, h1028, h6, hc23, hc45, hlam, hphi, ht34, p1182_1]
                                    · have p1182_0 := h1182c.1
                                      have p1182_1 := h1182c.2.1
                                      have p1182_2 := h1182c.2.2.1
                                      have p1182_3 := h1182c.2.2.2
                                      linarith only [h1022, h1028, h6, hc23, hc45, hlam, hphi, ht34, p1182_1]
                                    · have p1182_0 := h1182c.1
                                      have p1182_1 := h1182c.2.1
                                      have p1182_2 := h1182c.2.2.1
                                      have p1182_3 := h1182c.2.2.2
                                      linarith only [h6, hlam, p1182_0]
                                    · have p1182_0 := h1182c.1
                                      have p1182_1 := h1182c.2.1
                                      have p1182_2 := h1182c.2.2.1
                                      have p1182_3 := h1182c.2.2.2
                                      linarith only [h659, hlam, p1182_0]
                                    · have p1182_0 := h1182c.1
                                      have p1182_1 := h1182c.2.1
                                      have p1182_2 := h1182c.2.2.1
                                      have p1182_3 := h1182c.2.2.2
                                      linarith only [h2, hlam, p1182_1]
                                    · have p1182_0 := h1182c.1
                                      have p1182_1 := h1182c.2.1
                                      have p1182_2 := h1182c.2.2.1
                                      have p1182_3 := h1182c.2.2.2
                                      linarith only [hlam, p1182_0]
                                    · have p1182_0 := h1182c.1
                                      have p1182_1 := h1182c.2.1
                                      have p1182_2 := h1182c.2.2.1
                                      have p1182_3 := h1182c.2.2.2
                                      linarith only [h1022, h1028, h2, h6, hc23, hc45, hlam, hphi, ht34, p1182_1]
                                    · have p1182_0 := h1182c.1
                                      have p1182_1 := h1182c.2.1
                                      have p1182_2 := h1182c.2.2.1
                                      have p1182_3 := h1182c.2.2.2
                                      linarith only [h1014, hlam, p1182_1]
                                    · have p1182_0 := h1182c.1
                                      have p1182_1 := h1182c.2.1
                                      have p1182_2 := h1182c.2.2.1
                                      have p1182_3 := h1182c.2.2.2
                                      linarith only [h1020, hlam, p1182_0]
                                    · have p1182_0 := h1182c.1
                                      have p1182_1 := h1182c.2.1
                                      have p1182_2 := h1182c.2.2.1
                                      have p1182_3 := h1182c.2.2.2
                                      linarith only [h5, hlam, p1182_1]
                                    · have p1182_0 := h1182c.1
                                      have p1182_1 := h1182c.2.1
                                      have p1182_2 := h1182c.2.2.1
                                      have p1182_3 := h1182c.2.2.2
                                      linarith only [h1012, hlam, p1182_1]
                                    · have p1182_0 := h1182c.1
                                      have p1182_1 := h1182c.2.1
                                      have p1182_2 := h1182c.2.2.1
                                      have p1182_3 := h1182c.2.2.2
                                      linarith only [hlam, p1182_0]
                                    · have p1182_0 := h1182c.1
                                      have p1182_1 := h1182c.2.1
                                      have p1182_2 := h1182c.2.2.1
                                      have p1182_3 := h1182c.2.2.2
                                      linarith only [h1022, hlam, p1182_1]
                                    · have p1182_0 := h1182c.1
                                      have p1182_1 := h1182c.2.1
                                      have p1182_2 := h1182c.2.2.1
                                      have p1182_3 := h1182c.2.2.2
                                      linarith only [h1026, hlam, p1182_0]
                                    · have p1182_0 := h1182c.1
                                      have p1182_1 := h1182c.2.1
                                      have p1182_2 := h1182c.2.2.1
                                      have p1182_3 := h1182c.2.2.2
                                      linarith only [h1028, hc04, hc45, hlam, hphi, p1182_1]
                                    · have p1182_0 := h1182c.1
                                      have p1182_1 := h1182c.2.1
                                      have p1182_2 := h1182c.2.2.1
                                      have p1182_3 := h1182c.2.2.2
                                      linarith only [h1028, hc14, hc45, hlam, hphi, p1182_1]
                                    · have p1182_0 := h1182c.1
                                      have p1182_1 := h1182c.2.1
                                      have p1182_2 := h1182c.2.2.1
                                      have p1182_3 := h1182c.2.2.2
                                      linarith only [h1022, h1028, hc23, hc45, hlam, hphi, ht34, p1182_1]
                                    · have p1182_0 := h1182c.1
                                      have p1182_1 := h1182c.2.1
                                      have p1182_2 := h1182c.2.2.1
                                      have p1182_3 := h1182c.2.2.2
                                      linarith only [hlam, p1182_0]
                                    · have p1182_0 := h1182c.1
                                      have p1182_1 := h1182c.2.1
                                      have p1182_2 := h1182c.2.2.1
                                      have p1182_3 := h1182c.2.2.2
                                      linarith only [h1028, hlam, p1182_0]
                                    · have p1182_0 := h1182c.1
                                      have p1182_1 := h1182c.2.1
                                      have p1182_2 := h1182c.2.2.1
                                      have p1182_3 := h1182c.2.2.2
                                      rcases p1182_3 (m.d 0 4) (by simp) with h1203 | h1203
                                      · linarith only [h1203, hlam, p1182_0]
                                      · rcases p1182_3 (m.d 1 4) (by simp) with h1205 | h1205
                                        · linarith only [h1020, h1205, hlam]
                                        · rcases p1182_3 (m.d 2 4) (by simp) with h1207 | h1207
                                          · linarith only [h1026, h1207, hlam]
                                          · rcases p1182_3 (m.d 3 4) (by simp) with h1209 | h1209
                                            · linarith only [h1028, h1209, hlam]
                                            · linarith only [h1209, h6, hlam]
                                    · have p1182_0 := h1182c.1
                                      have p1182_1 := h1182c.2.1
                                      have p1182_2 := h1182c.2.2.1
                                      have p1182_3 := h1182c.2.2.2
                                      rcases p1182_3 (m.d 0 4) (by simp) with h1212 | h1212
                                      · linarith only [h1212, h659, hlam]
                                      · linarith only [h1212, h2, hlam]
                                    · have p1182_0 := h1182c.1
                                      have p1182_1 := h1182c.2.1
                                      have p1182_2 := h1182c.2.2.1
                                      have p1182_3 := h1182c.2.2.2
                                      rcases p1182_3 (m.d 0 4) (by simp) with h1215 | h1215
                                      · linarith only [h1215, h659, hlam]
                                      · linarith only [h1215, h5, hlam]
                                    · have p1182_0 := h1182c.1
                                      have p1182_1 := h1182c.2.1
                                      have p1182_2 := h1182c.2.2.1
                                      have p1182_3 := h1182c.2.2.2
                                      linarith only [h1, h1011, h6, hc23, hc45, hlam, hphi, ht34, p1182_1]
                                    · have p1182_0 := h1182c.1
                                      have p1182_1 := h1182c.2.1
                                      have p1182_2 := h1182c.2.2.1
                                      have p1182_3 := h1182c.2.2.2
                                      linarith only [hlam, p1182_0]
                            · linarith only [h1175, hlam, p1134_0]
                          · linarith only [h1174, hc02, hlam, hphi, p1134_1, u2elo1]
                        · have p1134_0 := h1134c.1
                          have p1134_1 := h1134c.2.1
                          have p1134_2 := h1134c.2.2.1
                          have p1134_3 := h1134c.2.2.2
                          linarith only [h4, hlam, p1134_0]
                        · have p1134_0 := h1134c.1
                          have p1134_1 := h1134c.2.1
                          have p1134_2 := h1134c.2.2.1
                          have p1134_3 := h1134c.2.2.2
                          linarith only [h1011, hlam, p1134_0]
                        · have p1134_0 := h1134c.1
                          have p1134_1 := h1134c.2.1
                          have p1134_2 := h1134c.2.2.1
                          have p1134_3 := h1134c.2.2.2
                          linarith only [hlam, p1134_0]
                        · have p1134_0 := h1134c.1
                          have p1134_1 := h1134c.2.1
                          have p1134_2 := h1134c.2.2.1
                          have p1134_3 := h1134c.2.2.2
                          linarith only [h1022, hlam, p1134_0]
                        · have p1134_0 := h1134c.1
                          have p1134_1 := h1134c.2.1
                          have p1134_2 := h1134c.2.2.1
                          have p1134_3 := h1134c.2.2.2
                          linarith only [h1024, hlam, p1134_0]
                        · have p1134_0 := h1134c.1
                          have p1134_1 := h1134c.2.1
                          have p1134_2 := h1134c.2.2.1
                          have p1134_3 := h1134c.2.2.2
                          linarith only [h5, hlam, p1134_0]
                        · have p1134_0 := h1134c.1
                          have p1134_1 := h1134c.2.1
                          have p1134_2 := h1134c.2.2.1
                          have p1134_3 := h1134c.2.2.2
                          linarith only [h1012, hlam, p1134_0]
                        · have p1134_0 := h1134c.1
                          have p1134_1 := h1134c.2.1
                          have p1134_2 := h1134c.2.2.1
                          have p1134_3 := h1134c.2.2.2
                          linarith only [h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1134_1, u2elo0]
                        · have p1134_0 := h1134c.1
                          have p1134_1 := h1134c.2.1
                          have p1134_2 := h1134c.2.2.1
                          have p1134_3 := h1134c.2.2.2
                          linarith only [hlam, p1134_0]
                        · have p1134_0 := h1134c.1
                          have p1134_1 := h1134c.2.1
                          have p1134_2 := h1134c.2.2.1
                          have p1134_3 := h1134c.2.2.2
                          linarith only [h1026, hlam, p1134_1]
                        · have p1134_0 := h1134c.1
                          have p1134_1 := h1134c.2.1
                          have p1134_2 := h1134c.2.2.1
                          have p1134_3 := h1134c.2.2.2
                          linarith only [h0, h1013, hlam, p1134_1]
                        · have p1134_0 := h1134c.1
                          have p1134_1 := h1134c.2.1
                          have p1134_2 := h1134c.2.2.1
                          have p1134_3 := h1134c.2.2.2
                          linarith only [h1013, hlam, p1134_0]
                        · have p1134_0 := h1134c.1
                          have p1134_1 := h1134c.2.1
                          have p1134_2 := h1134c.2.2.1
                          have p1134_3 := h1134c.2.2.2
                          linarith only [h0, h1013, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1134_1, u2elo0]
                        · have p1134_0 := h1134c.1
                          have p1134_1 := h1134c.2.1
                          have p1134_2 := h1134c.2.2.1
                          have p1134_3 := h1134c.2.2.2
                          linarith only [h0, h1013, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1134_1, u2elo0]
                        · have p1134_0 := h1134c.1
                          have p1134_1 := h1134c.2.1
                          have p1134_2 := h1134c.2.2.1
                          have p1134_3 := h1134c.2.2.2
                          linarith only [hlam, p1134_0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1237 | h1237
          · linarith only [h1, h1237, h6, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1239 | h1239
            · linarith only [h1011, h1013, h1239, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1241 | h1241
              · linarith only [h1012, h1013, h1241, h3, h659, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1243 | h1243
                · linarith only [h1243, h4, h6, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1245 | h1245
                  · linarith only [h1013, h1239, h1245, h4, hc12, hlam, hphi, u2elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1247 | h1247
                    · linarith only [h1012, h1013, h1247, h3, h659, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1249 | h1249
                      · linarith only [h1012, h1013, h1243, h1247, h1249, hc23, hc34, hlam, hphi]
                      · rcases h2bigk with h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [hlam, p1251_0]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [h1012, h1243, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1251_1, u2elo0]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          rcases p1251_3 (m.d 0 2) (by simp) with h1254 | h1254
                          · rcases p1251_3 (m.d 1 2) (by simp) with h1255 | h1255
                            · linarith only [h0, h1255, hlam]
                            · linarith only [h1011, h1255, hlam]
                          · linarith only [h1254, hlam, p1251_0]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          rcases p1251_3 (m.d 0 2) (by simp) with h1259 | h1259
                          · rcases p1251_3 (m.d 1 2) (by simp) with h1260 | h1260
                            · linarith only [h0, h1260, hlam]
                            · linarith only [h1012, h1260, hlam]
                          · linarith only [h1259, hlam, p1251_0]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [h1012, h1013, h1243, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1251_1, u2elo0]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [h0, hlam, p1251_0]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [hlam, p1251_0]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [h1013, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1251_1, u2elo4]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [h1013, h1243, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1251_1, u2elo4]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [h1013, hlam, p1251_0]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [h4, hlam, p1251_0]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [h1011, hlam, p1251_0]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [hlam, p1251_0]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [h1243, hlam, p1251_0]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [h1245, hlam, p1251_0]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [h5, hlam, p1251_0]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [h1012, hlam, p1251_0]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1251_1, u2elo0]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [hlam, p1251_0]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [h1247, hlam, p1251_1]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [hc02, hlam, hphi, p1251_1, u2elo4]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [hc12, hlam, hphi, p1251_1, u2elo4]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          rcases p1251_3 (m.d 0 2) (by simp) with h1282 | h1282
                          · rcases p1251_3 (m.d 1 2) (by simp) with h1283 | h1283
                            · linarith only [h1013, h1283, hlam]
                            · linarith only [h1011, h1283, hlam]
                          · linarith only [h1282, h4, hlam]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          rcases p1251_3 (m.d 0 2) (by simp) with h1287 | h1287
                          · rcases p1251_3 (m.d 1 2) (by simp) with h1288 | h1288
                            · linarith only [h1013, h1288, hlam]
                            · linarith only [h1012, h1288, hlam]
                          · linarith only [h1287, h5, hlam]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [hlam, p1251_0]
      · linarith only [h1012, h5, hc12, hlam, hphi, u2elo0]
    · linarith only [h1011, h4, hc12, hlam, hphi, u2elo0]

set_option maxHeartbeats 7332000 in
set_option maxHeartbeats 7332000 in
theorem r1l7_22_14_M_LI_L_I_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4bigk := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
  · exact r1l7_22_14_M_LI_L_I_x0_x0_x0_x0_x0_x0_x0 m hb2 hb4 h0 h1 h2 h3 h4 h5 h6
  · exact r1l7_22_14_M_LI_L_I_x0_x0_x0_x0_x0_x0_x1 m hb2 hb4 h0 h1 h2 h3 h4 h5 h6

set_option maxHeartbeats 7332000 in
set_option maxHeartbeats 7332000 in
theorem r1l7_22_14_M_LI_L_I_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4bigk := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h1295 | h1295
  · linarith only [h1295, h4, h5, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1297 | h1297
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1298 | h1298
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1299 | h1299
        · linarith only [h1299, h5, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1301 | h1301
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1302 | h1302
            · linarith only [h0, h1295, h1298, h1302, h5, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1304 | h1304
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1305 | h1305
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1306 | h1306
                  · linarith only [h1, h1295, h1304, h1306, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1308 | h1308
                    · linarith only [h0, h1298, h1308, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                    · linarith only [h1, h1304, h1308, h4, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h1297, h1299, h1305, h5, hc12, hlam, hphi, u2elo3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1312 | h1312
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1313 | h1313
                  · linarith only [h0, h1295, h1298, h1313, h5, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1315 | h1315
                    · linarith only [h0, h1298, h1304, h1315, h5, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1317 | h1317
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1318 | h1318
                        · rcases h2bigk with h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c
                          · have p1319_0 := h1319c.1
                            have p1319_1 := h1319c.2.1
                            have p1319_2 := h1319c.2.2.1
                            have p1319_3 := h1319c.2.2.2
                            linarith only [hlam, p1319_0]
                          · have p1319_0 := h1319c.1
                            have p1319_1 := h1319c.2.1
                            have p1319_2 := h1319c.2.2.1
                            have p1319_3 := h1319c.2.2.2
                            linarith only [h5, hc12, hlam, hphi, p1319_1, u2elo3]
                          · have p1319_0 := h1319c.1
                            have p1319_1 := h1319c.2.1
                            have p1319_2 := h1319c.2.2.1
                            have p1319_3 := h1319c.2.2.2
                            linarith only [h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1319_1, u2elo3]
                          · have p1319_0 := h1319c.1
                            have p1319_1 := h1319c.2.1
                            have p1319_2 := h1319c.2.2.1
                            have p1319_3 := h1319c.2.2.2
                            linarith only [h5, hlam, p1319_0]
                          · have p1319_0 := h1319c.1
                            have p1319_1 := h1319c.2.1
                            have p1319_2 := h1319c.2.2.1
                            have p1319_3 := h1319c.2.2.2
                            linarith only [h1315, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1319_1, u2elo3]
                          · have p1319_0 := h1319c.1
                            have p1319_1 := h1319c.2.1
                            have p1319_2 := h1319c.2.2.1
                            have p1319_3 := h1319c.2.2.2
                            linarith only [h0, hlam, p1319_0]
                          · have p1319_0 := h1319c.1
                            have p1319_1 := h1319c.2.1
                            have p1319_2 := h1319c.2.2.1
                            have p1319_3 := h1319c.2.2.2
                            linarith only [hlam, p1319_0]
                          · have p1319_0 := h1319c.1
                            have p1319_1 := h1319c.2.1
                            have p1319_2 := h1319c.2.2.1
                            have p1319_3 := h1319c.2.2.2
                            linarith only [h0, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1319_1, u2elo3]
                          · have p1319_0 := h1319c.1
                            have p1319_1 := h1319c.2.1
                            have p1319_2 := h1319c.2.2.1
                            have p1319_3 := h1319c.2.2.2
                            linarith only [h1299, hlam, p1319_0]
                          · have p1319_0 := h1319c.1
                            have p1319_1 := h1319c.2.1
                            have p1319_2 := h1319c.2.2.1
                            have p1319_3 := h1319c.2.2.2
                            linarith only [h0, h1315, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1319_1, u2elo3]
                          · have p1319_0 := h1319c.1
                            have p1319_1 := h1319c.2.1
                            have p1319_2 := h1319c.2.2.1
                            have p1319_3 := h1319c.2.2.2
                            linarith only [h4, hlam, p1319_0]
                          · have p1319_0 := h1319c.1
                            have p1319_1 := h1319c.2.1
                            have p1319_2 := h1319c.2.2.1
                            have p1319_3 := h1319c.2.2.2
                            linarith only [h1298, hlam, p1319_0]
                          · have p1319_0 := h1319c.1
                            have p1319_1 := h1319c.2.1
                            have p1319_2 := h1319c.2.2.1
                            have p1319_3 := h1319c.2.2.2
                            linarith only [hlam, p1319_0]
                          · have p1319_0 := h1319c.1
                            have p1319_1 := h1319c.2.1
                            have p1319_2 := h1319c.2.2.1
                            have p1319_3 := h1319c.2.2.2
                            linarith only [h1313, hlam, p1319_0]
                          · have p1319_0 := h1319c.1
                            have p1319_1 := h1319c.2.1
                            have p1319_2 := h1319c.2.2.1
                            have p1319_3 := h1319c.2.2.2
                            linarith only [h1315, hlam, p1319_0]
                          · have p1319_0 := h1319c.1
                            have p1319_1 := h1319c.2.1
                            have p1319_2 := h1319c.2.2.1
                            have p1319_3 := h1319c.2.2.2
                            linarith only [hc02, hlam, hphi, p1319_1, u2elo3]
                          · have p1319_0 := h1319c.1
                            have p1319_1 := h1319c.2.1
                            have p1319_2 := h1319c.2.2.1
                            have p1319_3 := h1319c.2.2.2
                            linarith only [h1298, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1319_1, u2elo3]
                          · have p1319_0 := h1319c.1
                            have p1319_1 := h1319c.2.1
                            have p1319_2 := h1319c.2.2.1
                            have p1319_3 := h1319c.2.2.2
                            rcases p1319_3 (m.d 0 2) (by simp) with h1337 | h1337
                            · linarith only [h1337, h5, hlam]
                            · linarith only [h1337, h4, hlam]
                          · have p1319_0 := h1319c.1
                            have p1319_1 := h1319c.2.1
                            have p1319_2 := h1319c.2.2.1
                            have p1319_3 := h1319c.2.2.2
                            linarith only [hlam, p1319_0]
                          · have p1319_0 := h1319c.1
                            have p1319_1 := h1319c.2.1
                            have p1319_2 := h1319c.2.2.1
                            have p1319_3 := h1319c.2.2.2
                            rcases p1319_3 (m.d 0 2) (by simp) with h1341 | h1341
                            · linarith only [h1341, h5, hlam]
                            · linarith only [h0, h1301, h1341, hlam]
                          · have p1319_0 := h1319c.1
                            have p1319_1 := h1319c.2.1
                            have p1319_2 := h1319c.2.2.1
                            have p1319_3 := h1319c.2.2.2
                            linarith only [h0, h1301, hlam, p1319_1]
                          · have p1319_0 := h1319c.1
                            have p1319_1 := h1319c.2.1
                            have p1319_2 := h1319c.2.2.1
                            have p1319_3 := h1319c.2.2.2
                            linarith only [h1301, hlam, p1319_0]
                          · have p1319_0 := h1319c.1
                            have p1319_1 := h1319c.2.1
                            have p1319_2 := h1319c.2.2.1
                            have p1319_3 := h1319c.2.2.2
                            linarith only [h0, h1301, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1319_1, u2elo0]
                          · have p1319_0 := h1319c.1
                            have p1319_1 := h1319c.2.1
                            have p1319_2 := h1319c.2.2.1
                            have p1319_3 := h1319c.2.2.2
                            linarith only [h1317, hlam, p1319_0]
                          · have p1319_0 := h1319c.1
                            have p1319_1 := h1319c.2.1
                            have p1319_2 := h1319c.2.2.1
                            have p1319_3 := h1319c.2.2.2
                            linarith only [hlam, p1319_0]
                        · linarith only [h1313, h1318, h4, h5, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h1301, h1312, h1315, h1317, h5, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h1297, h1298, h1299, h1312, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1352 | h1352
            · linarith only [h1, h1295, h1352, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1354 | h1354
              · linarith only [h1298, h1301, h1354, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1356 | h1356
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1357 | h1357
                  · linarith only [h1295, h1298, h1301, h1357, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1359 | h1359
                    · linarith only [h0, h1298, h1354, h1359, h5, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1361 | h1361
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1362 | h1362
                        · rcases h2bigk with h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c
                          · have p1363_0 := h1363c.1
                            have p1363_1 := h1363c.2.1
                            have p1363_2 := h1363c.2.2.1
                            have p1363_3 := h1363c.2.2.2
                            linarith only [hlam, p1363_0]
                          · have p1363_0 := h1363c.1
                            have p1363_1 := h1363c.2.1
                            have p1363_2 := h1363c.2.2.1
                            have p1363_3 := h1363c.2.2.2
                            linarith only [h5, hc12, hlam, hphi, p1363_1, u2elo3]
                          · have p1363_0 := h1363c.1
                            have p1363_1 := h1363c.2.1
                            have p1363_2 := h1363c.2.2.1
                            have p1363_3 := h1363c.2.2.2
                            linarith only [h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1363_1, u2elo3]
                          · have p1363_0 := h1363c.1
                            have p1363_1 := h1363c.2.1
                            have p1363_2 := h1363c.2.2.1
                            have p1363_3 := h1363c.2.2.2
                            linarith only [h5, hlam, p1363_0]
                          · have p1363_0 := h1363c.1
                            have p1363_1 := h1363c.2.1
                            have p1363_2 := h1363c.2.2.1
                            have p1363_3 := h1363c.2.2.2
                            linarith only [h1298, h1301, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1363_1]
                          · have p1363_0 := h1363c.1
                            have p1363_1 := h1363c.2.1
                            have p1363_2 := h1363c.2.2.1
                            have p1363_3 := h1363c.2.2.2
                            linarith only [h0, hlam, p1363_0]
                          · have p1363_0 := h1363c.1
                            have p1363_1 := h1363c.2.1
                            have p1363_2 := h1363c.2.2.1
                            have p1363_3 := h1363c.2.2.2
                            linarith only [hlam, p1363_0]
                          · have p1363_0 := h1363c.1
                            have p1363_1 := h1363c.2.1
                            have p1363_2 := h1363c.2.2.1
                            have p1363_3 := h1363c.2.2.2
                            linarith only [h1301, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1363_1, u2elo4]
                          · have p1363_0 := h1363c.1
                            have p1363_1 := h1363c.2.1
                            have p1363_2 := h1363c.2.2.1
                            have p1363_3 := h1363c.2.2.2
                            linarith only [h1299, hlam, p1363_0]
                          · have p1363_0 := h1363c.1
                            have p1363_1 := h1363c.2.1
                            have p1363_2 := h1363c.2.2.1
                            have p1363_3 := h1363c.2.2.2
                            linarith only [h1301, hlam, p1363_0]
                          · have p1363_0 := h1363c.1
                            have p1363_1 := h1363c.2.1
                            have p1363_2 := h1363c.2.2.1
                            have p1363_3 := h1363c.2.2.2
                            linarith only [h4, hlam, p1363_0]
                          · have p1363_0 := h1363c.1
                            have p1363_1 := h1363c.2.1
                            have p1363_2 := h1363c.2.2.1
                            have p1363_3 := h1363c.2.2.2
                            linarith only [h1298, hlam, p1363_0]
                          · have p1363_0 := h1363c.1
                            have p1363_1 := h1363c.2.1
                            have p1363_2 := h1363c.2.2.1
                            have p1363_3 := h1363c.2.2.2
                            linarith only [hlam, p1363_0]
                          · have p1363_0 := h1363c.1
                            have p1363_1 := h1363c.2.1
                            have p1363_2 := h1363c.2.2.1
                            have p1363_3 := h1363c.2.2.2
                            linarith only [h1357, hlam, p1363_0]
                          · have p1363_0 := h1363c.1
                            have p1363_1 := h1363c.2.1
                            have p1363_2 := h1363c.2.2.1
                            have p1363_3 := h1363c.2.2.2
                            linarith only [h1359, hlam, p1363_0]
                          · have p1363_0 := h1363c.1
                            have p1363_1 := h1363c.2.1
                            have p1363_2 := h1363c.2.2.1
                            have p1363_3 := h1363c.2.2.2
                            linarith only [hc02, hlam, hphi, p1363_1, u2elo3]
                          · have p1363_0 := h1363c.1
                            have p1363_1 := h1363c.2.1
                            have p1363_2 := h1363c.2.2.1
                            have p1363_3 := h1363c.2.2.2
                            linarith only [hc12, hlam, hphi, p1363_1, u2elo3]
                          · have p1363_0 := h1363c.1
                            have p1363_1 := h1363c.2.1
                            have p1363_2 := h1363c.2.2.1
                            have p1363_3 := h1363c.2.2.2
                            rcases p1363_3 (m.d 0 2) (by simp) with h1381 | h1381
                            · linarith only [h1381, h5, hlam]
                            · linarith only [h1381, h4, hlam]
                          · have p1363_0 := h1363c.1
                            have p1363_1 := h1363c.2.1
                            have p1363_2 := h1363c.2.2.1
                            have p1363_3 := h1363c.2.2.2
                            linarith only [hlam, p1363_0]
                          · have p1363_0 := h1363c.1
                            have p1363_1 := h1363c.2.1
                            have p1363_2 := h1363c.2.2.1
                            have p1363_3 := h1363c.2.2.2
                            linarith only [h1298, h1301, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1363_1, u2elo3]
                          · have p1363_0 := h1363c.1
                            have p1363_1 := h1363c.2.1
                            have p1363_2 := h1363c.2.2.1
                            have p1363_3 := h1363c.2.2.2
                            linarith only [hc02, hlam, hphi, p1363_1, u2elo4]
                          · have p1363_0 := h1363c.1
                            have p1363_1 := h1363c.2.1
                            have p1363_2 := h1363c.2.2.1
                            have p1363_3 := h1363c.2.2.2
                            linarith only [h1298, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1363_1, u2elo4]
                          · have p1363_0 := h1363c.1
                            have p1363_1 := h1363c.2.1
                            have p1363_2 := h1363c.2.2.1
                            have p1363_3 := h1363c.2.2.2
                            rcases p1363_3 (m.d 0 2) (by simp) with h1388 | h1388
                            · linarith only [h1298, h1301, h1388, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                            · linarith only [h1388, h4, hlam]
                          · have p1363_0 := h1363c.1
                            have p1363_1 := h1363c.2.1
                            have p1363_2 := h1363c.2.2.1
                            have p1363_3 := h1363c.2.2.2
                            linarith only [h1361, hlam, p1363_0]
                          · have p1363_0 := h1363c.1
                            have p1363_1 := h1363c.2.1
                            have p1363_2 := h1363c.2.2.1
                            have p1363_3 := h1363c.2.2.2
                            linarith only [hlam, p1363_0]
                        · linarith only [h0, h1298, h1357, h1362, h5, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h1298, h1356, h1361, h5, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h1297, h1298, h1299, h1356, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
      · linarith only [h1298, h4, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1397 | h1397
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1398 | h1398
        · linarith only [h0, h1398, h5, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1400 | h1400
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1401 | h1401
            · linarith only [h1, h1295, h1397, h1398, h1401, h2, h4, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1403 | h1403
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1404 | h1404
                · linarith only [h0, h1297, h1397, h1404, h2, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h1398, h1400, h1404, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1407 | h1407
                · linarith only [h0, h1297, h1397, h1407, h2, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h1398, h1400, h1407, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1410 | h1410
            · linarith only [h1, h1295, h1410, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1412 | h1412
              · linarith only [h1397, h1400, h1412, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1414 | h1414
                · linarith only [h0, h1297, h1397, h1414, h2, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1416 | h1416
                  · linarith only [h1397, h1400, h1416, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1418 | h1418
                    · linarith only [h1412, h1414, h1418, h4, h5, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1420 | h1420
                      · linarith only [h1297, h1420, h5, hc02, hlam, hphi, u2elo3]
                      · linarith only [h0, h1397, h1420, h5, hc23, hc45, hlam, hphi, ht34]
      · linarith only [h1397, h4, h5, hc12, hlam, hphi, u2elo3]

set_option maxHeartbeats 7332000 in
set_option maxHeartbeats 7332000 in
theorem r1l7_22_14_M_LI_L_I_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4bigk := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_22_14_M_LI_L_I_x0_x0_x0_x0_x0_x0 m hb2 hb4 h0 h1 h2 h3 h4 h5
  · exact r1l7_22_14_M_LI_L_I_x0_x0_x0_x0_x0_x1 m hb2 hb4 h0 h1 h2 h3 h4 h5

end R2N4
