import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_39S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6958000 in
set_option maxHeartbeats 6958000 in
theorem r1l7_11_23_L_I_M_IR_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h661 | h661
  · rcases m.htr 0 3 5 (by decide) (by decide) with h662 | h662
    · rcases m.htr 1 2 3 (by decide) (by decide) with h663 | h663
      · linarith only [h0, h4, h663, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h665 | h665
        · rcases m.htr 1 2 5 (by decide) (by decide) with h666 | h666
          · rcases m.htr 1 3 4 (by decide) (by decide) with h667 | h667
            · rcases m.htr 1 3 5 (by decide) (by decide) with h668 | h668
              · rcases m.htr 1 4 5 (by decide) (by decide) with h669 | h669
                · rcases m.htr 2 3 4 (by decide) (by decide) with h670 | h670
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h671 | h671
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h672 | h672
                      · rcases h1bigk with h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [hlam, p673_0]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [h665, h670, h672, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p673_1, u3ehi4]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [h663, h665, h670, h672, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p673_1, u3ehi4]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          rcases p673_3 (m.d 0 1) (by simp) with h677 | h677
                          · rcases p673_3 (m.d 1 2) (by simp) with h678 | h678
                            · linarith only [h0, h678, hlam]
                            · linarith only [h665, h678, hlam]
                          · linarith only [h677, hlam, p673_0]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          rcases p673_3 (m.d 0 1) (by simp) with h682 | h682
                          · rcases p673_3 (m.d 1 2) (by simp) with h683 | h683
                            · linarith only [h0, h683, hlam]
                            · linarith only [h666, h683, hlam]
                          · linarith only [h682, hlam, p673_0]
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
                          linarith only [h663, hlam, p673_0]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [h0, h4, h666, h669, h671, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p673_1, u3ehi4]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [h0, h4, h666, h671, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p673_1, u3ehi4]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [h1, hlam, p673_0]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [h1, h665, h670, h672, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p673_1, u3ehi4]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [hlam, p673_0]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [h1, h666, h669, h671, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p673_1, u3ehi4]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [h1, h666, h671, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p673_1, u3ehi4]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [h2, hlam, p673_0]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [h665, hlam, p673_1]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [h667, hlam, p673_0]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [hlam, p673_0]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [h2, h666, h671, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p673_1, u3ehi4]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [h3, hlam, p673_0]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [h666, hlam, p673_1]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [h668, hlam, p673_0]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [h669, hlam, p673_0]
                        · have p673_0 := h673c.1
                          have p673_1 := h673c.2.1
                          have p673_2 := h673c.2.2.1
                          have p673_3 := h673c.2.2.2
                          linarith only [hlam, p673_0]
                      · linarith only [h0, h4, h665, h669, h672, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h4, h661, h671, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h0, h4, h665, h667, h670, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h710 | h710
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h711 | h711
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h712 | h712
                      · linarith only [h665, h669, h710, h712, hlam]
                      · rcases h1bigk with h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [hlam, p714_0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h666, h711, h712, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p714_1, u3ehi3]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h663, h666, h711, h712, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p714_1, u3ehi3]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          rcases p714_3 (m.d 0 1) (by simp) with h718 | h718
                          · rcases p714_3 (m.d 1 2) (by simp) with h719 | h719
                            · linarith only [h0, h719, hlam]
                            · linarith only [h665, h719, hlam]
                          · linarith only [h718, hlam, p714_0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          rcases p714_3 (m.d 0 1) (by simp) with h723 | h723
                          · rcases p714_3 (m.d 1 2) (by simp) with h724 | h724
                            · linarith only [h0, h724, hlam]
                            · linarith only [h666, h724, hlam]
                          · linarith only [h723, hlam, p714_0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h0, hlam, p714_0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [hlam, p714_0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h663, hlam, p714_0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h0, h4, h667, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p714_1, u3ehi3]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h0, h4, h666, h711, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p714_1, u3ehi4]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h1, hlam, p714_0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h1, h665, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p714_1]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [hlam, p714_0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h1, h667, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p714_1, u3ehi3]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h1, h666, h711, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p714_1, u3ehi4]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h2, hlam, p714_0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h665, hlam, p714_1]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h667, hlam, p714_0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [hlam, p714_0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h669, hlam, p714_1]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h3, hlam, p714_0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h666, hlam, p714_1]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h668, hlam, p714_0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h3, h667, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p714_1, u3ehi3]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [hlam, p714_0]
                    · linarith only [h4, h661, h711, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h0, h4, h666, h667, h669, h710, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
              · linarith only [h662, h667, h668, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
            · linarith only [h663, h665, h667, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h752 | h752
            · rcases m.htr 1 3 5 (by decide) (by decide) with h753 | h753
              · rcases m.htr 1 4 5 (by decide) (by decide) with h754 | h754
                · linarith only [h665, h666, h754, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h756 | h756
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h757 | h757
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h758 | h758
                      · linarith only [h665, h666, h754, h756, h758, hlam]
                      · rcases h1bigk with h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c
                        · have p760_0 := h760c.1
                          have p760_1 := h760c.2.1
                          have p760_2 := h760c.2.2.1
                          have p760_3 := h760c.2.2.2
                          linarith only [hlam, p760_0]
                        · have p760_0 := h760c.1
                          have p760_1 := h760c.2.1
                          have p760_2 := h760c.2.2.1
                          have p760_3 := h760c.2.2.2
                          linarith only [h665, h756, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p760_1, u3ehi3]
                        · have p760_0 := h760c.1
                          have p760_1 := h760c.2.1
                          have p760_2 := h760c.2.2.1
                          have p760_3 := h760c.2.2.2
                          linarith only [h753, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p760_1, u3ehi4]
                        · have p760_0 := h760c.1
                          have p760_1 := h760c.2.1
                          have p760_2 := h760c.2.2.1
                          have p760_3 := h760c.2.2.2
                          rcases p760_3 (m.d 0 1) (by simp) with h764 | h764
                          · rcases p760_3 (m.d 1 2) (by simp) with h765 | h765
                            · linarith only [h0, h765, hlam]
                            · linarith only [h665, h765, hlam]
                          · linarith only [h764, hlam, p760_0]
                        · have p760_0 := h760c.1
                          have p760_1 := h760c.2.1
                          have p760_2 := h760c.2.2.1
                          have p760_3 := h760c.2.2.2
                          linarith only [h665, h666, h756, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p760_1, u3ehi3]
                        · have p760_0 := h760c.1
                          have p760_1 := h760c.2.1
                          have p760_2 := h760c.2.2.1
                          have p760_3 := h760c.2.2.2
                          linarith only [h0, hlam, p760_0]
                        · have p760_0 := h760c.1
                          have p760_1 := h760c.2.1
                          have p760_2 := h760c.2.2.1
                          have p760_3 := h760c.2.2.2
                          linarith only [hlam, p760_0]
                        · have p760_0 := h760c.1
                          have p760_1 := h760c.2.1
                          have p760_2 := h760c.2.2.1
                          have p760_3 := h760c.2.2.2
                          linarith only [h663, hlam, p760_0]
                        · have p760_0 := h760c.1
                          have p760_1 := h760c.2.1
                          have p760_2 := h760c.2.2.1
                          have p760_3 := h760c.2.2.2
                          linarith only [h665, h666, h756, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p760_1, u3ehi3]
                        · have p760_0 := h760c.1
                          have p760_1 := h760c.2.1
                          have p760_2 := h760c.2.2.1
                          have p760_3 := h760c.2.2.2
                          linarith only [h666, hlam, p760_0]
                        · have p760_0 := h760c.1
                          have p760_1 := h760c.2.1
                          have p760_2 := h760c.2.2.1
                          have p760_3 := h760c.2.2.2
                          linarith only [h1, hlam, p760_0]
                        · have p760_0 := h760c.1
                          have p760_1 := h760c.2.1
                          have p760_2 := h760c.2.2.1
                          have p760_3 := h760c.2.2.2
                          linarith only [h1, h665, h756, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p760_1, u3ehi3]
                        · have p760_0 := h760c.1
                          have p760_1 := h760c.2.1
                          have p760_2 := h760c.2.2.1
                          have p760_3 := h760c.2.2.2
                          linarith only [hlam, p760_0]
                        · have p760_0 := h760c.1
                          have p760_1 := h760c.2.1
                          have p760_2 := h760c.2.2.1
                          have p760_3 := h760c.2.2.2
                          linarith only [h1, h665, h756, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p760_1, u3ehi3]
                        · have p760_0 := h760c.1
                          have p760_1 := h760c.2.1
                          have p760_2 := h760c.2.2.1
                          have p760_3 := h760c.2.2.2
                          linarith only [h1, h665, h666, h756, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p760_1, u3ehi3]
                        · have p760_0 := h760c.1
                          have p760_1 := h760c.2.1
                          have p760_2 := h760c.2.2.1
                          have p760_3 := h760c.2.2.2
                          linarith only [h2, hlam, p760_0]
                        · have p760_0 := h760c.1
                          have p760_1 := h760c.2.1
                          have p760_2 := h760c.2.2.1
                          have p760_3 := h760c.2.2.2
                          linarith only [h665, hlam, p760_1]
                        · have p760_0 := h760c.1
                          have p760_1 := h760c.2.1
                          have p760_2 := h760c.2.2.1
                          have p760_3 := h760c.2.2.2
                          linarith only [h752, hlam, p760_0]
                        · have p760_0 := h760c.1
                          have p760_1 := h760c.2.1
                          have p760_2 := h760c.2.2.1
                          have p760_3 := h760c.2.2.2
                          linarith only [hlam, p760_0]
                        · have p760_0 := h760c.1
                          have p760_1 := h760c.2.1
                          have p760_2 := h760c.2.2.1
                          have p760_3 := h760c.2.2.2
                          linarith only [h754, hlam, p760_1]
                        · have p760_0 := h760c.1
                          have p760_1 := h760c.2.1
                          have p760_2 := h760c.2.2.1
                          have p760_3 := h760c.2.2.2
                          linarith only [h3, hlam, p760_0]
                        · have p760_0 := h760c.1
                          have p760_1 := h760c.2.1
                          have p760_2 := h760c.2.2.1
                          have p760_3 := h760c.2.2.2
                          linarith only [h665, h756, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p760_1, u3ehi3]
                        · have p760_0 := h760c.1
                          have p760_1 := h760c.2.1
                          have p760_2 := h760c.2.2.1
                          have p760_3 := h760c.2.2.2
                          linarith only [h753, hlam, p760_0]
                        · have p760_0 := h760c.1
                          have p760_1 := h760c.2.1
                          have p760_2 := h760c.2.2.1
                          have p760_3 := h760c.2.2.2
                          linarith only [h1, h665, h753, h756, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p760_1, u3ehi3]
                        · have p760_0 := h760c.1
                          have p760_1 := h760c.2.1
                          have p760_2 := h760c.2.2.1
                          have p760_3 := h760c.2.2.2
                          linarith only [hlam, p760_0]
                    · linarith only [h0, h4, h665, h756, h757, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1, h4, h753, h756, hc34, hlam, hphi, u3ehi4]
              · linarith only [h752, h753, hc35, hlam, hphi, u3ehi3]
            · linarith only [h663, h665, h752, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h794 | h794
          · rcases m.htr 1 3 4 (by decide) (by decide) with h795 | h795
            · rcases m.htr 1 3 5 (by decide) (by decide) with h796 | h796
              · rcases m.htr 1 4 5 (by decide) (by decide) with h797 | h797
                · rcases m.htr 2 3 4 (by decide) (by decide) with h798 | h798
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h799 | h799
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h800 | h800
                      · rcases h1bigk with h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c
                        · have p801_0 := h801c.1
                          have p801_1 := h801c.2.1
                          have p801_2 := h801c.2.2.1
                          have p801_3 := h801c.2.2.2
                          linarith only [hlam, p801_0]
                        · have p801_0 := h801c.1
                          have p801_1 := h801c.2.1
                          have p801_2 := h801c.2.2.1
                          have p801_3 := h801c.2.2.2
                          linarith only [h794, h799, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p801_1, u3ehi4]
                        · have p801_0 := h801c.1
                          have p801_1 := h801c.2.1
                          have p801_2 := h801c.2.2.1
                          have p801_3 := h801c.2.2.2
                          linarith only [h665, h794, h795, h799, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p801_1, u3ehi4]
                        · have p801_0 := h801c.1
                          have p801_1 := h801c.2.1
                          have p801_2 := h801c.2.2.1
                          have p801_3 := h801c.2.2.2
                          linarith only [h665, h794, h799, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p801_1, u3ehi4]
                        · have p801_0 := h801c.1
                          have p801_1 := h801c.2.1
                          have p801_2 := h801c.2.2.1
                          have p801_3 := h801c.2.2.2
                          rcases p801_3 (m.d 0 1) (by simp) with h806 | h806
                          · rcases p801_3 (m.d 1 2) (by simp) with h807 | h807
                            · linarith only [h0, h807, hlam]
                            · linarith only [h794, h807, hlam]
                          · linarith only [h806, hlam, p801_0]
                        · have p801_0 := h801c.1
                          have p801_1 := h801c.2.1
                          have p801_2 := h801c.2.2.1
                          have p801_3 := h801c.2.2.2
                          linarith only [h0, hlam, p801_0]
                        · have p801_0 := h801c.1
                          have p801_1 := h801c.2.1
                          have p801_2 := h801c.2.2.1
                          have p801_3 := h801c.2.2.2
                          linarith only [hlam, p801_0]
                        · have p801_0 := h801c.1
                          have p801_1 := h801c.2.1
                          have p801_2 := h801c.2.2.1
                          have p801_3 := h801c.2.2.2
                          linarith only [h663, hlam, p801_0]
                        · have p801_0 := h801c.1
                          have p801_1 := h801c.2.1
                          have p801_2 := h801c.2.2.1
                          have p801_3 := h801c.2.2.2
                          linarith only [h665, hlam, p801_0]
                        · have p801_0 := h801c.1
                          have p801_1 := h801c.2.1
                          have p801_2 := h801c.2.2.1
                          have p801_3 := h801c.2.2.2
                          linarith only [h665, h794, h799, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p801_1, u3ehi4]
                        · have p801_0 := h801c.1
                          have p801_1 := h801c.2.1
                          have p801_2 := h801c.2.2.1
                          have p801_3 := h801c.2.2.2
                          linarith only [h1, hlam, p801_0]
                        · have p801_0 := h801c.1
                          have p801_1 := h801c.2.1
                          have p801_2 := h801c.2.2.1
                          have p801_3 := h801c.2.2.2
                          linarith only [h1, h794, h799, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p801_1, u3ehi4]
                        · have p801_0 := h801c.1
                          have p801_1 := h801c.2.1
                          have p801_2 := h801c.2.2.1
                          have p801_3 := h801c.2.2.2
                          linarith only [hlam, p801_0]
                        · have p801_0 := h801c.1
                          have p801_1 := h801c.2.1
                          have p801_2 := h801c.2.2.1
                          have p801_3 := h801c.2.2.2
                          linarith only [h1, h665, h794, h799, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p801_1, u3ehi4]
                        · have p801_0 := h801c.1
                          have p801_1 := h801c.2.1
                          have p801_2 := h801c.2.2.1
                          have p801_3 := h801c.2.2.2
                          linarith only [h1, h794, h799, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p801_1, u3ehi4]
                        · have p801_0 := h801c.1
                          have p801_1 := h801c.2.1
                          have p801_2 := h801c.2.2.1
                          have p801_3 := h801c.2.2.2
                          linarith only [h2, hlam, p801_0]
                        · have p801_0 := h801c.1
                          have p801_1 := h801c.2.1
                          have p801_2 := h801c.2.2.1
                          have p801_3 := h801c.2.2.2
                          linarith only [h794, h799, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p801_1, u3ehi4]
                        · have p801_0 := h801c.1
                          have p801_1 := h801c.2.1
                          have p801_2 := h801c.2.2.1
                          have p801_3 := h801c.2.2.2
                          linarith only [h795, hlam, p801_0]
                        · have p801_0 := h801c.1
                          have p801_1 := h801c.2.1
                          have p801_2 := h801c.2.2.1
                          have p801_3 := h801c.2.2.2
                          linarith only [hlam, p801_0]
                        · have p801_0 := h801c.1
                          have p801_1 := h801c.2.1
                          have p801_2 := h801c.2.2.1
                          have p801_3 := h801c.2.2.2
                          linarith only [h1, h794, h795, h799, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p801_1, u3ehi4]
                        · have p801_0 := h801c.1
                          have p801_1 := h801c.2.1
                          have p801_2 := h801c.2.2.1
                          have p801_3 := h801c.2.2.2
                          linarith only [h3, hlam, p801_0]
                        · have p801_0 := h801c.1
                          have p801_1 := h801c.2.1
                          have p801_2 := h801c.2.2.1
                          have p801_3 := h801c.2.2.2
                          linarith only [h794, hlam, p801_1]
                        · have p801_0 := h801c.1
                          have p801_1 := h801c.2.1
                          have p801_2 := h801c.2.2.1
                          have p801_3 := h801c.2.2.2
                          linarith only [h796, hlam, p801_0]
                        · have p801_0 := h801c.1
                          have p801_1 := h801c.2.1
                          have p801_2 := h801c.2.2.1
                          have p801_3 := h801c.2.2.2
                          linarith only [h797, hlam, p801_0]
                        · have p801_0 := h801c.1
                          have p801_1 := h801c.2.1
                          have p801_2 := h801c.2.2.1
                          have p801_3 := h801c.2.2.2
                          linarith only [hlam, p801_0]
                      · linarith only [h1, h795, h797, h800, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h4, h661, h799, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1, h4, h795, h798, hlam]
                · linarith only [h665, h794, h797, hlam]
              · linarith only [h795, h796, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h836 | h836
              · linarith only [h661, h795, h836, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
              · linarith only [h663, h794, h836, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h839 | h839
            · rcases m.htr 1 3 5 (by decide) (by decide) with h840 | h840
              · rcases m.htr 1 4 5 (by decide) (by decide) with h841 | h841
                · rcases m.htr 2 3 4 (by decide) (by decide) with h842 | h842
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h843 | h843
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h844 | h844
                      · rcases h1bigk with h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [hlam, p845_0]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          rcases p845_3 (m.d 0 1) (by simp) with h847 | h847
                          · rcases p845_3 (m.d 1 2) (by simp) with h848 | h848
                            · linarith only [h848, hlam, p845_0]
                            · rcases p845_3 (m.d 1 3) (by simp) with h850 | h850
                              · linarith only [h1, h850, hlam]
                              · linarith only [h663, h850, hlam]
                          · linarith only [h847, hlam, p845_0]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [h839, h844, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p845_1, u3ehi4]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          rcases p845_3 (m.d 0 1) (by simp) with h855 | h855
                          · rcases p845_3 (m.d 1 2) (by simp) with h856 | h856
                            · linarith only [h0, h856, hlam]
                            · rcases p845_3 (m.d 1 3) (by simp) with h858 | h858
                              · linarith only [h1, h858, hlam]
                              · linarith only [h839, h858, hlam]
                          · linarith only [h855, hlam, p845_0]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          rcases p845_3 (m.d 0 1) (by simp) with h862 | h862
                          · rcases p845_3 (m.d 1 2) (by simp) with h863 | h863
                            · linarith only [h0, h863, hlam]
                            · rcases p845_3 (m.d 1 3) (by simp) with h865 | h865
                              · linarith only [h1, h865, hlam]
                              · linarith only [h840, h865, hlam]
                          · linarith only [h862, hlam, p845_0]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [h0, hlam, p845_0]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [hlam, p845_0]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [h663, hlam, p845_0]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [h665, hlam, p845_0]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [h794, hlam, p845_0]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [h1, hlam, p845_0]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          rcases p845_3 (m.d 0 1) (by simp) with h875 | h875
                          · rcases p845_3 (m.d 1 2) (by simp) with h876 | h876
                            · linarith only [h663, h876, hlam]
                            · rcases p845_3 (m.d 1 3) (by simp) with h878 | h878
                              · rcases p845_3 (m.d 1 4) (by simp) with h879 | h879
                                · linarith only [h839, h879, hlam]
                                · linarith only [h665, h879, hlam]
                              · linarith only [h663, h878, hlam]
                          · linarith only [h0, h875, hlam]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [hlam, p845_0]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [h1, h839, h844, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p845_1, u3ehi4]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [h1, h840, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p845_1, u3ehi4]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [h2, hlam, p845_0]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          rcases p845_3 (m.d 0 1) (by simp) with h888 | h888
                          · rcases p845_3 (m.d 1 2) (by simp) with h889 | h889
                            · linarith only [h665, h889, hlam]
                            · rcases p845_3 (m.d 1 3) (by simp) with h891 | h891
                              · rcases p845_3 (m.d 1 4) (by simp) with h892 | h892
                                · rcases p845_3 (m.d 1 5) (by simp) with h893 | h893
                                  · linarith only [h841, h893, hlam]
                                  · linarith only [h794, h893, hlam]
                                · linarith only [h665, h892, hlam]
                              · linarith only [h663, h891, hlam]
                          · linarith only [h0, h888, hlam]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [h839, hlam, p845_0]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [hlam, p845_0]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [h1, h839, h840, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p845_1, u3ehi4]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [h3, hlam, p845_0]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          rcases p845_3 (m.d 0 1) (by simp) with h903 | h903
                          · rcases p845_3 (m.d 1 2) (by simp) with h904 | h904
                            · linarith only [h794, h904, hlam]
                            · rcases p845_3 (m.d 1 3) (by simp) with h906 | h906
                              · rcases p845_3 (m.d 1 4) (by simp) with h907 | h907
                                · rcases p845_3 (m.d 1 5) (by simp) with h908 | h908
                                  · rcases h3bigk with h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c
                                    · have p909_0 := h909c.1
                                      have p909_1 := h909c.2.1
                                      have p909_2 := h909c.2.2.1
                                      have p909_3 := h909c.2.2.2
                                      linarith only [hlam, p909_0]
                                    · have p909_0 := h909c.1
                                      have p909_1 := h909c.2.1
                                      have p909_2 := h909c.2.2.1
                                      have p909_3 := h909c.2.2.2
                                      linarith only [h4, h839, h841, hc12, hc23, hlam, hphi, p845_1, p909_1]
                                    · have p909_0 := h909c.1
                                      have p909_1 := h909c.2.1
                                      have p909_2 := h909c.2.2.1
                                      have p909_3 := h909c.2.2.2
                                      linarith only [h4, hlam, p909_1]
                                    · have p909_0 := h909c.1
                                      have p909_1 := h909c.2.1
                                      have p909_2 := h909c.2.2.1
                                      have p909_3 := h909c.2.2.2
                                      rcases p909_3 (m.d 0 3) (by simp) with h913 | h913
                                      · rcases p909_3 (m.d 1 3) (by simp) with h914 | h914
                                        · linarith only [h1, h914, hlam]
                                        · linarith only [h839, h914, hlam]
                                      · linarith only [h913, hlam, p909_0]
                                    · have p909_0 := h909c.1
                                      have p909_1 := h909c.2.1
                                      have p909_2 := h909c.2.2.1
                                      have p909_3 := h909c.2.2.2
                                      rcases p909_3 (m.d 0 3) (by simp) with h918 | h918
                                      · rcases p909_3 (m.d 1 3) (by simp) with h919 | h919
                                        · linarith only [h1, h919, hlam]
                                        · linarith only [h840, h919, hlam]
                                      · linarith only [h918, hlam, p909_0]
                                    · have p909_0 := h909c.1
                                      have p909_1 := h909c.2.1
                                      have p909_2 := h909c.2.2.1
                                      have p909_3 := h909c.2.2.2
                                      linarith only [h1, hlam, p909_0]
                                    · have p909_0 := h909c.1
                                      have p909_1 := h909c.2.1
                                      have p909_2 := h909c.2.2.1
                                      have p909_3 := h909c.2.2.2
                                      linarith only [hlam, p909_0]
                                    · have p909_0 := h909c.1
                                      have p909_1 := h909c.2.1
                                      have p909_2 := h909c.2.2.1
                                      have p909_3 := h909c.2.2.2
                                      linarith only [h663, hlam, p909_1]
                                    · have p909_0 := h909c.1
                                      have p909_1 := h909c.2.1
                                      have p909_2 := h909c.2.2.1
                                      have p909_3 := h909c.2.2.2
                                      linarith only [h1, h844, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p909_1, u3ehi4]
                                    · have p909_0 := h909c.1
                                      have p909_1 := h909c.2.1
                                      have p909_2 := h909c.2.2.1
                                      have p909_3 := h909c.2.2.2
                                      linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p909_1, u3ehi4]
                                    · have p909_0 := h909c.1
                                      have p909_1 := h909c.2.1
                                      have p909_2 := h909c.2.2.1
                                      have p909_3 := h909c.2.2.2
                                      linarith only [h1, h839, h841, hc12, hc23, hlam, hphi, p845_1, p909_1]
                                    · have p909_0 := h909c.1
                                      have p909_1 := h909c.2.1
                                      have p909_2 := h909c.2.2.1
                                      have p909_3 := h909c.2.2.2
                                      linarith only [h839, h841, hc12, hc23, hlam, hphi, p845_1, p909_1]
                                    · have p909_0 := h909c.1
                                      have p909_1 := h909c.2.1
                                      have p909_2 := h909c.2.2.1
                                      have p909_3 := h909c.2.2.2
                                      linarith only [hlam, p909_0]
                                    · have p909_0 := h909c.1
                                      have p909_1 := h909c.2.1
                                      have p909_2 := h909c.2.2.1
                                      have p909_3 := h909c.2.2.2
                                      rcases p909_3 (m.d 0 3) (by simp) with h931 | h931
                                      · linarith only [h4, h931, hlam]
                                      · linarith only [h661, h931, hlam]
                                    · have p909_0 := h909c.1
                                      have p909_1 := h909c.2.1
                                      have p909_2 := h909c.2.2.1
                                      have p909_3 := h909c.2.2.2
                                      rcases p909_3 (m.d 0 3) (by simp) with h934 | h934
                                      · linarith only [h4, h934, hlam]
                                      · linarith only [h662, h934, hlam]
                                    · have p909_0 := h909c.1
                                      have p909_1 := h909c.2.1
                                      have p909_2 := h909c.2.2.1
                                      have p909_3 := h909c.2.2.2
                                      linarith only [h661, hlam, p909_0]
                                    · have p909_0 := h909c.1
                                      have p909_1 := h909c.2.1
                                      have p909_2 := h909c.2.2.1
                                      have p909_3 := h909c.2.2.2
                                      linarith only [h839, hlam, p909_0]
                                    · have p909_0 := h909c.1
                                      have p909_1 := h909c.2.1
                                      have p909_2 := h909c.2.2.1
                                      have p909_3 := h909c.2.2.2
                                      linarith only [h842, hlam, p909_0]
                                    · have p909_0 := h909c.1
                                      have p909_1 := h909c.2.1
                                      have p909_2 := h909c.2.2.1
                                      have p909_3 := h909c.2.2.2
                                      linarith only [hlam, p909_0]
                                    · have p909_0 := h909c.1
                                      have p909_1 := h909c.2.1
                                      have p909_2 := h909c.2.2.1
                                      have p909_3 := h909c.2.2.2
                                      linarith only [hc34, hlam, hphi, p909_1, u3ehi4]
                                    · have p909_0 := h909c.1
                                      have p909_1 := h909c.2.1
                                      have p909_2 := h909c.2.2.1
                                      have p909_3 := h909c.2.2.2
                                      linarith only [h662, hlam, p909_0]
                                    · have p909_0 := h909c.1
                                      have p909_1 := h909c.2.1
                                      have p909_2 := h909c.2.2.1
                                      have p909_3 := h909c.2.2.2
                                      linarith only [h840, hlam, p909_0]
                                    · have p909_0 := h909c.1
                                      have p909_1 := h909c.2.1
                                      have p909_2 := h909c.2.2.1
                                      have p909_3 := h909c.2.2.2
                                      linarith only [h843, hlam, p909_0]
                                    · have p909_0 := h909c.1
                                      have p909_1 := h909c.2.1
                                      have p909_2 := h909c.2.2.1
                                      have p909_3 := h909c.2.2.2
                                      linarith only [h844, hlam, p909_0]
                                    · have p909_0 := h909c.1
                                      have p909_1 := h909c.2.1
                                      have p909_2 := h909c.2.2.1
                                      have p909_3 := h909c.2.2.2
                                      linarith only [hlam, p909_0]
                                  · linarith only [h794, h908, hlam]
                                · linarith only [h665, h907, hlam]
                              · linarith only [h663, h906, hlam]
                          · linarith only [h0, h903, hlam]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [h840, hlam, p845_0]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [h841, hlam, p845_0]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [hlam, p845_0]
                      · linarith only [h1, h839, h841, h844, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h4, h661, h843, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1, h4, h839, h842, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h957 | h957
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h958 | h958
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h959 | h959
                      · linarith only [h1, h839, h841, h959, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases h1bigk with h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c | h961c
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [hlam, p961_0]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          rcases p961_3 (m.d 0 1) (by simp) with h963 | h963
                          · rcases p961_3 (m.d 1 2) (by simp) with h964 | h964
                            · linarith only [h964, hlam, p961_0]
                            · rcases p961_3 (m.d 1 3) (by simp) with h966 | h966
                              · linarith only [h1, h966, hlam]
                              · linarith only [h663, h966, hlam]
                          · linarith only [h963, hlam, p961_0]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [h840, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p961_1, u3ehi4]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          rcases p961_3 (m.d 0 1) (by simp) with h971 | h971
                          · rcases p961_3 (m.d 1 2) (by simp) with h972 | h972
                            · linarith only [h0, h972, hlam]
                            · rcases p961_3 (m.d 1 3) (by simp) with h974 | h974
                              · linarith only [h1, h974, hlam]
                              · linarith only [h839, h974, hlam]
                          · linarith only [h971, hlam, p961_0]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          rcases p961_3 (m.d 0 1) (by simp) with h978 | h978
                          · rcases p961_3 (m.d 1 2) (by simp) with h979 | h979
                            · linarith only [h0, h979, hlam]
                            · rcases p961_3 (m.d 1 3) (by simp) with h981 | h981
                              · linarith only [h1, h981, hlam]
                              · linarith only [h840, h981, hlam]
                          · linarith only [h978, hlam, p961_0]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [h0, hlam, p961_0]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [hlam, p961_0]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [h663, hlam, p961_0]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [h665, hlam, p961_0]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [h794, hlam, p961_0]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [h1, hlam, p961_0]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          rcases p961_3 (m.d 0 1) (by simp) with h991 | h991
                          · rcases p961_3 (m.d 1 2) (by simp) with h992 | h992
                            · linarith only [h663, h992, hlam]
                            · rcases p961_3 (m.d 1 3) (by simp) with h994 | h994
                              · rcases p961_3 (m.d 1 4) (by simp) with h995 | h995
                                · linarith only [h839, h995, hlam]
                                · linarith only [h665, h995, hlam]
                              · linarith only [h663, h994, hlam]
                          · linarith only [h0, h991, hlam]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [hlam, p961_0]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [h1, h839, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p961_1, u3ehi3]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [h1, h840, h959, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p961_1, u3ehi3]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [h2, hlam, p961_0]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [h841, hc12, hc45, hlam, hphi, ht23, ht34, p961_1]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [h839, hlam, p961_0]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [hlam, p961_0]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [h841, hlam, p961_1]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [h3, hlam, p961_0]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          rcases p961_3 (m.d 0 1) (by simp) with h1009 | h1009
                          · rcases p961_3 (m.d 1 2) (by simp) with h1010 | h1010
                            · linarith only [h1010, h794, hlam]
                            · rcases p961_3 (m.d 1 3) (by simp) with h1012 | h1012
                              · rcases p961_3 (m.d 1 4) (by simp) with h1013 | h1013
                                · linarith only [h1013, h841, hlam]
                                · linarith only [h1013, h665, hlam]
                              · linarith only [h1012, h663, hlam]
                          · linarith only [h0, h1009, hlam]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [h840, hlam, p961_0]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [h3, h839, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p961_1, u3ehi3]
                        · have p961_0 := h961c.1
                          have p961_1 := h961c.2.1
                          have p961_2 := h961c.2.2.1
                          have p961_3 := h961c.2.2.2
                          linarith only [hlam, p961_0]
                    · linarith only [h4, h661, h958, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1, h4, h839, h957, hlam]
              · linarith only [h839, h840, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1024 | h1024
              · linarith only [h1024, h4, h661, h839, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1026 | h1026
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1027 | h1027
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1028 | h1028
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1029 | h1029
                      · rcases h1bigk with h1030c | h1030c | h1030c | h1030c | h1030c | h1030c | h1030c | h1030c | h1030c | h1030c | h1030c | h1030c | h1030c | h1030c | h1030c | h1030c | h1030c | h1030c | h1030c | h1030c | h1030c | h1030c | h1030c | h1030c | h1030c
                        · have p1030_0 := h1030c.1
                          have p1030_1 := h1030c.2.1
                          have p1030_2 := h1030c.2.2.1
                          have p1030_3 := h1030c.2.2.2
                          linarith only [hlam, p1030_0]
                        · have p1030_0 := h1030c.1
                          have p1030_1 := h1030c.2.1
                          have p1030_2 := h1030c.2.2.1
                          have p1030_3 := h1030c.2.2.2
                          rcases p1030_3 (m.d 0 1) (by simp) with h1032 | h1032
                          · rcases p1030_3 (m.d 1 2) (by simp) with h1033 | h1033
                            · linarith only [h1033, hlam, p1030_0]
                            · rcases p1030_3 (m.d 1 3) (by simp) with h1035 | h1035
                              · linarith only [h1, h1035, hlam]
                              · linarith only [h1035, h663, hlam]
                          · linarith only [h1032, hlam, p1030_0]
                        · have p1030_0 := h1030c.1
                          have p1030_1 := h1030c.2.1
                          have p1030_2 := h1030c.2.2.1
                          have p1030_3 := h1030c.2.2.2
                          rcases p1030_3 (m.d 0 1) (by simp) with h1039 | h1039
                          · rcases p1030_3 (m.d 1 2) (by simp) with h1040 | h1040
                            · linarith only [h0, h1040, hlam]
                            · rcases p1030_3 (m.d 1 3) (by simp) with h1042 | h1042
                              · linarith only [h1042, hlam, p1030_0]
                              · rcases p1030_3 (m.d 1 4) (by simp) with h1044 | h1044
                                · linarith only [h1044, h2, hlam]
                                · linarith only [h1044, h839, hlam]
                          · linarith only [h1039, hlam, p1030_0]
                        · have p1030_0 := h1030c.1
                          have p1030_1 := h1030c.2.1
                          have p1030_2 := h1030c.2.2.1
                          have p1030_3 := h1030c.2.2.2
                          rcases p1030_3 (m.d 0 1) (by simp) with h1048 | h1048
                          · rcases p1030_3 (m.d 1 2) (by simp) with h1049 | h1049
                            · linarith only [h0, h1049, hlam]
                            · rcases p1030_3 (m.d 1 3) (by simp) with h1051 | h1051
                              · linarith only [h1, h1051, hlam]
                              · rcases p1030_3 (m.d 1 4) (by simp) with h1053 | h1053
                                · linarith only [h1053, hlam, p1030_0]
                                · rcases p1030_3 (m.d 1 5) (by simp) with h1055 | h1055
                                  · linarith only [h1055, h3, hlam]
                                  · rcases h3bigk with h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c
                                    · have p1057_0 := h1057c.1
                                      have p1057_1 := h1057c.2.1
                                      have p1057_2 := h1057c.2.2.1
                                      have p1057_3 := h1057c.2.2.2
                                      linarith only [hlam, p1057_0]
                                    · have p1057_0 := h1057c.1
                                      have p1057_1 := h1057c.2.1
                                      have p1057_2 := h1057c.2.2.1
                                      have p1057_3 := h1057c.2.2.2
                                      rcases p1057_3 (m.d 0 3) (by simp) with h1059 | h1059
                                      · rcases p1057_3 (m.d 1 3) (by simp) with h1060 | h1060
                                        · linarith only [h1, h1060, hlam]
                                        · rcases p1057_3 (m.d 2 3) (by simp) with h1062 | h1062
                                          · rcases p1057_3 (m.d 3 4) (by simp) with h1063 | h1063
                                            · linarith only [h1063, h661, hlam]
                                            · linarith only [h1063, h839, hlam]
                                          · linarith only [h1062, h663, hlam]
                                      · linarith only [h1, h1059, hlam]
                                    · have p1057_0 := h1057c.1
                                      have p1057_1 := h1057c.2.1
                                      have p1057_2 := h1057c.2.2.1
                                      have p1057_3 := h1057c.2.2.2
                                      linarith only [h4, hlam, p1057_1]
                                    · have p1057_0 := h1057c.1
                                      have p1057_1 := h1057c.2.1
                                      have p1057_2 := h1057c.2.2.1
                                      have p1057_3 := h1057c.2.2.2
                                      linarith only [h1024, h1029, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1057_1, u3ehi1]
                                    · have p1057_0 := h1057c.1
                                      have p1057_1 := h1057c.2.1
                                      have p1057_2 := h1057c.2.2.1
                                      have p1057_3 := h1057c.2.2.2
                                      linarith only [h1024, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1057_1, u3ehi1]
                                    · have p1057_0 := h1057c.1
                                      have p1057_1 := h1057c.2.1
                                      have p1057_2 := h1057c.2.2.1
                                      have p1057_3 := h1057c.2.2.2
                                      linarith only [h1, hlam, p1057_0]
                                    · have p1057_0 := h1057c.1
                                      have p1057_1 := h1057c.2.1
                                      have p1057_2 := h1057c.2.2.1
                                      have p1057_3 := h1057c.2.2.2
                                      linarith only [hlam, p1057_0]
                                    · have p1057_0 := h1057c.1
                                      have p1057_1 := h1057c.2.1
                                      have p1057_2 := h1057c.2.2.1
                                      have p1057_3 := h1057c.2.2.2
                                      linarith only [h663, hlam, p1057_1]
                                    · have p1057_0 := h1057c.1
                                      have p1057_1 := h1057c.2.1
                                      have p1057_2 := h1057c.2.2.1
                                      have p1057_3 := h1057c.2.2.2
                                      linarith only [h839, hlam, p1057_0]
                                    · have p1057_0 := h1057c.1
                                      have p1057_1 := h1057c.2.1
                                      have p1057_2 := h1057c.2.2.1
                                      have p1057_3 := h1057c.2.2.2
                                      linarith only [h1024, hlam, p1057_0]
                                    · have p1057_0 := h1057c.1
                                      have p1057_1 := h1057c.2.1
                                      have p1057_2 := h1057c.2.2.1
                                      have p1057_3 := h1057c.2.2.2
                                      linarith only [h1024, h1029, h661, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1057_1, u3ehi1]
                                    · have p1057_0 := h1057c.1
                                      have p1057_1 := h1057c.2.1
                                      have p1057_2 := h1057c.2.2.1
                                      have p1057_3 := h1057c.2.2.2
                                      rcases p1057_3 (m.d 0 3) (by simp) with h1077 | h1077
                                      · linarith only [h1077, h4, hlam]
                                      · linarith only [h1, h1077, hlam]
                                    · have p1057_0 := h1057c.1
                                      have p1057_1 := h1057c.2.1
                                      have p1057_2 := h1057c.2.2.1
                                      have p1057_3 := h1057c.2.2.2
                                      linarith only [hlam, p1057_0]
                                    · have p1057_0 := h1057c.1
                                      have p1057_1 := h1057c.2.1
                                      have p1057_2 := h1057c.2.2.1
                                      have p1057_3 := h1057c.2.2.2
                                      linarith only [h1024, h1029, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1057_1, u3ehi1]
                                    · have p1057_0 := h1057c.1
                                      have p1057_1 := h1057c.2.1
                                      have p1057_2 := h1057c.2.2.1
                                      have p1057_3 := h1057c.2.2.2
                                      linarith only [h1024, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1057_1, u3ehi1]
                                    · have p1057_0 := h1057c.1
                                      have p1057_1 := h1057c.2.1
                                      have p1057_2 := h1057c.2.2.1
                                      have p1057_3 := h1057c.2.2.2
                                      linarith only [h661, hlam, p1057_0]
                                    · have p1057_0 := h1057c.1
                                      have p1057_1 := h1057c.2.1
                                      have p1057_2 := h1057c.2.2.1
                                      have p1057_3 := h1057c.2.2.2
                                      linarith only [h661, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1057_1, u3ehi1]
                                    · have p1057_0 := h1057c.1
                                      have p1057_1 := h1057c.2.1
                                      have p1057_2 := h1057c.2.2.1
                                      have p1057_3 := h1057c.2.2.2
                                      linarith only [h1027, hlam, p1057_0]
                                    · have p1057_0 := h1057c.1
                                      have p1057_1 := h1057c.2.1
                                      have p1057_2 := h1057c.2.2.1
                                      have p1057_3 := h1057c.2.2.2
                                      linarith only [hlam, p1057_0]
                                    · have p1057_0 := h1057c.1
                                      have p1057_1 := h1057c.2.1
                                      have p1057_2 := h1057c.2.2.1
                                      have p1057_3 := h1057c.2.2.2
                                      linarith only [h1024, h4, h661, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1057_1, u3ehi1]
                                    · have p1057_0 := h1057c.1
                                      have p1057_1 := h1057c.2.1
                                      have p1057_2 := h1057c.2.2.1
                                      have p1057_3 := h1057c.2.2.2
                                      linarith only [h662, hlam, p1057_0]
                                    · have p1057_0 := h1057c.1
                                      have p1057_1 := h1057c.2.1
                                      have p1057_2 := h1057c.2.2.1
                                      have p1057_3 := h1057c.2.2.2
                                      linarith only [hc35, hlam, hphi, p1057_1, u3ehi1]
                                    · have p1057_0 := h1057c.1
                                      have p1057_1 := h1057c.2.1
                                      have p1057_2 := h1057c.2.2.1
                                      have p1057_3 := h1057c.2.2.2
                                      linarith only [h1028, hlam, p1057_0]
                                    · have p1057_0 := h1057c.1
                                      have p1057_1 := h1057c.2.1
                                      have p1057_2 := h1057c.2.2.1
                                      have p1057_3 := h1057c.2.2.2
                                      linarith only [h1029, hlam, p1057_0]
                                    · have p1057_0 := h1057c.1
                                      have p1057_1 := h1057c.2.1
                                      have p1057_2 := h1057c.2.2.1
                                      have p1057_3 := h1057c.2.2.2
                                      linarith only [hlam, p1057_0]
                          · linarith only [h1048, hlam, p1030_0]
                        · have p1030_0 := h1030c.1
                          have p1030_1 := h1030c.2.1
                          have p1030_2 := h1030c.2.2.1
                          have p1030_3 := h1030c.2.2.2
                          rcases p1030_3 (m.d 0 1) (by simp) with h1094 | h1094
                          · rcases p1030_3 (m.d 1 2) (by simp) with h1095 | h1095
                            · linarith only [h0, h1095, hlam]
                            · rcases p1030_3 (m.d 1 3) (by simp) with h1097 | h1097
                              · linarith only [h1, h1097, hlam]
                              · rcases p1030_3 (m.d 1 4) (by simp) with h1099 | h1099
                                · linarith only [h1099, h2, hlam]
                                · linarith only [h1026, h1099, hlam]
                          · linarith only [h1094, hlam, p1030_0]
                        · have p1030_0 := h1030c.1
                          have p1030_1 := h1030c.2.1
                          have p1030_2 := h1030c.2.2.1
                          have p1030_3 := h1030c.2.2.2
                          linarith only [h0, hlam, p1030_0]
                        · have p1030_0 := h1030c.1
                          have p1030_1 := h1030c.2.1
                          have p1030_2 := h1030c.2.2.1
                          have p1030_3 := h1030c.2.2.2
                          linarith only [hlam, p1030_0]
                        · have p1030_0 := h1030c.1
                          have p1030_1 := h1030c.2.1
                          have p1030_2 := h1030c.2.2.1
                          have p1030_3 := h1030c.2.2.2
                          linarith only [h663, hlam, p1030_0]
                        · have p1030_0 := h1030c.1
                          have p1030_1 := h1030c.2.1
                          have p1030_2 := h1030c.2.2.1
                          have p1030_3 := h1030c.2.2.2
                          linarith only [h665, hlam, p1030_0]
                        · have p1030_0 := h1030c.1
                          have p1030_1 := h1030c.2.1
                          have p1030_2 := h1030c.2.2.1
                          have p1030_3 := h1030c.2.2.2
                          linarith only [h794, hlam, p1030_0]
                        · have p1030_0 := h1030c.1
                          have p1030_1 := h1030c.2.1
                          have p1030_2 := h1030c.2.2.1
                          have p1030_3 := h1030c.2.2.2
                          linarith only [h1, hlam, p1030_0]
                        · have p1030_0 := h1030c.1
                          have p1030_1 := h1030c.2.1
                          have p1030_2 := h1030c.2.2.1
                          have p1030_3 := h1030c.2.2.2
                          linarith only [h4, h661, h839, hc12, hc23, hlam, hphi, p1030_1]
                        · have p1030_0 := h1030c.1
                          have p1030_1 := h1030c.2.1
                          have p1030_2 := h1030c.2.2.1
                          have p1030_3 := h1030c.2.2.2
                          linarith only [hlam, p1030_0]
                        · have p1030_0 := h1030c.1
                          have p1030_1 := h1030c.2.1
                          have p1030_2 := h1030c.2.2.1
                          have p1030_3 := h1030c.2.2.2
                          linarith only [h839, hlam, p1030_1]
                        · have p1030_0 := h1030c.1
                          have p1030_1 := h1030c.2.1
                          have p1030_2 := h1030c.2.2.1
                          have p1030_3 := h1030c.2.2.2
                          linarith only [h1024, hlam, p1030_1]
                        · have p1030_0 := h1030c.1
                          have p1030_1 := h1030c.2.1
                          have p1030_2 := h1030c.2.2.1
                          have p1030_3 := h1030c.2.2.2
                          linarith only [h2, hlam, p1030_0]
                        · have p1030_0 := h1030c.1
                          have p1030_1 := h1030c.2.1
                          have p1030_2 := h1030c.2.2.1
                          have p1030_3 := h1030c.2.2.2
                          linarith only [h4, h661, h839, hc12, hc23, hlam, hphi, p1030_1]
                        · have p1030_0 := h1030c.1
                          have p1030_1 := h1030c.2.1
                          have p1030_2 := h1030c.2.2.1
                          have p1030_3 := h1030c.2.2.2
                          linarith only [h4, h661, h839, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1030_1, u3ehi1]
                        · have p1030_0 := h1030c.1
                          have p1030_1 := h1030c.2.1
                          have p1030_2 := h1030c.2.2.1
                          have p1030_3 := h1030c.2.2.2
                          linarith only [hlam, p1030_0]
                        · have p1030_0 := h1030c.1
                          have p1030_1 := h1030c.2.1
                          have p1030_2 := h1030c.2.2.1
                          have p1030_3 := h1030c.2.2.2
                          linarith only [h4, h661, h794, h839, hc12, hc23, hlam, hphi, p1030_1]
                        · have p1030_0 := h1030c.1
                          have p1030_1 := h1030c.2.1
                          have p1030_2 := h1030c.2.2.1
                          have p1030_3 := h1030c.2.2.2
                          linarith only [h3, hlam, p1030_0]
                        · have p1030_0 := h1030c.1
                          have p1030_1 := h1030c.2.1
                          have p1030_2 := h1030c.2.2.1
                          have p1030_3 := h1030c.2.2.2
                          linarith only [h1024, h1029, h4, h661, hc12, hc23, hlam, hphi, p1030_1]
                        · have p1030_0 := h1030c.1
                          have p1030_1 := h1030c.2.1
                          have p1030_2 := h1030c.2.2.1
                          have p1030_3 := h1030c.2.2.2
                          linarith only [h1024, h1029, h4, h661, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1030_1, u3ehi1]
                        · have p1030_0 := h1030c.1
                          have p1030_1 := h1030c.2.1
                          have p1030_2 := h1030c.2.2.1
                          have p1030_3 := h1030c.2.2.2
                          linarith only [h1026, hlam, p1030_0]
                        · have p1030_0 := h1030c.1
                          have p1030_1 := h1030c.2.1
                          have p1030_2 := h1030c.2.2.1
                          have p1030_3 := h1030c.2.2.2
                          linarith only [hlam, p1030_0]
                      · linarith only [h1026, h1029, h839, hlam]
                    · linarith only [h1028, h4, h661, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1027, h4, h661, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1126 | h1126
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1127 | h1127
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1128 | h1128
                      · linarith only [h1026, h1128, h4, h661, h665, hc12, hc23, hlam, hphi]
                      · linarith only [h1128, h839, hc45, hlam, hphi, ht34, u3ehi1]
                    · linarith only [h1127, h4, h662, hlam]
                  · linarith only [h1126, h4, h661, hlam]
    · linarith only [h661, h662, hc35, hlam, hphi, u3ehi3]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1134 | h1134
    · linarith only [h1134, h661, hc34, hlam, hphi, u3ehi4]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1136 | h1136
      · linarith only [h0, h1136, h4, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1138 | h1138
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1139 | h1139
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1140 | h1140
            · linarith only [h1, h1140, h661, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
            · linarith only [h1136, h1138, h1140, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1143 | h1143
            · linarith only [h1, h1143, h661, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
            · linarith only [h1136, h1138, h1143, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1146 | h1146
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1147 | h1147
            · linarith only [h1, h1147, h661, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1149 | h1149
              · linarith only [h1, h1149, h661, hc34, hlam, hphi, u3ehi4]
              · linarith only [h1136, h1146, h1149, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1152 | h1152
            · linarith only [h1, h1152, h661, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1154 | h1154
              · linarith only [h1, h1154, h661, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1156 | h1156
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1157 | h1157
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1158 | h1158
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1159 | h1159
                      · rcases h1bigk with h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [hlam, p1160_0]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          rcases p1160_3 (m.d 0 1) (by simp) with h1162 | h1162
                          · rcases p1160_3 (m.d 1 2) (by simp) with h1163 | h1163
                            · linarith only [h1163, hlam, p1160_0]
                            · rcases p1160_3 (m.d 1 3) (by simp) with h1165 | h1165
                              · linarith only [h1, h1165, hlam]
                              · linarith only [h1136, h1165, hlam]
                          · linarith only [h1162, hlam, p1160_0]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          rcases p1160_3 (m.d 0 1) (by simp) with h1169 | h1169
                          · rcases p1160_3 (m.d 1 2) (by simp) with h1170 | h1170
                            · linarith only [h0, h1170, hlam]
                            · rcases p1160_3 (m.d 1 3) (by simp) with h1172 | h1172
                              · linarith only [h1172, hlam, p1160_0]
                              · rcases p1160_3 (m.d 1 4) (by simp) with h1174 | h1174
                                · linarith only [h1174, h2, hlam]
                                · linarith only [h1152, h1174, hlam]
                          · linarith only [h1169, hlam, p1160_0]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          rcases p1160_3 (m.d 0 1) (by simp) with h1178 | h1178
                          · rcases p1160_3 (m.d 1 2) (by simp) with h1179 | h1179
                            · linarith only [h0, h1179, hlam]
                            · rcases p1160_3 (m.d 1 3) (by simp) with h1181 | h1181
                              · linarith only [h1, h1181, hlam]
                              · rcases p1160_3 (m.d 1 4) (by simp) with h1183 | h1183
                                · linarith only [h1183, hlam, p1160_0]
                                · rcases p1160_3 (m.d 1 5) (by simp) with h1185 | h1185
                                  · linarith only [h1185, h3, hlam]
                                  · rcases h3bigk with h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c
                                    · have p1187_0 := h1187c.1
                                      have p1187_1 := h1187c.2.1
                                      have p1187_2 := h1187c.2.2.1
                                      have p1187_3 := h1187c.2.2.2
                                      linarith only [hlam, p1187_0]
                                    · have p1187_0 := h1187c.1
                                      have p1187_1 := h1187c.2.1
                                      have p1187_2 := h1187c.2.2.1
                                      have p1187_3 := h1187c.2.2.2
                                      linarith only [h1134, h1157, h1159, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1187_1, u3ehi1]
                                    · have p1187_0 := h1187c.1
                                      have p1187_1 := h1187c.2.1
                                      have p1187_2 := h1187c.2.2.1
                                      have p1187_3 := h1187c.2.2.2
                                      linarith only [h4, hlam, p1187_1]
                                    · have p1187_0 := h1187c.1
                                      have p1187_1 := h1187c.2.1
                                      have p1187_2 := h1187c.2.2.1
                                      have p1187_3 := h1187c.2.2.2
                                      linarith only [h661, hlam, p1187_0]
                                    · have p1187_0 := h1187c.1
                                      have p1187_1 := h1187c.2.1
                                      have p1187_2 := h1187c.2.2.1
                                      have p1187_3 := h1187c.2.2.2
                                      linarith only [h1134, hlam, p1187_0]
                                    · have p1187_0 := h1187c.1
                                      have p1187_1 := h1187c.2.1
                                      have p1187_2 := h1187c.2.2.1
                                      have p1187_3 := h1187c.2.2.2
                                      linarith only [h1, hlam, p1187_0]
                                    · have p1187_0 := h1187c.1
                                      have p1187_1 := h1187c.2.1
                                      have p1187_2 := h1187c.2.2.1
                                      have p1187_3 := h1187c.2.2.2
                                      linarith only [hlam, p1187_0]
                                    · have p1187_0 := h1187c.1
                                      have p1187_1 := h1187c.2.1
                                      have p1187_2 := h1187c.2.2.1
                                      have p1187_3 := h1187c.2.2.2
                                      linarith only [h1136, hlam, p1187_1]
                                    · have p1187_0 := h1187c.1
                                      have p1187_1 := h1187c.2.1
                                      have p1187_2 := h1187c.2.2.1
                                      have p1187_3 := h1187c.2.2.2
                                      linarith only [h1152, hlam, p1187_0]
                                    · have p1187_0 := h1187c.1
                                      have p1187_1 := h1187c.2.1
                                      have p1187_2 := h1187c.2.2.1
                                      have p1187_3 := h1187c.2.2.2
                                      linarith only [h1154, hlam, p1187_0]
                                    · have p1187_0 := h1187c.1
                                      have p1187_1 := h1187c.2.1
                                      have p1187_2 := h1187c.2.2.1
                                      have p1187_3 := h1187c.2.2.2
                                      rcases p1187_3 (m.d 0 3) (by simp) with h1198 | h1198
                                      · linarith only [h1198, h4, hlam]
                                      · rcases p1187_3 (m.d 1 3) (by simp) with h1200 | h1200
                                        · linarith only [h1136, h1200, hlam]
                                        · rcases p1187_3 (m.d 2 3) (by simp) with h1202 | h1202
                                          · rcases p1187_3 (m.d 3 4) (by simp) with h1203 | h1203
                                            · linarith only [h1157, h1203, hlam]
                                            · linarith only [h1203, h661, hlam]
                                          · linarith only [h1202, h4, hlam]
                                    · have p1187_0 := h1187c.1
                                      have p1187_1 := h1187c.2.1
                                      have p1187_2 := h1187c.2.2.1
                                      have p1187_3 := h1187c.2.2.2
                                      rcases p1187_3 (m.d 0 3) (by simp) with h1207 | h1207
                                      · linarith only [h1207, h4, hlam]
                                      · linarith only [h1, h1207, hlam]
                                    · have p1187_0 := h1187c.1
                                      have p1187_1 := h1187c.2.1
                                      have p1187_2 := h1187c.2.2.1
                                      have p1187_3 := h1187c.2.2.2
                                      linarith only [hlam, p1187_0]
                                    · have p1187_0 := h1187c.1
                                      have p1187_1 := h1187c.2.1
                                      have p1187_2 := h1187c.2.2.1
                                      have p1187_3 := h1187c.2.2.2
                                      linarith only [h1134, h1159, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1187_1, u3ehi0]
                                    · have p1187_0 := h1187c.1
                                      have p1187_1 := h1187c.2.1
                                      have p1187_2 := h1187c.2.2.1
                                      have p1187_3 := h1187c.2.2.2
                                      linarith only [h1, h1134, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1187_1, u3ehi1]
                                    · have p1187_0 := h1187c.1
                                      have p1187_1 := h1187c.2.1
                                      have p1187_2 := h1187c.2.2.1
                                      have p1187_3 := h1187c.2.2.2
                                      linarith only [h1, hc34, hlam, hphi, p1187_1, u3ehi1]
                                    · have p1187_0 := h1187c.1
                                      have p1187_1 := h1187c.2.1
                                      have p1187_2 := h1187c.2.2.1
                                      have p1187_3 := h1187c.2.2.2
                                      linarith only [hc34, hlam, hphi, p1187_1, u3ehi1]
                                    · have p1187_0 := h1187c.1
                                      have p1187_1 := h1187c.2.1
                                      have p1187_2 := h1187c.2.2.1
                                      have p1187_3 := h1187c.2.2.2
                                      linarith only [h1157, hlam, p1187_0]
                                    · have p1187_0 := h1187c.1
                                      have p1187_1 := h1187c.2.1
                                      have p1187_2 := h1187c.2.2.1
                                      have p1187_3 := h1187c.2.2.2
                                      linarith only [hlam, p1187_0]
                                    · have p1187_0 := h1187c.1
                                      have p1187_1 := h1187c.2.1
                                      have p1187_2 := h1187c.2.2.1
                                      have p1187_3 := h1187c.2.2.2
                                      linarith only [h1, h1134, h1157, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1187_1, u3ehi1]
                                    · have p1187_0 := h1187c.1
                                      have p1187_1 := h1187c.2.1
                                      have p1187_2 := h1187c.2.2.1
                                      have p1187_3 := h1187c.2.2.2
                                      linarith only [h1, hc35, hlam, hphi, p1187_1, u3ehi1]
                                    · have p1187_0 := h1187c.1
                                      have p1187_1 := h1187c.2.1
                                      have p1187_2 := h1187c.2.2.1
                                      have p1187_3 := h1187c.2.2.2
                                      linarith only [hc35, hlam, hphi, p1187_1, u3ehi1]
                                    · have p1187_0 := h1187c.1
                                      have p1187_1 := h1187c.2.1
                                      have p1187_2 := h1187c.2.2.1
                                      have p1187_3 := h1187c.2.2.2
                                      linarith only [h1158, hlam, p1187_0]
                                    · have p1187_0 := h1187c.1
                                      have p1187_1 := h1187c.2.1
                                      have p1187_2 := h1187c.2.2.1
                                      have p1187_3 := h1187c.2.2.2
                                      linarith only [h1159, hlam, p1187_0]
                                    · have p1187_0 := h1187c.1
                                      have p1187_1 := h1187c.2.1
                                      have p1187_2 := h1187c.2.2.1
                                      have p1187_3 := h1187c.2.2.2
                                      linarith only [hlam, p1187_0]
                          · linarith only [h1178, hlam, p1160_0]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          rcases p1160_3 (m.d 0 1) (by simp) with h1224 | h1224
                          · rcases p1160_3 (m.d 1 2) (by simp) with h1225 | h1225
                            · linarith only [h0, h1225, hlam]
                            · rcases p1160_3 (m.d 1 3) (by simp) with h1227 | h1227
                              · linarith only [h1, h1227, hlam]
                              · rcases p1160_3 (m.d 1 4) (by simp) with h1229 | h1229
                                · linarith only [h1229, h2, hlam]
                                · linarith only [h1156, h1229, hlam]
                          · linarith only [h1224, hlam, p1160_0]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h0, hlam, p1160_0]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [hlam, p1160_0]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h1136, hlam, p1160_0]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h1138, hlam, p1160_0]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h1146, hlam, p1160_0]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h1, hlam, p1160_0]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h1, h1157, h661, hc12, hc23, hlam, hphi, p1160_1]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [hlam, p1160_0]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h1152, hlam, p1160_1]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h1154, hlam, p1160_1]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h2, hlam, p1160_0]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h1157, h2, h661, hc12, hc23, hlam, hphi, p1160_1]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h1157, h2, h661, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1160_1, u3ehi1]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [hlam, p1160_0]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h1154, h1157, h2, h661, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1160_1, u3ehi1]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h3, hlam, p1160_0]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h1156, h1157, h2, h661, hc12, hc23, hlam, hphi, p1160_1]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h1134, h3, hc35, hlam, hphi, p1160_1, u3ehi1]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h1156, hlam, p1160_0]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [hlam, p1160_0]
                      · linarith only [h1156, h1159, h2, h661, hlam]
                    · linarith only [h1157, h1158, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1255 | h1255
                    · linarith only [h1157, h1255, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1257 | h1257
                      · rcases h1bigk with h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c
                        · have p1258_0 := h1258c.1
                          have p1258_1 := h1258c.2.1
                          have p1258_2 := h1258c.2.2.1
                          have p1258_3 := h1258c.2.2.2
                          linarith only [hlam, p1258_0]
                        · have p1258_0 := h1258c.1
                          have p1258_1 := h1258c.2.1
                          have p1258_2 := h1258c.2.2.1
                          have p1258_3 := h1258c.2.2.2
                          rcases p1258_3 (m.d 0 1) (by simp) with h1260 | h1260
                          · rcases p1258_3 (m.d 1 2) (by simp) with h1261 | h1261
                            · linarith only [h1261, hlam, p1258_0]
                            · rcases p1258_3 (m.d 1 3) (by simp) with h1263 | h1263
                              · linarith only [h1, h1263, hlam]
                              · linarith only [h1136, h1263, hlam]
                          · linarith only [h1260, hlam, p1258_0]
                        · have p1258_0 := h1258c.1
                          have p1258_1 := h1258c.2.1
                          have p1258_2 := h1258c.2.2.1
                          have p1258_3 := h1258c.2.2.2
                          rcases p1258_3 (m.d 0 1) (by simp) with h1267 | h1267
                          · rcases p1258_3 (m.d 1 2) (by simp) with h1268 | h1268
                            · linarith only [h0, h1268, hlam]
                            · rcases p1258_3 (m.d 1 3) (by simp) with h1270 | h1270
                              · linarith only [h1270, hlam, p1258_0]
                              · rcases p1258_3 (m.d 1 4) (by simp) with h1272 | h1272
                                · linarith only [h1272, h2, hlam]
                                · linarith only [h1152, h1272, hlam]
                          · linarith only [h1267, hlam, p1258_0]
                        · have p1258_0 := h1258c.1
                          have p1258_1 := h1258c.2.1
                          have p1258_2 := h1258c.2.2.1
                          have p1258_3 := h1258c.2.2.2
                          rcases p1258_3 (m.d 0 1) (by simp) with h1276 | h1276
                          · rcases p1258_3 (m.d 1 2) (by simp) with h1277 | h1277
                            · linarith only [h0, h1277, hlam]
                            · rcases p1258_3 (m.d 1 3) (by simp) with h1279 | h1279
                              · linarith only [h1, h1279, hlam]
                              · rcases p1258_3 (m.d 1 4) (by simp) with h1281 | h1281
                                · linarith only [h1281, hlam, p1258_0]
                                · rcases p1258_3 (m.d 1 5) (by simp) with h1283 | h1283
                                  · linarith only [h1283, h3, hlam]
                                  · rcases h3bigk with h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c | h1285c
                                    · have p1285_0 := h1285c.1
                                      have p1285_1 := h1285c.2.1
                                      have p1285_2 := h1285c.2.2.1
                                      have p1285_3 := h1285c.2.2.2
                                      linarith only [hlam, p1285_0]
                                    · have p1285_0 := h1285c.1
                                      have p1285_1 := h1285c.2.1
                                      have p1285_2 := h1285c.2.2.1
                                      have p1285_3 := h1285c.2.2.2
                                      linarith only [h1255, h1257, h4, hc34, hlam, hphi, p1285_1, u3ehi1]
                                    · have p1285_0 := h1285c.1
                                      have p1285_1 := h1285c.2.1
                                      have p1285_2 := h1285c.2.2.1
                                      have p1285_3 := h1285c.2.2.2
                                      linarith only [h4, hlam, p1285_1]
                                    · have p1285_0 := h1285c.1
                                      have p1285_1 := h1285c.2.1
                                      have p1285_2 := h1285c.2.2.1
                                      have p1285_3 := h1285c.2.2.2
                                      linarith only [h661, hlam, p1285_0]
                                    · have p1285_0 := h1285c.1
                                      have p1285_1 := h1285c.2.1
                                      have p1285_2 := h1285c.2.2.1
                                      have p1285_3 := h1285c.2.2.2
                                      linarith only [h1134, hlam, p1285_0]
                                    · have p1285_0 := h1285c.1
                                      have p1285_1 := h1285c.2.1
                                      have p1285_2 := h1285c.2.2.1
                                      have p1285_3 := h1285c.2.2.2
                                      linarith only [h1, hlam, p1285_0]
                                    · have p1285_0 := h1285c.1
                                      have p1285_1 := h1285c.2.1
                                      have p1285_2 := h1285c.2.2.1
                                      have p1285_3 := h1285c.2.2.2
                                      linarith only [hlam, p1285_0]
                                    · have p1285_0 := h1285c.1
                                      have p1285_1 := h1285c.2.1
                                      have p1285_2 := h1285c.2.2.1
                                      have p1285_3 := h1285c.2.2.2
                                      linarith only [h1136, hlam, p1285_1]
                                    · have p1285_0 := h1285c.1
                                      have p1285_1 := h1285c.2.1
                                      have p1285_2 := h1285c.2.2.1
                                      have p1285_3 := h1285c.2.2.2
                                      linarith only [h1152, hlam, p1285_0]
                                    · have p1285_0 := h1285c.1
                                      have p1285_1 := h1285c.2.1
                                      have p1285_2 := h1285c.2.2.1
                                      have p1285_3 := h1285c.2.2.2
                                      linarith only [h1154, hlam, p1285_0]
                                    · have p1285_0 := h1285c.1
                                      have p1285_1 := h1285c.2.1
                                      have p1285_2 := h1285c.2.2.1
                                      have p1285_3 := h1285c.2.2.2
                                      linarith only [h1255, h1257, hc34, hlam, hphi, p1285_1, u3ehi0]
                                    · have p1285_0 := h1285c.1
                                      have p1285_1 := h1285c.2.1
                                      have p1285_2 := h1285c.2.2.1
                                      have p1285_3 := h1285c.2.2.2
                                      linarith only [h1255, h1257, hc34, hlam, hphi, p1285_1, u3ehi1]
                                    · have p1285_0 := h1285c.1
                                      have p1285_1 := h1285c.2.1
                                      have p1285_2 := h1285c.2.2.1
                                      have p1285_3 := h1285c.2.2.2
                                      linarith only [hlam, p1285_0]
                                    · have p1285_0 := h1285c.1
                                      have p1285_1 := h1285c.2.1
                                      have p1285_2 := h1285c.2.2.1
                                      have p1285_3 := h1285c.2.2.2
                                      linarith only [h1157, hlam, p1285_0]
                                    · have p1285_0 := h1285c.1
                                      have p1285_1 := h1285c.2.1
                                      have p1285_2 := h1285c.2.2.1
                                      have p1285_3 := h1285c.2.2.2
                                      linarith only [h1255, hlam, p1285_0]
                                    · have p1285_0 := h1285c.1
                                      have p1285_1 := h1285c.2.1
                                      have p1285_2 := h1285c.2.2.1
                                      have p1285_3 := h1285c.2.2.2
                                      linarith only [h1, hc34, hlam, hphi, p1285_1, u3ehi1]
                                    · have p1285_0 := h1285c.1
                                      have p1285_1 := h1285c.2.1
                                      have p1285_2 := h1285c.2.2.1
                                      have p1285_3 := h1285c.2.2.2
                                      linarith only [hc34, hlam, hphi, p1285_1, u3ehi1]
                                    · have p1285_0 := h1285c.1
                                      have p1285_1 := h1285c.2.1
                                      have p1285_2 := h1285c.2.2.1
                                      have p1285_3 := h1285c.2.2.2
                                      linarith only [h4, hc02, hc34, hlam, hphi, ht23, p1285_1]
                                    · have p1285_0 := h1285c.1
                                      have p1285_1 := h1285c.2.1
                                      have p1285_2 := h1285c.2.2.1
                                      have p1285_3 := h1285c.2.2.2
                                      linarith only [hlam, p1285_0]
                                    · have p1285_0 := h1285c.1
                                      have p1285_1 := h1285c.2.1
                                      have p1285_2 := h1285c.2.2.1
                                      have p1285_3 := h1285c.2.2.2
                                      linarith only [hc34, hlam, hphi, p1285_1, u3ehi4]
                                    · have p1285_0 := h1285c.1
                                      have p1285_1 := h1285c.2.1
                                      have p1285_2 := h1285c.2.2.1
                                      have p1285_3 := h1285c.2.2.2
                                      linarith only [h1, hc35, hlam, hphi, p1285_1, u3ehi1]
                                    · have p1285_0 := h1285c.1
                                      have p1285_1 := h1285c.2.1
                                      have p1285_2 := h1285c.2.2.1
                                      have p1285_3 := h1285c.2.2.2
                                      linarith only [hc35, hlam, hphi, p1285_1, u3ehi1]
                                    · have p1285_0 := h1285c.1
                                      have p1285_1 := h1285c.2.1
                                      have p1285_2 := h1285c.2.2.1
                                      have p1285_3 := h1285c.2.2.2
                                      linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p1285_1]
                                    · have p1285_0 := h1285c.1
                                      have p1285_1 := h1285c.2.1
                                      have p1285_2 := h1285c.2.2.1
                                      have p1285_3 := h1285c.2.2.2
                                      linarith only [h1257, hlam, p1285_0]
                                    · have p1285_0 := h1285c.1
                                      have p1285_1 := h1285c.2.1
                                      have p1285_2 := h1285c.2.2.1
                                      have p1285_3 := h1285c.2.2.2
                                      linarith only [hlam, p1285_0]
                          · linarith only [h1276, hlam, p1258_0]
                        · have p1258_0 := h1258c.1
                          have p1258_1 := h1258c.2.1
                          have p1258_2 := h1258c.2.2.1
                          have p1258_3 := h1258c.2.2.2
                          rcases p1258_3 (m.d 0 1) (by simp) with h1312 | h1312
                          · rcases p1258_3 (m.d 1 2) (by simp) with h1313 | h1313
                            · linarith only [h0, h1313, hlam]
                            · rcases p1258_3 (m.d 1 3) (by simp) with h1315 | h1315
                              · linarith only [h1, h1315, hlam]
                              · rcases p1258_3 (m.d 1 4) (by simp) with h1317 | h1317
                                · linarith only [h1317, h2, hlam]
                                · linarith only [h1156, h1317, hlam]
                          · linarith only [h1312, hlam, p1258_0]
                        · have p1258_0 := h1258c.1
                          have p1258_1 := h1258c.2.1
                          have p1258_2 := h1258c.2.2.1
                          have p1258_3 := h1258c.2.2.2
                          linarith only [h0, hlam, p1258_0]
                        · have p1258_0 := h1258c.1
                          have p1258_1 := h1258c.2.1
                          have p1258_2 := h1258c.2.2.1
                          have p1258_3 := h1258c.2.2.2
                          linarith only [hlam, p1258_0]
                        · have p1258_0 := h1258c.1
                          have p1258_1 := h1258c.2.1
                          have p1258_2 := h1258c.2.2.1
                          have p1258_3 := h1258c.2.2.2
                          linarith only [h1136, hlam, p1258_0]
                        · have p1258_0 := h1258c.1
                          have p1258_1 := h1258c.2.1
                          have p1258_2 := h1258c.2.2.1
                          have p1258_3 := h1258c.2.2.2
                          linarith only [h1138, hlam, p1258_0]
                        · have p1258_0 := h1258c.1
                          have p1258_1 := h1258c.2.1
                          have p1258_2 := h1258c.2.2.1
                          have p1258_3 := h1258c.2.2.2
                          linarith only [h1146, hlam, p1258_0]
                        · have p1258_0 := h1258c.1
                          have p1258_1 := h1258c.2.1
                          have p1258_2 := h1258c.2.2.1
                          have p1258_3 := h1258c.2.2.2
                          linarith only [h1, hlam, p1258_0]
                        · have p1258_0 := h1258c.1
                          have p1258_1 := h1258c.2.1
                          have p1258_2 := h1258c.2.2.1
                          have p1258_3 := h1258c.2.2.2
                          linarith only [h1, h661, hc12, hc34, hlam, hphi, ht23, p1258_1]
                        · have p1258_0 := h1258c.1
                          have p1258_1 := h1258c.2.1
                          have p1258_2 := h1258c.2.2.1
                          have p1258_3 := h1258c.2.2.2
                          linarith only [hlam, p1258_0]
                        · have p1258_0 := h1258c.1
                          have p1258_1 := h1258c.2.1
                          have p1258_2 := h1258c.2.2.1
                          have p1258_3 := h1258c.2.2.2
                          linarith only [h1152, hlam, p1258_1]
                        · have p1258_0 := h1258c.1
                          have p1258_1 := h1258c.2.1
                          have p1258_2 := h1258c.2.2.1
                          have p1258_3 := h1258c.2.2.2
                          linarith only [h1154, hlam, p1258_1]
                        · have p1258_0 := h1258c.1
                          have p1258_1 := h1258c.2.1
                          have p1258_2 := h1258c.2.2.1
                          have p1258_3 := h1258c.2.2.2
                          linarith only [h2, hlam, p1258_0]
                        · have p1258_0 := h1258c.1
                          have p1258_1 := h1258c.2.1
                          have p1258_2 := h1258c.2.2.1
                          have p1258_3 := h1258c.2.2.2
                          rcases p1258_3 (m.d 0 1) (by simp) with h1332 | h1332
                          · rcases p1258_3 (m.d 1 2) (by simp) with h1333 | h1333
                            · linarith only [h1138, h1333, hlam]
                            · rcases p1258_3 (m.d 1 3) (by simp) with h1335 | h1335
                              · linarith only [h1152, h1335, hlam]
                              · linarith only [h1136, h1335, hlam]
                          · linarith only [h0, h1332, hlam]
                        · have p1258_0 := h1258c.1
                          have p1258_1 := h1258c.2.1
                          have p1258_2 := h1258c.2.2.1
                          have p1258_3 := h1258c.2.2.2
                          linarith only [h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1258_1, u3ehi1]
                        · have p1258_0 := h1258c.1
                          have p1258_1 := h1258c.2.1
                          have p1258_2 := h1258c.2.2.1
                          have p1258_3 := h1258c.2.2.2
                          linarith only [hlam, p1258_0]
                        · have p1258_0 := h1258c.1
                          have p1258_1 := h1258c.2.1
                          have p1258_2 := h1258c.2.2.1
                          have p1258_3 := h1258c.2.2.2
                          linarith only [h1154, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1258_1, u3ehi1]
                        · have p1258_0 := h1258c.1
                          have p1258_1 := h1258c.2.1
                          have p1258_2 := h1258c.2.2.1
                          have p1258_3 := h1258c.2.2.2
                          linarith only [h3, hlam, p1258_0]
                        · have p1258_0 := h1258c.1
                          have p1258_1 := h1258c.2.1
                          have p1258_2 := h1258c.2.2.1
                          have p1258_3 := h1258c.2.2.2
                          rcases p1258_3 (m.d 0 1) (by simp) with h1343 | h1343
                          · rcases p1258_3 (m.d 1 2) (by simp) with h1344 | h1344
                            · linarith only [h1146, h1344, hlam]
                            · rcases p1258_3 (m.d 1 3) (by simp) with h1346 | h1346
                              · linarith only [h1154, h1346, hlam]
                              · linarith only [h1136, h1346, hlam]
                          · linarith only [h0, h1343, hlam]
                        · have p1258_0 := h1258c.1
                          have p1258_1 := h1258c.2.1
                          have p1258_2 := h1258c.2.2.1
                          have p1258_3 := h1258c.2.2.2
                          linarith only [h1156, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1258_1, u3ehi1]
                        · have p1258_0 := h1258c.1
                          have p1258_1 := h1258c.2.1
                          have p1258_2 := h1258c.2.2.1
                          have p1258_3 := h1258c.2.2.2
                          linarith only [h1156, hlam, p1258_0]
                        · have p1258_0 := h1258c.1
                          have p1258_1 := h1258c.2.1
                          have p1258_2 := h1258c.2.2.1
                          have p1258_3 := h1258c.2.2.2
                          linarith only [hlam, p1258_0]
                      · linarith only [h1156, h1257, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1354 | h1354
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1355 | h1355
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1356 | h1356
                      · linarith only [h1138, h1156, h1354, h1356, hc12, hc23, hlam, hphi]
                      · linarith only [h1, h1356, h661, hc45, hlam, hphi, ht34, u3ehi1]
                    · linarith only [h1, h1354, h1355, h661, hc35, hlam, hphi, u3ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1360 | h1360
                    · linarith only [h1354, h1360, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1362 | h1362
                      · linarith only [h1152, h1156, h1362, hc34, hlam, hphi, u3ehi1]
                      · linarith only [h1354, h1362, hc45, hlam, hphi, ht34, u3ehi2]

set_option maxHeartbeats 6958000 in
set_option maxHeartbeats 6958000 in
theorem r1l7_11_23_L_I_M_IR_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_11_23_L_I_M_IR_x0_x0_x0_x0_x0 m hb1 hb3 h0 h1 h2 h3 h4
  · exact r1l7_11_23_L_I_M_IR_x0_x0_x0_x0_x1 m hb1 hb3 h0 h1 h2 h3 h4

set_option maxHeartbeats 6958000 in
set_option maxHeartbeats 6958000 in
theorem r1l7_11_23_L_I_M_IR_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1365 | h1365
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1366 | h1366
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1367 | h1367
      · linarith only [h0, h1365, h1367, h3, hlam]
      · linarith only [h1366, h1367, hc35, hlam, hphi, u3ehi3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1370 | h1370
      · linarith only [h1366, h1370, hc34, hlam, hphi, u3ehi4]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1372 | h1372
        · linarith only [h0, h1372, h3, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1374 | h1374
          · linarith only [h0, h1365, h1372, h1374, h3, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1376 | h1376
            · linarith only [h0, h1365, h1372, h1376, h3, hc15, hc25, hlam, hphi, ht01, ht0b, ht5b]
            · linarith only [h0, h1365, h1372, h1376, h3, hc12, hc25, hlam, hphi]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1379 | h1379
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1380 | h1380
      · linarith only [h1, h1380, h3, hlam]
      · linarith only [h1379, h1380, hc35, hlam, hphi, u3ehi3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1383 | h1383
      · linarith only [h1379, h1383, hc34, hlam, hphi, u3ehi4]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1385 | h1385
        · linarith only [h0, h1365, h1385, h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1387 | h1387
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1388 | h1388
            · linarith only [h0, h1388, h3, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1390 | h1390
              · linarith only [h1, h1365, h1379, h1388, h1390, h3, hc02, hc25, hlam, hphi]
              · linarith only [h1385, h1387, h1390, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1393 | h1393
            · linarith only [h0, h1393, h3, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1395 | h1395
              · linarith only [h1, h1379, h1395, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1397 | h1397
                · linarith only [h1383, h1395, h1397, h2, h3, hlam]
                · linarith only [h1395, h1397, h2, h3, hc35, hlam, hphi, u3ehi1]

set_option maxHeartbeats 6958000 in
set_option maxHeartbeats 6958000 in
theorem r1l7_11_23_L_I_M_IR_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_11_23_L_I_M_IR_x0_x0_x0_x0 m hb1 hb3 h0 h1 h2 h3
  · exact r1l7_11_23_L_I_M_IR_x0_x0_x0_x1 m hb1 hb3 h0 h1 h2 h3

set_option maxHeartbeats 6958000 in
set_option maxHeartbeats 6958000 in
theorem r1l7_11_23_L_I_M_IR_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1400 | h1400
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1401 | h1401
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1402 | h1402
      · linarith only [h0, h1401, h1402, h2, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1404 | h1404
        · linarith only [h1402, h1404, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1406 | h1406
          · linarith only [h0, h1406, h2, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1408 | h1408
            · linarith only [h0, h1401, h1406, h1408, h2, hc14, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · linarith only [h0, h1401, h1406, h1408, h2, hc12, hc24, hlam, hphi]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1411 | h1411
      · linarith only [h1, h1411, h2, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1413 | h1413
        · linarith only [h1411, h1413, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1415 | h1415
          · linarith only [h0, h1401, h1415, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1417 | h1417
            · linarith only [h0, h1417, h2, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1419 | h1419
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1420 | h1420
                · linarith only [h1, h1411, h1417, h1420, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                · linarith only [h1, h1420, h2, hc34, hlam, hphi, u3ehi1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1423 | h1423
                · linarith only [h1, h1417, h1423, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h1, h1423, h2, hc34, hlam, hphi, u3ehi1]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1426 | h1426
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1427 | h1427
      · linarith only [h0, h1426, h1427, h2, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1429 | h1429
        · linarith only [h1427, h1429, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1431 | h1431
          · linarith only [h0, h1431, h2, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1433 | h1433
            · linarith only [h0, h1426, h1431, h1433, h2, hc14, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · linarith only [h0, h1426, h1431, h1433, h2, hc12, hc24, hlam, hphi]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1436 | h1436
      · linarith only [h1, h1436, h2, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1438 | h1438
        · linarith only [h1436, h1438, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1440 | h1440
          · linarith only [h0, h1440, h2, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1442 | h1442
            · linarith only [h1, h1440, h1442, h2, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1444 | h1444
              · linarith only [h1, h1400, h1440, h1444, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1446 | h1446
                · linarith only [h1, h1426, h1436, h1442, h1446, h2, hc02, hc24, hlam, hphi]
                · linarith only [h1, h1446, h2, hc34, hlam, hphi, u3ehi1]

set_option maxHeartbeats 6958000 in
set_option maxHeartbeats 6958000 in
theorem r1l7_11_23_L_I_M_IR_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_11_23_L_I_M_IR_x0_x0_x0 m hb1 hb3 h0 h1 h2
  · exact r1l7_11_23_L_I_M_IR_x0_x0_x1 m hb1 hb3 h0 h1 h2

end R2N4
