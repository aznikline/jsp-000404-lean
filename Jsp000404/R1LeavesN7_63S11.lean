import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_63S10

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_11_14_M_LR_L_0_L_I_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h653 | h653
  · rcases m.htr 0 3 4 (by decide) (by decide) with h654 | h654
    · linarith only [h3, h4, h654, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h656 | h656
      · rcases m.htr 1 2 4 (by decide) (by decide) with h657 | h657
        · linarith only [h4, h653, h657, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h659 | h659
          · rcases m.htr 1 3 4 (by decide) (by decide) with h660 | h660
            · linarith only [h654, h660, hlam, hphi, ht01, u0ehi7, u1elo2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h662 | h662
              · rcases m.htr 1 4 5 (by decide) (by decide) with h663 | h663
                · rcases m.htr 2 3 4 (by decide) (by decide) with h664 | h664
                  · linarith only [h654, h664, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h666 | h666
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h667 | h667
                      · rcases h4bigk with h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [hlam, p668_0]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [h660, h662, hc35, hlam, hphi, ht0b, ht5b, p668_1, u0elo3]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [h4, hlam, p668_0]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [h654, hlam, p668_0]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          rcases p668_3 (m.d 0 4) (by simp) with h673 | h673
                          · rcases p668_3 (m.d 1 4) (by simp) with h674 | h674
                            · linarith only [h2, h674, hlam]
                            · linarith only [h663, h674, hlam]
                          · linarith only [h673, hlam, p668_0]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [h2, hlam, p668_1]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [hlam, p668_0]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [h657, hlam, p668_0]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [h660, hlam, p668_1]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p668_1, u1elo0]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [hc24, hlam, hphi, ht01, ht12, p668_1, u0ehi8]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          rcases p668_3 (m.d 0 4) (by simp) with h684 | h684
                          · linarith only [h4, h684, hlam]
                          · linarith only [h2, h684, hlam]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [hlam, p668_0]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [h664, hlam, p668_1]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          rcases p668_3 (m.d 0 4) (by simp) with h689 | h689
                          · linarith only [h4, h689, hlam]
                          · linarith only [h656, h689, hlam]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [h4, h653, hc34, hlam, hphi, ht01, ht12, ht23, p668_1, u0ehi9]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          rcases p668_3 (m.d 0 4) (by simp) with h693 | h693
                          · linarith only [h654, h693, hlam]
                          · linarith only [h2, h693, hlam]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [h4, h653, hc34, hlam, hphi, ht01, ht12, ht23, p668_1, u0ehi9]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [hlam, p668_0]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          rcases p668_3 (m.d 0 4) (by simp) with h698 | h698
                          · linarith only [h654, h698, hlam]
                          · linarith only [h656, h698, hlam]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [h656, hlam, p668_0]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [h663, hlam, p668_0]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [h666, hlam, p668_0]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [h667, hlam, p668_0]
                        · have p668_0 := h668c.1
                          have p668_1 := h668c.2.1
                          have p668_2 := h668c.2.2.1
                          have p668_3 := h668c.2.2.2
                          linarith only [hlam, p668_0]
                      · linarith only [h4, h653, h659, h664, h666, h667, hlam, hphi, ht01, u0ehi9, u1elo1]
                    · linarith only [h2, h4, h653, h663, h666, hlam, hphi, ht01, u0ehi9, u1elo0]
                · linarith only [h656, h657, h659, h663, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h709 | h709
                · rcases m.htr 2 3 4 (by decide) (by decide) with h710 | h710
                  · linarith only [h3, h654, h710, hlam, hphi, u0ehi7, u0elo1]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h712 | h712
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h713 | h713
                      · rcases h4bigk with h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [hlam, p714_0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h2, h657, h659, h712, hc45, hlam, hphi, ht01, ht0b, ht5b, p714_1, u1elo0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h4, hlam, p714_0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h654, hlam, p714_0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          rcases p714_3 (m.d 0 4) (by simp) with h719 | h719
                          · rcases p714_3 (m.d 1 4) (by simp) with h720 | h720
                            · linarith only [h2, h720, hlam]
                            · linarith only [h709, h720, hlam]
                          · linarith only [h719, hlam, p714_0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h2, hlam, p714_1]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [hlam, p714_0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h657, hlam, p714_0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h660, hlam, p714_1]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p714_1, u1elo0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h710, hc34, hlam, hphi, ht01, ht12, ht23, p714_1, u0ehi8]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          rcases p714_3 (m.d 0 4) (by simp) with h730 | h730
                          · linarith only [h4, h730, hlam]
                          · linarith only [h2, h730, hlam]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [hlam, p714_0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h710, hlam, p714_1]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          rcases p714_3 (m.d 0 4) (by simp) with h735 | h735
                          · linarith only [h4, h735, hlam]
                          · linarith only [h656, h735, hlam]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h3, h4, hc23, hc34, hlam, hphi, p714_1]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          rcases p714_3 (m.d 0 4) (by simp) with h739 | h739
                          · linarith only [h654, h739, hlam]
                          · linarith only [h2, h739, hlam]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h3, h4, hc34, hlam, hphi, ht01, ht12, ht23, p714_1, u0ehi7]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [hlam, p714_0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          rcases p714_3 (m.d 0 4) (by simp) with h744 | h744
                          · linarith only [h654, h744, hlam]
                          · linarith only [h656, h744, hlam]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h656, hlam, p714_0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h709, hlam, p714_0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h712, hlam, p714_0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h713, hlam, p714_0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [hlam, p714_0]
                      · linarith only [h2, h657, h659, h712, h713, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · linarith only [h3, h4, h712, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                · linarith only [h656, h657, h659, h709, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
          · linarith only [h4, h653, h659, hc12, hc24, hlam, hphi]
      · linarith only [h4, h653, h656, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h757 | h757
    · linarith only [h3, h4, h757, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h759 | h759
      · rcases m.htr 1 2 4 (by decide) (by decide) with h760 | h760
        · linarith only [h3, h4, h760, hlam, hphi, ht01, u0ehi7, u1elo1]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h762 | h762
          · linarith only [h3, h653, h762, hlam, hphi, ht01, u0ehi7, u1elo1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h764 | h764
            · linarith only [h757, h764, hlam, hphi, ht01, u0ehi7, u1elo2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h766 | h766
              · rcases m.htr 1 4 5 (by decide) (by decide) with h767 | h767
                · rcases m.htr 2 3 4 (by decide) (by decide) with h768 | h768
                  · linarith only [h757, h768, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h770 | h770
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h771 | h771
                      · rcases h4bigk with h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c
                        · have p772_0 := h772c.1
                          have p772_1 := h772c.2.1
                          have p772_2 := h772c.2.2.1
                          have p772_3 := h772c.2.2.2
                          linarith only [hlam, p772_0]
                        · have p772_0 := h772c.1
                          have p772_1 := h772c.2.1
                          have p772_2 := h772c.2.2.1
                          have p772_3 := h772c.2.2.2
                          linarith only [h764, h766, hc35, hlam, hphi, ht0b, ht5b, p772_1, u0elo3]
                        · have p772_0 := h772c.1
                          have p772_1 := h772c.2.1
                          have p772_2 := h772c.2.2.1
                          have p772_3 := h772c.2.2.2
                          linarith only [h4, hlam, p772_0]
                        · have p772_0 := h772c.1
                          have p772_1 := h772c.2.1
                          have p772_2 := h772c.2.2.1
                          have p772_3 := h772c.2.2.2
                          linarith only [h757, hlam, p772_0]
                        · have p772_0 := h772c.1
                          have p772_1 := h772c.2.1
                          have p772_2 := h772c.2.2.1
                          have p772_3 := h772c.2.2.2
                          rcases p772_3 (m.d 0 4) (by simp) with h777 | h777
                          · rcases p772_3 (m.d 1 4) (by simp) with h778 | h778
                            · linarith only [h2, h778, hlam]
                            · linarith only [h767, h778, hlam]
                          · linarith only [h777, hlam, p772_0]
                        · have p772_0 := h772c.1
                          have p772_1 := h772c.2.1
                          have p772_2 := h772c.2.2.1
                          have p772_3 := h772c.2.2.2
                          linarith only [h2, hlam, p772_1]
                        · have p772_0 := h772c.1
                          have p772_1 := h772c.2.1
                          have p772_2 := h772c.2.2.1
                          have p772_3 := h772c.2.2.2
                          linarith only [hlam, p772_0]
                        · have p772_0 := h772c.1
                          have p772_1 := h772c.2.1
                          have p772_2 := h772c.2.2.1
                          have p772_3 := h772c.2.2.2
                          linarith only [h760, hlam, p772_0]
                        · have p772_0 := h772c.1
                          have p772_1 := h772c.2.1
                          have p772_2 := h772c.2.2.1
                          have p772_3 := h772c.2.2.2
                          linarith only [h764, hlam, p772_1]
                        · have p772_0 := h772c.1
                          have p772_1 := h772c.2.1
                          have p772_2 := h772c.2.2.1
                          have p772_3 := h772c.2.2.2
                          linarith only [h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p772_1, u1elo0]
                        · have p772_0 := h772c.1
                          have p772_1 := h772c.2.1
                          have p772_2 := h772c.2.2.1
                          have p772_3 := h772c.2.2.2
                          linarith only [h768, hc34, hlam, hphi, ht01, ht12, ht23, p772_1, u0ehi8]
                        · have p772_0 := h772c.1
                          have p772_1 := h772c.2.1
                          have p772_2 := h772c.2.2.1
                          have p772_3 := h772c.2.2.2
                          rcases p772_3 (m.d 0 4) (by simp) with h788 | h788
                          · linarith only [h4, h788, hlam]
                          · linarith only [h2, h788, hlam]
                        · have p772_0 := h772c.1
                          have p772_1 := h772c.2.1
                          have p772_2 := h772c.2.2.1
                          have p772_3 := h772c.2.2.2
                          linarith only [hlam, p772_0]
                        · have p772_0 := h772c.1
                          have p772_1 := h772c.2.1
                          have p772_2 := h772c.2.2.1
                          have p772_3 := h772c.2.2.2
                          linarith only [h768, hlam, p772_1]
                        · have p772_0 := h772c.1
                          have p772_1 := h772c.2.1
                          have p772_2 := h772c.2.2.1
                          have p772_3 := h772c.2.2.2
                          rcases p772_3 (m.d 0 4) (by simp) with h793 | h793
                          · linarith only [h4, h793, hlam]
                          · linarith only [h759, h793, hlam]
                        · have p772_0 := h772c.1
                          have p772_1 := h772c.2.1
                          have p772_2 := h772c.2.2.1
                          have p772_3 := h772c.2.2.2
                          linarith only [h3, h653, h759, hc34, hlam, hphi, ht01, ht12, ht23, p772_1, u0ehi7]
                        · have p772_0 := h772c.1
                          have p772_1 := h772c.2.1
                          have p772_2 := h772c.2.2.1
                          have p772_3 := h772c.2.2.2
                          rcases p772_3 (m.d 0 4) (by simp) with h797 | h797
                          · linarith only [h757, h797, hlam]
                          · linarith only [h2, h797, hlam]
                        · have p772_0 := h772c.1
                          have p772_1 := h772c.2.1
                          have p772_2 := h772c.2.2.1
                          have p772_3 := h772c.2.2.2
                          linarith only [h3, h653, h770, hc34, hlam, hphi, ht01, ht12, ht23, p772_1, u0ehi7]
                        · have p772_0 := h772c.1
                          have p772_1 := h772c.2.1
                          have p772_2 := h772c.2.2.1
                          have p772_3 := h772c.2.2.2
                          linarith only [hlam, p772_0]
                        · have p772_0 := h772c.1
                          have p772_1 := h772c.2.1
                          have p772_2 := h772c.2.2.1
                          have p772_3 := h772c.2.2.2
                          rcases p772_3 (m.d 0 4) (by simp) with h802 | h802
                          · linarith only [h757, h802, hlam]
                          · linarith only [h759, h802, hlam]
                        · have p772_0 := h772c.1
                          have p772_1 := h772c.2.1
                          have p772_2 := h772c.2.2.1
                          have p772_3 := h772c.2.2.2
                          linarith only [h759, hlam, p772_0]
                        · have p772_0 := h772c.1
                          have p772_1 := h772c.2.1
                          have p772_2 := h772c.2.2.1
                          have p772_3 := h772c.2.2.2
                          linarith only [h767, hlam, p772_0]
                        · have p772_0 := h772c.1
                          have p772_1 := h772c.2.1
                          have p772_2 := h772c.2.2.1
                          have p772_3 := h772c.2.2.2
                          linarith only [h770, hlam, p772_0]
                        · have p772_0 := h772c.1
                          have p772_1 := h772c.2.1
                          have p772_2 := h772c.2.2.1
                          have p772_3 := h772c.2.2.2
                          linarith only [h771, hlam, p772_0]
                        · have p772_0 := h772c.1
                          have p772_1 := h772c.2.1
                          have p772_2 := h772c.2.2.1
                          have p772_3 := h772c.2.2.2
                          linarith only [hlam, p772_0]
                      · linarith only [h3, h653, h768, h770, h771, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                    · linarith only [h2, h767, h770, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h759, h764, h766, h767, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h813 | h813
                · rcases m.htr 2 3 4 (by decide) (by decide) with h814 | h814
                  · linarith only [h3, h757, h814, hlam, hphi, u0ehi7, u0elo1]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h816 | h816
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h817 | h817
                      · rcases h4bigk with h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c
                        · have p818_0 := h818c.1
                          have p818_1 := h818c.2.1
                          have p818_2 := h818c.2.2.1
                          have p818_3 := h818c.2.2.2
                          linarith only [hlam, p818_0]
                        · have p818_0 := h818c.1
                          have p818_1 := h818c.2.1
                          have p818_2 := h818c.2.2.1
                          have p818_3 := h818c.2.2.2
                          linarith only [h2, h813, hc45, hlam, hphi, ht01, ht0b, ht5b, p818_1, u1elo0]
                        · have p818_0 := h818c.1
                          have p818_1 := h818c.2.1
                          have p818_2 := h818c.2.2.1
                          have p818_3 := h818c.2.2.2
                          linarith only [h4, hlam, p818_0]
                        · have p818_0 := h818c.1
                          have p818_1 := h818c.2.1
                          have p818_2 := h818c.2.2.1
                          have p818_3 := h818c.2.2.2
                          linarith only [h757, hlam, p818_0]
                        · have p818_0 := h818c.1
                          have p818_1 := h818c.2.1
                          have p818_2 := h818c.2.2.1
                          have p818_3 := h818c.2.2.2
                          rcases p818_3 (m.d 0 4) (by simp) with h823 | h823
                          · rcases p818_3 (m.d 1 4) (by simp) with h824 | h824
                            · linarith only [h2, h824, hlam]
                            · linarith only [h813, h824, hlam]
                          · linarith only [h823, hlam, p818_0]
                        · have p818_0 := h818c.1
                          have p818_1 := h818c.2.1
                          have p818_2 := h818c.2.2.1
                          have p818_3 := h818c.2.2.2
                          linarith only [h2, hlam, p818_1]
                        · have p818_0 := h818c.1
                          have p818_1 := h818c.2.1
                          have p818_2 := h818c.2.2.1
                          have p818_3 := h818c.2.2.2
                          linarith only [hlam, p818_0]
                        · have p818_0 := h818c.1
                          have p818_1 := h818c.2.1
                          have p818_2 := h818c.2.2.1
                          have p818_3 := h818c.2.2.2
                          linarith only [h760, hlam, p818_0]
                        · have p818_0 := h818c.1
                          have p818_1 := h818c.2.1
                          have p818_2 := h818c.2.2.1
                          have p818_3 := h818c.2.2.2
                          linarith only [h764, hlam, p818_1]
                        · have p818_0 := h818c.1
                          have p818_1 := h818c.2.1
                          have p818_2 := h818c.2.2.1
                          have p818_3 := h818c.2.2.2
                          linarith only [h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p818_1, u1elo0]
                        · have p818_0 := h818c.1
                          have p818_1 := h818c.2.1
                          have p818_2 := h818c.2.2.1
                          have p818_3 := h818c.2.2.2
                          linarith only [h814, hc34, hlam, hphi, ht01, ht12, ht23, p818_1, u0ehi8]
                        · have p818_0 := h818c.1
                          have p818_1 := h818c.2.1
                          have p818_2 := h818c.2.2.1
                          have p818_3 := h818c.2.2.2
                          rcases p818_3 (m.d 0 4) (by simp) with h834 | h834
                          · linarith only [h4, h834, hlam]
                          · linarith only [h2, h834, hlam]
                        · have p818_0 := h818c.1
                          have p818_1 := h818c.2.1
                          have p818_2 := h818c.2.2.1
                          have p818_3 := h818c.2.2.2
                          linarith only [hlam, p818_0]
                        · have p818_0 := h818c.1
                          have p818_1 := h818c.2.1
                          have p818_2 := h818c.2.2.1
                          have p818_3 := h818c.2.2.2
                          linarith only [h814, hlam, p818_1]
                        · have p818_0 := h818c.1
                          have p818_1 := h818c.2.1
                          have p818_2 := h818c.2.2.1
                          have p818_3 := h818c.2.2.2
                          rcases p818_3 (m.d 0 4) (by simp) with h839 | h839
                          · linarith only [h4, h839, hlam]
                          · linarith only [h759, h839, hlam]
                        · have p818_0 := h818c.1
                          have p818_1 := h818c.2.1
                          have p818_2 := h818c.2.2.1
                          have p818_3 := h818c.2.2.2
                          linarith only [h3, h653, h759, hc23, hc34, hlam, hphi, p818_1]
                        · have p818_0 := h818c.1
                          have p818_1 := h818c.2.1
                          have p818_2 := h818c.2.2.1
                          have p818_3 := h818c.2.2.2
                          rcases p818_3 (m.d 0 4) (by simp) with h843 | h843
                          · linarith only [h757, h843, hlam]
                          · linarith only [h2, h843, hlam]
                        · have p818_0 := h818c.1
                          have p818_1 := h818c.2.1
                          have p818_2 := h818c.2.2.1
                          have p818_3 := h818c.2.2.2
                          linarith only [h3, h4, hc34, hlam, hphi, ht01, ht12, ht23, p818_1, u0ehi7]
                        · have p818_0 := h818c.1
                          have p818_1 := h818c.2.1
                          have p818_2 := h818c.2.2.1
                          have p818_3 := h818c.2.2.2
                          linarith only [hlam, p818_0]
                        · have p818_0 := h818c.1
                          have p818_1 := h818c.2.1
                          have p818_2 := h818c.2.2.1
                          have p818_3 := h818c.2.2.2
                          rcases p818_3 (m.d 0 4) (by simp) with h848 | h848
                          · linarith only [h757, h848, hlam]
                          · linarith only [h759, h848, hlam]
                        · have p818_0 := h818c.1
                          have p818_1 := h818c.2.1
                          have p818_2 := h818c.2.2.1
                          have p818_3 := h818c.2.2.2
                          linarith only [h759, hlam, p818_0]
                        · have p818_0 := h818c.1
                          have p818_1 := h818c.2.1
                          have p818_2 := h818c.2.2.1
                          have p818_3 := h818c.2.2.2
                          linarith only [h813, hlam, p818_0]
                        · have p818_0 := h818c.1
                          have p818_1 := h818c.2.1
                          have p818_2 := h818c.2.2.1
                          have p818_3 := h818c.2.2.2
                          linarith only [h816, hlam, p818_0]
                        · have p818_0 := h818c.1
                          have p818_1 := h818c.2.1
                          have p818_2 := h818c.2.2.1
                          have p818_3 := h818c.2.2.2
                          linarith only [h817, hlam, p818_0]
                        · have p818_0 := h818c.1
                          have p818_1 := h818c.2.1
                          have p818_2 := h818c.2.2.1
                          have p818_3 := h818c.2.2.2
                          linarith only [hlam, p818_0]
                      · linarith only [h3, h653, h813, h814, h816, h817, hlam, hphi, ht01, u0ehi7, u1elo3]
                    · linarith only [h2, h813, h816, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h858 | h858
                  · linarith only [h2, h757, h759, h760, h813, h858, hc12, hc23, hlam, hphi, ht01, u0ehi7, u1elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h860 | h860
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h861 | h861
                      · rcases h4bigk with h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c
                        · have p862_0 := h862c.1
                          have p862_1 := h862c.2.1
                          have p862_2 := h862c.2.2.1
                          have p862_3 := h862c.2.2.2
                          linarith only [hlam, p862_0]
                        · have p862_0 := h862c.1
                          have p862_1 := h862c.2.1
                          have p862_2 := h862c.2.2.1
                          have p862_3 := h862c.2.2.2
                          rcases p862_3 (m.d 0 4) (by simp) with h864 | h864
                          · rcases p862_3 (m.d 1 4) (by simp) with h865 | h865
                            · linarith only [h2, h865, hlam]
                            · rcases p862_3 (m.d 2 4) (by simp) with h867 | h867
                              · rcases p862_3 (m.d 3 4) (by simp) with h868 | h868
                                · rcases p862_3 (m.d 4 5) (by simp) with h869 | h869
                                  · linarith only [h759, h869, hlam]
                                  · linarith only [h813, h869, hlam]
                                · linarith only [h764, h868, hlam]
                              · linarith only [h760, h867, hlam]
                          · linarith only [h2, h864, hlam]
                        · have p862_0 := h862c.1
                          have p862_1 := h862c.2.1
                          have p862_2 := h862c.2.2.1
                          have p862_3 := h862c.2.2.2
                          linarith only [h4, hlam, p862_0]
                        · have p862_0 := h862c.1
                          have p862_1 := h862c.2.1
                          have p862_2 := h862c.2.2.1
                          have p862_3 := h862c.2.2.2
                          linarith only [h757, hlam, p862_0]
                        · have p862_0 := h862c.1
                          have p862_1 := h862c.2.1
                          have p862_2 := h862c.2.2.1
                          have p862_3 := h862c.2.2.2
                          linarith only [h2, h760, h813, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p862_1, u1elo0]
                        · have p862_0 := h862c.1
                          have p862_1 := h862c.2.1
                          have p862_2 := h862c.2.2.1
                          have p862_3 := h862c.2.2.2
                          linarith only [h2, hlam, p862_1]
                        · have p862_0 := h862c.1
                          have p862_1 := h862c.2.1
                          have p862_2 := h862c.2.2.1
                          have p862_3 := h862c.2.2.2
                          linarith only [hlam, p862_0]
                        · have p862_0 := h862c.1
                          have p862_1 := h862c.2.1
                          have p862_2 := h862c.2.2.1
                          have p862_3 := h862c.2.2.2
                          linarith only [h760, hlam, p862_0]
                        · have p862_0 := h862c.1
                          have p862_1 := h862c.2.1
                          have p862_2 := h862c.2.2.1
                          have p862_3 := h862c.2.2.2
                          linarith only [h764, hlam, p862_1]
                        · have p862_0 := h862c.1
                          have p862_1 := h862c.2.1
                          have p862_2 := h862c.2.2.1
                          have p862_3 := h862c.2.2.2
                          linarith only [h813, hlam, p862_0]
                        · have p862_0 := h862c.1
                          have p862_1 := h862c.2.1
                          have p862_2 := h862c.2.2.1
                          have p862_3 := h862c.2.2.2
                          linarith only [h858, hc34, hlam, hphi, ht01, ht12, ht23, p862_1, u0ehi8]
                        · have p862_0 := h862c.1
                          have p862_1 := h862c.2.1
                          have p862_2 := h862c.2.2.1
                          have p862_3 := h862c.2.2.2
                          rcases p862_3 (m.d 0 4) (by simp) with h884 | h884
                          · linarith only [h4, h884, hlam]
                          · linarith only [h2, h884, hlam]
                        · have p862_0 := h862c.1
                          have p862_1 := h862c.2.1
                          have p862_2 := h862c.2.2.1
                          have p862_3 := h862c.2.2.2
                          linarith only [hlam, p862_0]
                        · have p862_0 := h862c.1
                          have p862_1 := h862c.2.1
                          have p862_2 := h862c.2.2.1
                          have p862_3 := h862c.2.2.2
                          linarith only [h858, hlam, p862_1]
                        · have p862_0 := h862c.1
                          have p862_1 := h862c.2.1
                          have p862_2 := h862c.2.2.1
                          have p862_3 := h862c.2.2.2
                          linarith only [h760, h813, h858, hc12, hc34, hlam, hphi, ht23, p862_1]
                        · have p862_0 := h862c.1
                          have p862_1 := h862c.2.1
                          have p862_2 := h862c.2.2.1
                          have p862_3 := h862c.2.2.2
                          linarith only [h759, h760, h813, hc12, hc34, hlam, hphi, ht23, p862_1]
                        · have p862_0 := h862c.1
                          have p862_1 := h862c.2.1
                          have p862_2 := h862c.2.2.1
                          have p862_3 := h862c.2.2.2
                          rcases p862_3 (m.d 0 4) (by simp) with h891 | h891
                          · linarith only [h757, h891, hlam]
                          · linarith only [h2, h891, hlam]
                        · have p862_0 := h862c.1
                          have p862_1 := h862c.2.1
                          have p862_2 := h862c.2.2.1
                          have p862_3 := h862c.2.2.2
                          linarith only [h653, h860, hc02, hc34, hlam, hphi, ht23, p862_1]
                        · have p862_0 := h862c.1
                          have p862_1 := h862c.2.1
                          have p862_2 := h862c.2.2.1
                          have p862_3 := h862c.2.2.2
                          linarith only [hlam, p862_0]
                        · have p862_0 := h862c.1
                          have p862_1 := h862c.2.1
                          have p862_2 := h862c.2.2.1
                          have p862_3 := h862c.2.2.2
                          linarith only [h760, h813, hc12, hc34, hlam, hphi, ht23, p862_1]
                        · have p862_0 := h862c.1
                          have p862_1 := h862c.2.1
                          have p862_2 := h862c.2.2.1
                          have p862_3 := h862c.2.2.2
                          linarith only [h759, hlam, p862_0]
                        · have p862_0 := h862c.1
                          have p862_1 := h862c.2.1
                          have p862_2 := h862c.2.2.1
                          have p862_3 := h862c.2.2.2
                          linarith only [h2, h759, h760, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p862_1, u1elo0]
                        · have p862_0 := h862c.1
                          have p862_1 := h862c.2.1
                          have p862_2 := h862c.2.2.1
                          have p862_3 := h862c.2.2.2
                          linarith only [h860, hlam, p862_0]
                        · have p862_0 := h862c.1
                          have p862_1 := h862c.2.1
                          have p862_2 := h862c.2.2.1
                          have p862_3 := h862c.2.2.2
                          linarith only [h861, hlam, p862_0]
                        · have p862_0 := h862c.1
                          have p862_1 := h862c.2.1
                          have p862_2 := h862c.2.2.1
                          have p862_3 := h862c.2.2.2
                          linarith only [hlam, p862_0]
                      · linarith only [h2, h3, h653, h759, h858, h860, h861, hlam, hphi, ht01, u0ehi7, u1elo0]
                    · linarith only [h2, h3, h4, h759, h860, hlam, hphi, ht01, u0ehi7, u1elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h904 | h904
        · linarith only [h3, h4, h904, hlam, hphi, ht01, u0ehi7, u1elo1]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h906 | h906
          · linarith only [h2, h3, h653, h904, h906, hlam, hphi, ht01, u0ehi7, u1elo0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h908 | h908
            · linarith only [h757, h908, hlam, hphi, ht01, u0ehi7, u1elo2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h910 | h910
              · rcases m.htr 1 4 5 (by decide) (by decide) with h911 | h911
                · linarith only [h2, h3, h4, h759, h911, hlam, hphi, ht01, u0ehi7, u1elo0]
                · linarith only [h908, h910, h911, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h914 | h914
                · linarith only [h2, h3, h4, h759, h914, hlam, hphi, ht01, u0ehi7, u1elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h916 | h916
                  · linarith only [h757, h916, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h918 | h918
                    · linarith only [h3, h4, h759, h918, hc24, hlam, hphi, ht01, ht12, u0ehi7]
                    · linarith only [h3, h4, h918, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]

theorem r1l7_20_11_14_M_LR_L_0_L_I_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
  · exact r1l7_20_11_14_M_LR_L_0_L_I_x0_x0_x0_x0_x0 m hb0 hb1 hb4 h0 h1 h2 h3 h4
  · exact r1l7_20_11_14_M_LR_L_0_L_I_x0_x0_x0_x0_x1 m hb0 hb1 hb4 h0 h1 h2 h3 h4

theorem r1l7_20_11_14_M_LR_L_0_L_I_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h921 | h921
  · rcases m.htr 0 2 5 (by decide) (by decide) with h922 | h922
    · rcases m.htr 0 3 4 (by decide) (by decide) with h923 | h923
      · rcases m.htr 0 4 5 (by decide) (by decide) with h924 | h924
        · rcases m.htr 1 2 4 (by decide) (by decide) with h925 | h925
          · rcases m.htr 1 2 5 (by decide) (by decide) with h926 | h926
            · rcases m.htr 1 3 4 (by decide) (by decide) with h927 | h927
              · rcases m.htr 1 3 5 (by decide) (by decide) with h928 | h928
                · rcases m.htr 1 4 5 (by decide) (by decide) with h929 | h929
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h930 | h930
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h931 | h931
                      · linarith only [h0, h925, h931, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · linarith only [h0, h925, h929, h930, h931, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · linarith only [h3, h921, h924, h930, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h935 | h935
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h936 | h936
                      · linarith only [h925, h929, h936, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h938 | h938
                        · linarith only [h925, h929, h935, h938, hlam]
                        · rcases h4bigk with h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c | h940c
                          · have p940_0 := h940c.1
                            have p940_1 := h940c.2.1
                            have p940_2 := h940c.2.2.1
                            have p940_3 := h940c.2.2.2
                            linarith only [hlam, p940_0]
                          · have p940_0 := h940c.1
                            have p940_1 := h940c.2.1
                            have p940_2 := h940c.2.2.1
                            have p940_3 := h940c.2.2.2
                            rcases p940_3 (m.d 0 4) (by simp) with h942 | h942
                            · rcases p940_3 (m.d 1 4) (by simp) with h943 | h943
                              · linarith only [h2, h943, hlam]
                              · rcases p940_3 (m.d 2 4) (by simp) with h945 | h945
                                · linarith only [h921, h945, hlam]
                                · rcases p940_3 (m.d 3 4) (by simp) with h947 | h947
                                  · linarith only [h923, h947, hlam]
                                  · rcases p940_3 (m.d 4 5) (by simp) with h949 | h949
                                    · linarith only [h924, h949, hlam]
                                    · linarith only [h929, h949, hlam]
                            · linarith only [h2, h942, hlam]
                          · have p940_0 := h940c.1
                            have p940_1 := h940c.2.1
                            have p940_2 := h940c.2.2.1
                            have p940_3 := h940c.2.2.2
                            rcases p940_3 (m.d 0 4) (by simp) with h953 | h953
                            · rcases p940_3 (m.d 1 4) (by simp) with h954 | h954
                              · linarith only [h2, h954, hlam]
                              · linarith only [h925, h954, hlam]
                            · linarith only [h921, h953, hlam]
                          · have p940_0 := h940c.1
                            have p940_1 := h940c.2.1
                            have p940_2 := h940c.2.2.1
                            have p940_3 := h940c.2.2.2
                            rcases p940_3 (m.d 0 4) (by simp) with h958 | h958
                            · rcases p940_3 (m.d 1 4) (by simp) with h959 | h959
                              · linarith only [h2, h959, hlam]
                              · linarith only [h927, h959, hlam]
                            · linarith only [h923, h958, hlam]
                          · have p940_0 := h940c.1
                            have p940_1 := h940c.2.1
                            have p940_2 := h940c.2.2.1
                            have p940_3 := h940c.2.2.2
                            linarith only [h921, h925, h929, h935, hc34, hlam, hphi, ht0b, ht45, ht5b, p940_1, u0elo1]
                          · have p940_0 := h940c.1
                            have p940_1 := h940c.2.1
                            have p940_2 := h940c.2.2.1
                            have p940_3 := h940c.2.2.2
                            linarith only [h2, hlam, p940_1]
                          · have p940_0 := h940c.1
                            have p940_1 := h940c.2.1
                            have p940_2 := h940c.2.2.1
                            have p940_3 := h940c.2.2.2
                            linarith only [hlam, p940_0]
                          · have p940_0 := h940c.1
                            have p940_1 := h940c.2.1
                            have p940_2 := h940c.2.2.1
                            have p940_3 := h940c.2.2.2
                            linarith only [h929, h935, hc34, hc45, hlam, hphi, p940_1]
                          · have p940_0 := h940c.1
                            have p940_1 := h940c.2.1
                            have p940_2 := h940c.2.2.1
                            have p940_3 := h940c.2.2.2
                            linarith only [h0, h925, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p940_1, u1elo0]
                          · have p940_0 := h940c.1
                            have p940_1 := h940c.2.1
                            have p940_2 := h940c.2.2.1
                            have p940_3 := h940c.2.2.2
                            linarith only [h929, hlam, p940_0]
                          · have p940_0 := h940c.1
                            have p940_1 := h940c.2.1
                            have p940_2 := h940c.2.2.1
                            have p940_3 := h940c.2.2.2
                            linarith only [h921, hlam, p940_1]
                          · have p940_0 := h940c.1
                            have p940_1 := h940c.2.1
                            have p940_2 := h940c.2.2.1
                            have p940_3 := h940c.2.2.2
                            linarith only [h925, hlam, p940_1]
                          · have p940_0 := h940c.1
                            have p940_1 := h940c.2.1
                            have p940_2 := h940c.2.2.1
                            have p940_3 := h940c.2.2.2
                            linarith only [hlam, p940_0]
                          · have p940_0 := h940c.1
                            have p940_1 := h940c.2.1
                            have p940_2 := h940c.2.2.1
                            have p940_3 := h940c.2.2.2
                            linarith only [h1, h3, h921, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p940_1, u1elo0]
                          · have p940_0 := h940c.1
                            have p940_1 := h940c.2.1
                            have p940_2 := h940c.2.2.1
                            have p940_3 := h940c.2.2.2
                            linarith only [h936, hlam, p940_0]
                          · have p940_0 := h940c.1
                            have p940_1 := h940c.2.1
                            have p940_2 := h940c.2.2.1
                            have p940_3 := h940c.2.2.2
                            linarith only [h923, hlam, p940_1]
                          · have p940_0 := h940c.1
                            have p940_1 := h940c.2.1
                            have p940_2 := h940c.2.2.1
                            have p940_3 := h940c.2.2.2
                            linarith only [h927, hlam, p940_0]
                          · have p940_0 := h940c.1
                            have p940_1 := h940c.2.1
                            have p940_2 := h940c.2.2.1
                            have p940_3 := h940c.2.2.2
                            linarith only [h935, hlam, p940_0]
                          · have p940_0 := h940c.1
                            have p940_1 := h940c.2.1
                            have p940_2 := h940c.2.2.1
                            have p940_3 := h940c.2.2.2
                            linarith only [hlam, p940_0]
                          · have p940_0 := h940c.1
                            have p940_1 := h940c.2.1
                            have p940_2 := h940c.2.2.1
                            have p940_3 := h940c.2.2.2
                            linarith only [h938, hlam, p940_0]
                          · have p940_0 := h940c.1
                            have p940_1 := h940c.2.1
                            have p940_2 := h940c.2.2.1
                            have p940_3 := h940c.2.2.2
                            linarith only [h924, hlam, p940_0]
                          · have p940_0 := h940c.1
                            have p940_1 := h940c.2.1
                            have p940_2 := h940c.2.2.1
                            have p940_3 := h940c.2.2.2
                            linarith only [h1, h3, h921, h924, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p940_1, u1elo0]
                          · have p940_0 := h940c.1
                            have p940_1 := h940c.2.1
                            have p940_2 := h940c.2.2.1
                            have p940_3 := h940c.2.2.2
                            linarith only [h1, h3, h921, h924, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p940_1, u1elo0]
                          · have p940_0 := h940c.1
                            have p940_1 := h940c.2.1
                            have p940_2 := h940c.2.2.1
                            have p940_3 := h940c.2.2.2
                            linarith only [h1, h3, h921, h924, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p940_1, u1elo0]
                          · have p940_0 := h940c.1
                            have p940_1 := h940c.2.1
                            have p940_2 := h940c.2.2.1
                            have p940_3 := h940c.2.2.2
                            linarith only [hlam, p940_0]
                    · linarith only [h3, h921, h924, h929, h935, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h985 | h985
                  · linarith only [h927, h928, h985, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h987 | h987
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h988 | h988
                      · linarith only [h2, h925, h927, h928, h985, h988, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h990 | h990
                        · linarith only [h927, h928, h985, h990, hlam]
                        · linarith only [h921, h924, h927, h928, h990, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h927, h928, h987, hc23, hc35, hlam, hphi]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h994 | h994
                · linarith only [h1, h923, h927, h994, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h996 | h996
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h997 | h997
                    · linarith only [h0, h925, h927, h997, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h3, h997, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1000 | h1000
                    · linarith only [h0, h1000, h925, h927, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h1000, h3, h921, h924, h927, h996, hc13, hc34, hlam, hphi]
            · linarith only [h3, h922, h926, hc12, hc23, hlam, hphi]
          · linarith only [h3, h921, h925, hc12, hc23, hlam, hphi]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1005 | h1005
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1006 | h1006
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1007 | h1007
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1008 | h1008
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1009 | h1009
                  · linarith only [h1009, h924, hlam, hphi, ht01, u0ehi8, u1elo3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1011 | h1011
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1012 | h1012
                      · linarith only [h0, h1005, h1012, h924, hlam, hphi, ht01, u0ehi8, u1elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1014 | h1014
                        · linarith only [h0, h1006, h1011, h1012, h1014, h924, hlam, hphi, ht01, u0ehi8, u1elo0]
                        · rcases h4bigk with h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [hlam, p1016_0]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h924, hc14, hc45, hlam, hphi, p1016_1]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h924, hc24, hc45, hlam, hphi, p1016_1]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h924, hc34, hc45, hlam, hphi, p1016_1]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h924, hlam, p1016_0]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h2, hlam, p1016_1]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [hlam, p1016_0]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h1011, h2, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1016_1, u1elo0]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h0, h1005, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1016_1, u1elo0]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h1009, hlam, p1016_0]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h921, hlam, p1016_1]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h1005, hlam, p1016_1]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [hlam, p1016_0]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h3, h921, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1016_1]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h1012, hlam, p1016_0]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h923, hlam, p1016_1]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h1007, hlam, p1016_0]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h1011, hlam, p1016_0]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [hlam, p1016_0]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h1014, hlam, p1016_0]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1016_1, u0ehi8]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            rcases p1016_3 (m.d 0 4) (by simp) with h1038 | h1038
                            · linarith only [h1038, h924, hlam]
                            · linarith only [h1038, h2, hlam]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            rcases p1016_3 (m.d 0 4) (by simp) with h1041 | h1041
                            · linarith only [h1041, h924, hlam]
                            · linarith only [h1041, h921, hlam]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            rcases p1016_3 (m.d 0 4) (by simp) with h1044 | h1044
                            · linarith only [h1044, h924, hlam]
                            · linarith only [h1044, h923, hlam]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [hlam, p1016_0]
                    · linarith only [h1011, h3, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1049 | h1049
                  · linarith only [h1049, h924, hlam, hphi, ht01, u0ehi8, u1elo3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1051 | h1051
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1052 | h1052
                      · linarith only [h1052, h924, hc24, hlam, hphi, ht01, ht12, u0ehi8]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1054 | h1054
                        · linarith only [h1054, h924, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                        · rcases h4bigk with h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c
                          · have p1056_0 := h1056c.1
                            have p1056_1 := h1056c.2.1
                            have p1056_2 := h1056c.2.2.1
                            have p1056_3 := h1056c.2.2.2
                            linarith only [hlam, p1056_0]
                          · have p1056_0 := h1056c.1
                            have p1056_1 := h1056c.2.1
                            have p1056_2 := h1056c.2.2.1
                            have p1056_3 := h1056c.2.2.2
                            linarith only [h924, hc14, hc45, hlam, hphi, p1056_1]
                          · have p1056_0 := h1056c.1
                            have p1056_1 := h1056c.2.1
                            have p1056_2 := h1056c.2.2.1
                            have p1056_3 := h1056c.2.2.2
                            linarith only [h924, hc24, hc45, hlam, hphi, p1056_1]
                          · have p1056_0 := h1056c.1
                            have p1056_1 := h1056c.2.1
                            have p1056_2 := h1056c.2.2.1
                            have p1056_3 := h1056c.2.2.2
                            linarith only [h924, hc34, hc45, hlam, hphi, p1056_1]
                          · have p1056_0 := h1056c.1
                            have p1056_1 := h1056c.2.1
                            have p1056_2 := h1056c.2.2.1
                            have p1056_3 := h1056c.2.2.2
                            linarith only [h924, hlam, p1056_0]
                          · have p1056_0 := h1056c.1
                            have p1056_1 := h1056c.2.1
                            have p1056_2 := h1056c.2.2.1
                            have p1056_3 := h1056c.2.2.2
                            linarith only [h2, hlam, p1056_1]
                          · have p1056_0 := h1056c.1
                            have p1056_1 := h1056c.2.1
                            have p1056_2 := h1056c.2.2.1
                            have p1056_3 := h1056c.2.2.2
                            linarith only [hlam, p1056_0]
                          · have p1056_0 := h1056c.1
                            have p1056_1 := h1056c.2.1
                            have p1056_2 := h1056c.2.2.1
                            have p1056_3 := h1056c.2.2.2
                            linarith only [h2, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1056_1, u1elo0]
                          · have p1056_0 := h1056c.1
                            have p1056_1 := h1056c.2.1
                            have p1056_2 := h1056c.2.2.1
                            have p1056_3 := h1056c.2.2.2
                            linarith only [h0, h1006, h1007, h1008, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1056_1, u1elo0]
                          · have p1056_0 := h1056c.1
                            have p1056_1 := h1056c.2.1
                            have p1056_2 := h1056c.2.2.1
                            have p1056_3 := h1056c.2.2.2
                            linarith only [h1049, hlam, p1056_0]
                          · have p1056_0 := h1056c.1
                            have p1056_1 := h1056c.2.1
                            have p1056_2 := h1056c.2.2.1
                            have p1056_3 := h1056c.2.2.2
                            linarith only [h921, hlam, p1056_1]
                          · have p1056_0 := h1056c.1
                            have p1056_1 := h1056c.2.1
                            have p1056_2 := h1056c.2.2.1
                            have p1056_3 := h1056c.2.2.2
                            linarith only [h1005, hlam, p1056_1]
                          · have p1056_0 := h1056c.1
                            have p1056_1 := h1056c.2.1
                            have p1056_2 := h1056c.2.2.1
                            have p1056_3 := h1056c.2.2.2
                            linarith only [hlam, p1056_0]
                          · have p1056_0 := h1056c.1
                            have p1056_1 := h1056c.2.1
                            have p1056_2 := h1056c.2.2.1
                            have p1056_3 := h1056c.2.2.2
                            linarith only [h921, hc34, hlam, hphi, ht0b, ht45, ht5b, p1056_1, u0elo1]
                          · have p1056_0 := h1056c.1
                            have p1056_1 := h1056c.2.1
                            have p1056_2 := h1056c.2.2.1
                            have p1056_3 := h1056c.2.2.2
                            linarith only [h1052, hlam, p1056_0]
                          · have p1056_0 := h1056c.1
                            have p1056_1 := h1056c.2.1
                            have p1056_2 := h1056c.2.2.1
                            have p1056_3 := h1056c.2.2.2
                            linarith only [h923, hlam, p1056_1]
                          · have p1056_0 := h1056c.1
                            have p1056_1 := h1056c.2.1
                            have p1056_2 := h1056c.2.2.1
                            have p1056_3 := h1056c.2.2.2
                            linarith only [h1007, hlam, p1056_0]
                          · have p1056_0 := h1056c.1
                            have p1056_1 := h1056c.2.1
                            have p1056_2 := h1056c.2.2.1
                            have p1056_3 := h1056c.2.2.2
                            linarith only [h1051, hlam, p1056_0]
                          · have p1056_0 := h1056c.1
                            have p1056_1 := h1056c.2.1
                            have p1056_2 := h1056c.2.2.1
                            have p1056_3 := h1056c.2.2.2
                            linarith only [hlam, p1056_0]
                          · have p1056_0 := h1056c.1
                            have p1056_1 := h1056c.2.1
                            have p1056_2 := h1056c.2.2.1
                            have p1056_3 := h1056c.2.2.2
                            linarith only [h1054, hlam, p1056_0]
                          · have p1056_0 := h1056c.1
                            have p1056_1 := h1056c.2.1
                            have p1056_2 := h1056c.2.2.1
                            have p1056_3 := h1056c.2.2.2
                            linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1056_1, u0ehi8]
                          · have p1056_0 := h1056c.1
                            have p1056_1 := h1056c.2.1
                            have p1056_2 := h1056c.2.2.1
                            have p1056_3 := h1056c.2.2.2
                            rcases p1056_3 (m.d 0 4) (by simp) with h1078 | h1078
                            · linarith only [h1078, h924, hlam]
                            · linarith only [h1078, h2, hlam]
                          · have p1056_0 := h1056c.1
                            have p1056_1 := h1056c.2.1
                            have p1056_2 := h1056c.2.2.1
                            have p1056_3 := h1056c.2.2.2
                            rcases p1056_3 (m.d 0 4) (by simp) with h1081 | h1081
                            · linarith only [h1081, h924, hlam]
                            · linarith only [h1081, h921, hlam]
                          · have p1056_0 := h1056c.1
                            have p1056_1 := h1056c.2.1
                            have p1056_2 := h1056c.2.2.1
                            have p1056_3 := h1056c.2.2.2
                            rcases p1056_3 (m.d 0 4) (by simp) with h1084 | h1084
                            · linarith only [h1084, h924, hlam]
                            · linarith only [h1084, h923, hlam]
                          · have p1056_0 := h1056c.1
                            have p1056_1 := h1056c.2.1
                            have p1056_2 := h1056c.2.2.1
                            have p1056_3 := h1056c.2.2.2
                            linarith only [hlam, p1056_0]
                    · linarith only [h1051, h3, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1089 | h1089
                · linarith only [h1, h1007, h1089, h923, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1091 | h1091
                  · linarith only [h1091, h924, hlam, hphi, ht01, u0ehi8, u1elo3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1093 | h1093
                    · linarith only [h0, h1005, h1007, h1093, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h1093, h3, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
            · linarith only [h1006, h3, h922, hc12, hc23, hlam, hphi]
          · linarith only [h1005, h3, h921, hc12, hc23, hlam, hphi]
      · linarith only [h3, h921, h923, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1099 | h1099
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1100 | h1100
        · linarith only [h1100, h921, h922, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1102 | h1102
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1103 | h1103
            · linarith only [h0, h1103, h922, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1105 | h1105
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1106 | h1106
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1107 | h1107
                  · linarith only [h1100, h1107, hlam, hphi, ht01, u0ehi8, u1elo3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1109 | h1109
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1110 | h1110
                      · linarith only [h1, h1100, h1102, h1103, h1106, h1110, hlam, hphi, ht01, u0ehi8, u1elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1112 | h1112
                        · linarith only [h1, h1102, h1103, h1106, h1109, h1110, h1112, h921, h922, hlam, hphi, ht01, u0ehi8, u1elo0]
                        · rcases h4bigk with h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [hlam, p1114_0]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [h1110, h921, h922, hc14, hc45, hlam, hphi, p1114_1]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [h1110, h921, h922, hc24, hc45, hlam, hphi, p1114_1]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [h1110, h921, h922, hc34, hc45, hlam, hphi, p1114_1]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [h1100, hlam, p1114_0]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [h2, hlam, p1114_1]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [hlam, p1114_0]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [h1109, h1110, h2, h921, h922, hc34, hc45, hlam, hphi, ht01, p1114_1, u0ehi8, u1elo0]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [h1, h1102, h1103, h1106, h1110, h921, h922, hc34, hc45, hlam, hphi, ht01, p1114_1, u0ehi8, u1elo0]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [h1107, hlam, p1114_0]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [h921, hlam, p1114_1]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [h1102, hlam, p1114_1]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [hlam, p1114_0]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [h1110, h921, h922, hc34, hc45, hlam, hphi, p1114_1]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [h1110, hlam, p1114_0]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [h1099, hlam, p1114_1]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [h1105, hlam, p1114_0]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [h1109, hlam, p1114_0]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [hlam, p1114_0]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [h1112, hlam, p1114_0]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1114_1, u0ehi8]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            rcases p1114_3 (m.d 0 4) (by simp) with h1136 | h1136
                            · linarith only [h1100, h1136, hlam]
                            · linarith only [h1136, h2, hlam]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            rcases p1114_3 (m.d 0 4) (by simp) with h1139 | h1139
                            · linarith only [h1100, h1139, hlam]
                            · linarith only [h1139, h921, hlam]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            rcases p1114_3 (m.d 0 4) (by simp) with h1142 | h1142
                            · linarith only [h1100, h1142, hlam]
                            · linarith only [h1099, h1142, hlam]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [hlam, p1114_0]
                    · linarith only [h1109, h3, h921, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1147 | h1147
                  · linarith only [h1100, h1102, h1147, hlam, hphi, ht01, u0ehi8, u1elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1149 | h1149
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1150 | h1150
                      · linarith only [h0, h1100, h1102, h1150, hlam, hphi, ht01, u0ehi8, u1elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1152 | h1152
                        · linarith only [h0, h1102, h1149, h1150, h1152, h921, h922, hlam, hphi, ht01, u0ehi8, u1elo0]
                        · rcases h4bigk with h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c | h1154c
                          · have p1154_0 := h1154c.1
                            have p1154_1 := h1154c.2.1
                            have p1154_2 := h1154c.2.2.1
                            have p1154_3 := h1154c.2.2.2
                            linarith only [hlam, p1154_0]
                          · have p1154_0 := h1154c.1
                            have p1154_1 := h1154c.2.1
                            have p1154_2 := h1154c.2.2.1
                            have p1154_3 := h1154c.2.2.2
                            linarith only [h1150, h921, h922, hc14, hc45, hlam, hphi, p1154_1]
                          · have p1154_0 := h1154c.1
                            have p1154_1 := h1154c.2.1
                            have p1154_2 := h1154c.2.2.1
                            have p1154_3 := h1154c.2.2.2
                            linarith only [h1150, h921, h922, hc24, hc45, hlam, hphi, p1154_1]
                          · have p1154_0 := h1154c.1
                            have p1154_1 := h1154c.2.1
                            have p1154_2 := h1154c.2.2.1
                            have p1154_3 := h1154c.2.2.2
                            linarith only [h1150, h921, h922, hc34, hc45, hlam, hphi, p1154_1]
                          · have p1154_0 := h1154c.1
                            have p1154_1 := h1154c.2.1
                            have p1154_2 := h1154c.2.2.1
                            have p1154_3 := h1154c.2.2.2
                            linarith only [h1100, hlam, p1154_0]
                          · have p1154_0 := h1154c.1
                            have p1154_1 := h1154c.2.1
                            have p1154_2 := h1154c.2.2.1
                            have p1154_3 := h1154c.2.2.2
                            linarith only [h2, hlam, p1154_1]
                          · have p1154_0 := h1154c.1
                            have p1154_1 := h1154c.2.1
                            have p1154_2 := h1154c.2.2.1
                            have p1154_3 := h1154c.2.2.2
                            linarith only [hlam, p1154_0]
                          · have p1154_0 := h1154c.1
                            have p1154_1 := h1154c.2.1
                            have p1154_2 := h1154c.2.2.1
                            have p1154_3 := h1154c.2.2.2
                            linarith only [h1149, h1150, h2, h921, h922, hc34, hc45, hlam, hphi, ht01, p1154_1, u0ehi8, u1elo0]
                          · have p1154_0 := h1154c.1
                            have p1154_1 := h1154c.2.1
                            have p1154_2 := h1154c.2.2.1
                            have p1154_3 := h1154c.2.2.2
                            linarith only [h0, h1102, h1150, h921, h922, hc34, hc45, hlam, hphi, ht01, p1154_1, u0ehi8, u1elo0]
                          · have p1154_0 := h1154c.1
                            have p1154_1 := h1154c.2.1
                            have p1154_2 := h1154c.2.2.1
                            have p1154_3 := h1154c.2.2.2
                            linarith only [h1147, hlam, p1154_0]
                          · have p1154_0 := h1154c.1
                            have p1154_1 := h1154c.2.1
                            have p1154_2 := h1154c.2.2.1
                            have p1154_3 := h1154c.2.2.2
                            linarith only [h921, hlam, p1154_1]
                          · have p1154_0 := h1154c.1
                            have p1154_1 := h1154c.2.1
                            have p1154_2 := h1154c.2.2.1
                            have p1154_3 := h1154c.2.2.2
                            linarith only [h1102, hlam, p1154_1]
                          · have p1154_0 := h1154c.1
                            have p1154_1 := h1154c.2.1
                            have p1154_2 := h1154c.2.2.1
                            have p1154_3 := h1154c.2.2.2
                            linarith only [hlam, p1154_0]
                          · have p1154_0 := h1154c.1
                            have p1154_1 := h1154c.2.1
                            have p1154_2 := h1154c.2.2.1
                            have p1154_3 := h1154c.2.2.2
                            linarith only [h1150, h921, h922, hc34, hc45, hlam, hphi, p1154_1]
                          · have p1154_0 := h1154c.1
                            have p1154_1 := h1154c.2.1
                            have p1154_2 := h1154c.2.2.1
                            have p1154_3 := h1154c.2.2.2
                            linarith only [h1150, hlam, p1154_0]
                          · have p1154_0 := h1154c.1
                            have p1154_1 := h1154c.2.1
                            have p1154_2 := h1154c.2.2.1
                            have p1154_3 := h1154c.2.2.2
                            linarith only [h1099, hlam, p1154_1]
                          · have p1154_0 := h1154c.1
                            have p1154_1 := h1154c.2.1
                            have p1154_2 := h1154c.2.2.1
                            have p1154_3 := h1154c.2.2.2
                            linarith only [h1105, hlam, p1154_0]
                          · have p1154_0 := h1154c.1
                            have p1154_1 := h1154c.2.1
                            have p1154_2 := h1154c.2.2.1
                            have p1154_3 := h1154c.2.2.2
                            linarith only [h1149, hlam, p1154_0]
                          · have p1154_0 := h1154c.1
                            have p1154_1 := h1154c.2.1
                            have p1154_2 := h1154c.2.2.1
                            have p1154_3 := h1154c.2.2.2
                            linarith only [hlam, p1154_0]
                          · have p1154_0 := h1154c.1
                            have p1154_1 := h1154c.2.1
                            have p1154_2 := h1154c.2.2.1
                            have p1154_3 := h1154c.2.2.2
                            linarith only [h1152, hlam, p1154_0]
                          · have p1154_0 := h1154c.1
                            have p1154_1 := h1154c.2.1
                            have p1154_2 := h1154c.2.2.1
                            have p1154_3 := h1154c.2.2.2
                            linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1154_1, u0ehi8]
                          · have p1154_0 := h1154c.1
                            have p1154_1 := h1154c.2.1
                            have p1154_2 := h1154c.2.2.1
                            have p1154_3 := h1154c.2.2.2
                            rcases p1154_3 (m.d 0 4) (by simp) with h1176 | h1176
                            · linarith only [h1100, h1176, hlam]
                            · linarith only [h1176, h2, hlam]
                          · have p1154_0 := h1154c.1
                            have p1154_1 := h1154c.2.1
                            have p1154_2 := h1154c.2.2.1
                            have p1154_3 := h1154c.2.2.2
                            rcases p1154_3 (m.d 0 4) (by simp) with h1179 | h1179
                            · linarith only [h1100, h1179, hlam]
                            · linarith only [h1179, h921, hlam]
                          · have p1154_0 := h1154c.1
                            have p1154_1 := h1154c.2.1
                            have p1154_2 := h1154c.2.2.1
                            have p1154_3 := h1154c.2.2.2
                            rcases p1154_3 (m.d 0 4) (by simp) with h1182 | h1182
                            · linarith only [h1100, h1182, hlam]
                            · linarith only [h1099, h1182, hlam]
                          · have p1154_0 := h1154c.1
                            have p1154_1 := h1154c.2.1
                            have p1154_2 := h1154c.2.2.1
                            have p1154_3 := h1154c.2.2.2
                            linarith only [hlam, p1154_0]
                    · linarith only [h1149, h3, h921, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1187 | h1187
                · linarith only [h1099, h1105, h1187, hc35, hlam, hphi, ht0b, ht5b, u0elo2]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1189 | h1189
                  · linarith only [h1, h1099, h1100, h1105, h1189, hlam, hphi, ht01, u0ehi8, u1elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1191 | h1191
                    · linarith only [h0, h1102, h1105, h1191, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h1191, h3, h921, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
          · linarith only [h1102, h3, h921, hc12, hc23, hlam, hphi]
      · linarith only [h1099, h3, h921, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1196 | h1196
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1197 | h1197
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1198 | h1198
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1199 | h1199
          · linarith only [h1196, h1199, h921, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1201 | h1201
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1202 | h1202
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1203 | h1203
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1204 | h1204
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1205 | h1205
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1206 | h1206
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1207 | h1207
                        · linarith only [h1, h1202, h1207, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · linarith only [h1, h1202, h1204, h1207, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · linarith only [h1, h1196, h1202, h1204, h1206, h921, hlam, hphi, ht01, u0ehi9, u1elo0]
                    · linarith only [h1196, h1205, h3, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                  · linarith only [h1197, h1198, h1199, h1201, h1204, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                · linarith only [h1199, h1201, h1202, h1203, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1214 | h1214
                · linarith only [h1, h1197, h1202, h1214, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1216 | h1216
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1217 | h1217
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1218 | h1218
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1219 | h1219
                        · rcases h4bigk with h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c
                          · have p1220_0 := h1220c.1
                            have p1220_1 := h1220c.2.1
                            have p1220_2 := h1220c.2.2.1
                            have p1220_3 := h1220c.2.2.2
                            linarith only [hlam, p1220_0]
                          · have p1220_0 := h1220c.1
                            have p1220_1 := h1220c.2.1
                            have p1220_2 := h1220c.2.2.1
                            have p1220_3 := h1220c.2.2.2
                            linarith only [h1, h1197, h1199, h1201, hc25, hlam, hphi, ht01, ht0b, ht5b, p1220_1, u1elo0]
                          · have p1220_0 := h1220c.1
                            have p1220_1 := h1220c.2.1
                            have p1220_2 := h1220c.2.2.1
                            have p1220_3 := h1220c.2.2.2
                            linarith only [h921, hlam, p1220_0]
                          · have p1220_0 := h1220c.1
                            have p1220_1 := h1220c.2.1
                            have p1220_2 := h1220c.2.2.1
                            have p1220_3 := h1220c.2.2.2
                            linarith only [h1, h1197, h1214, h1219, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1220_1, u1elo0]
                          · have p1220_0 := h1220c.1
                            have p1220_1 := h1220c.2.1
                            have p1220_2 := h1220c.2.2.1
                            have p1220_3 := h1220c.2.2.2
                            rcases p1220_3 (m.d 0 4) (by simp) with h1225 | h1225
                            · rcases p1220_3 (m.d 1 4) (by simp) with h1226 | h1226
                              · linarith only [h1226, h2, hlam]
                              · linarith only [h1216, h1226, hlam]
                            · linarith only [h1225, hlam, p1220_0]
                          · have p1220_0 := h1220c.1
                            have p1220_1 := h1220c.2.1
                            have p1220_2 := h1220c.2.2.1
                            have p1220_3 := h1220c.2.2.2
                            linarith only [h2, hlam, p1220_1]
                          · have p1220_0 := h1220c.1
                            have p1220_1 := h1220c.2.1
                            have p1220_2 := h1220c.2.2.1
                            have p1220_3 := h1220c.2.2.2
                            linarith only [hlam, p1220_0]
                          · have p1220_0 := h1220c.1
                            have p1220_1 := h1220c.2.1
                            have p1220_2 := h1220c.2.2.1
                            have p1220_3 := h1220c.2.2.2
                            linarith only [h1199, hlam, p1220_0]
                          · have p1220_0 := h1220c.1
                            have p1220_1 := h1220c.2.1
                            have p1220_2 := h1220c.2.2.1
                            have p1220_3 := h1220c.2.2.2
                            linarith only [h1202, hlam, p1220_1]
                          · have p1220_0 := h1220c.1
                            have p1220_1 := h1220c.2.1
                            have p1220_2 := h1220c.2.2.1
                            have p1220_3 := h1220c.2.2.2
                            linarith only [h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p1220_1, u1elo0]
                          · have p1220_0 := h1220c.1
                            have p1220_1 := h1220c.2.1
                            have p1220_2 := h1220c.2.2.1
                            have p1220_3 := h1220c.2.2.2
                            linarith only [h1217, hc23, hlam, hphi, ht01, ht12, p1220_1, u0ehi8]
                          · have p1220_0 := h1220c.1
                            have p1220_1 := h1220c.2.1
                            have p1220_2 := h1220c.2.2.1
                            have p1220_3 := h1220c.2.2.2
                            rcases p1220_3 (m.d 0 4) (by simp) with h1236 | h1236
                            · linarith only [h1236, h921, hlam]
                            · linarith only [h1236, h2, hlam]
                          · have p1220_0 := h1220c.1
                            have p1220_1 := h1220c.2.1
                            have p1220_2 := h1220c.2.2.1
                            have p1220_3 := h1220c.2.2.2
                            linarith only [hlam, p1220_0]
                          · have p1220_0 := h1220c.1
                            have p1220_1 := h1220c.2.1
                            have p1220_2 := h1220c.2.2.1
                            have p1220_3 := h1220c.2.2.2
                            rcases p1220_3 (m.d 0 4) (by simp) with h1240 | h1240
                            · linarith only [h1240, h921, hlam]
                            · linarith only [h1197, h1240, hlam]
                          · have p1220_0 := h1220c.1
                            have p1220_1 := h1220c.2.1
                            have p1220_2 := h1220c.2.2.1
                            have p1220_3 := h1220c.2.2.2
                            rcases p1220_3 (m.d 0 4) (by simp) with h1243 | h1243
                            · linarith only [h1243, h921, hlam]
                            · linarith only [h1198, h1243, hlam]
                          · have p1220_0 := h1220c.1
                            have p1220_1 := h1220c.2.1
                            have p1220_2 := h1220c.2.2.1
                            have p1220_3 := h1220c.2.2.2
                            linarith only [h1197, hlam, p1220_1]
                          · have p1220_0 := h1220c.1
                            have p1220_1 := h1220c.2.1
                            have p1220_2 := h1220c.2.2.1
                            have p1220_3 := h1220c.2.2.2
                            linarith only [h1, h1197, h1199, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1220_1, u1elo0]
                          · have p1220_0 := h1220c.1
                            have p1220_1 := h1220c.2.1
                            have p1220_2 := h1220c.2.2.1
                            have p1220_3 := h1220c.2.2.2
                            linarith only [h1217, hlam, p1220_0]
                          · have p1220_0 := h1220c.1
                            have p1220_1 := h1220c.2.1
                            have p1220_2 := h1220c.2.2.1
                            have p1220_3 := h1220c.2.2.2
                            linarith only [hlam, p1220_0]
                          · have p1220_0 := h1220c.1
                            have p1220_1 := h1220c.2.1
                            have p1220_2 := h1220c.2.2.1
                            have p1220_3 := h1220c.2.2.2
                            linarith only [h1, h1197, hc45, hlam, hphi, ht01, ht0b, ht5b, p1220_1, u1elo0]
                          · have p1220_0 := h1220c.1
                            have p1220_1 := h1220c.2.1
                            have p1220_2 := h1220c.2.2.1
                            have p1220_3 := h1220c.2.2.2
                            linarith only [h1198, hlam, p1220_0]
                          · have p1220_0 := h1220c.1
                            have p1220_1 := h1220c.2.1
                            have p1220_2 := h1220c.2.2.1
                            have p1220_3 := h1220c.2.2.2
                            linarith only [h1216, hlam, p1220_0]
                          · have p1220_0 := h1220c.1
                            have p1220_1 := h1220c.2.1
                            have p1220_2 := h1220c.2.2.1
                            have p1220_3 := h1220c.2.2.2
                            linarith only [h1218, hlam, p1220_0]
                          · have p1220_0 := h1220c.1
                            have p1220_1 := h1220c.2.1
                            have p1220_2 := h1220c.2.2.1
                            have p1220_3 := h1220c.2.2.2
                            linarith only [h1219, hlam, p1220_0]
                          · have p1220_0 := h1220c.1
                            have p1220_1 := h1220c.2.1
                            have p1220_2 := h1220c.2.2.1
                            have p1220_3 := h1220c.2.2.2
                            linarith only [hlam, p1220_0]
                        · linarith only [h0, h1201, h1218, h1219, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · linarith only [h1196, h1218, h921, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi9]
                    · linarith only [h1, h1196, h1197, h1217, h3, hlam, hphi, ht01, u0ehi9, u1elo0]
                  · linarith only [h1198, h1199, h1201, h1216, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
            · linarith only [h1196, h1201, h3, hc12, hc23, hlam, hphi]
        · linarith only [h1196, h1198, h921, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1262 | h1262
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1263 | h1263
          · linarith only [h1196, h1263, h921, hlam, hphi, ht01, u0ehi9, u1elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1265 | h1265
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1266 | h1266
              · linarith only [h1197, h1266, hlam, hphi, ht01, u0ehi7, u1elo2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1268 | h1268
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1269 | h1269
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1270 | h1270
                    · linarith only [h1196, h1197, h1270, h3, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                    · linarith only [h1196, h1270, h3, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                  · linarith only [h1262, h1263, h1265, h1269, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1274 | h1274
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1275 | h1275
                    · linarith only [h1196, h1197, h1275, h3, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                    · linarith only [h1196, h1275, h3, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                  · linarith only [h1262, h1263, h1265, h1274, h2, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · linarith only [h1196, h1265, h3, hc12, hc23, hlam, hphi]
        · linarith only [h1196, h1262, h921, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1281 | h1281
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1282 | h1282
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1283 | h1283
          · linarith only [h1283, h921, hlam, hphi, ht01, u0ehi6, u1elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1285 | h1285
            · linarith only [h1196, h1285, hlam, hphi, ht01, u0ehi6, u1elo1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1287 | h1287
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1288 | h1288
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1289 | h1289
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1290 | h1290
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1291 | h1291
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1292 | h1292
                        · linarith only [h1, h1287, h1292, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · linarith only [h1, h1287, h1289, h1292, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · linarith only [h1, h1287, h1289, h1291, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · linarith only [h1290, h3, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1297 | h1297
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1298 | h1298
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1299 | h1299
                        · linarith only [h1287, h1289, h1299, hlam]
                        · rcases h4bigk with h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c
                          · have p1301_0 := h1301c.1
                            have p1301_1 := h1301c.2.1
                            have p1301_2 := h1301c.2.2.1
                            have p1301_3 := h1301c.2.2.2
                            linarith only [hlam, p1301_0]
                          · have p1301_0 := h1301c.1
                            have p1301_1 := h1301c.2.1
                            have p1301_2 := h1301c.2.2.1
                            have p1301_3 := h1301c.2.2.2
                            rcases p1301_3 (m.d 0 4) (by simp) with h1303 | h1303
                            · rcases p1301_3 (m.d 1 4) (by simp) with h1304 | h1304
                              · linarith only [h1304, h2, hlam]
                              · rcases p1301_3 (m.d 2 4) (by simp) with h1306 | h1306
                                · rcases p1301_3 (m.d 3 4) (by simp) with h1307 | h1307
                                  · linarith only [h1281, h1307, hlam]
                                  · rcases p1301_3 (m.d 4 5) (by simp) with h1309 | h1309
                                    · linarith only [h1282, h1309, hlam]
                                    · linarith only [h1289, h1309, hlam]
                                · linarith only [h1283, h1306, hlam]
                            · linarith only [h1303, h2, hlam]
                          · have p1301_0 := h1301c.1
                            have p1301_1 := h1301c.2.1
                            have p1301_2 := h1301c.2.2.1
                            have p1301_3 := h1301c.2.2.2
                            linarith only [h921, hlam, p1301_0]
                          · have p1301_0 := h1301c.1
                            have p1301_1 := h1301c.2.1
                            have p1301_2 := h1301c.2.2.1
                            have p1301_3 := h1301c.2.2.2
                            rcases p1301_3 (m.d 0 4) (by simp) with h1315 | h1315
                            · rcases p1301_3 (m.d 1 4) (by simp) with h1316 | h1316
                              · linarith only [h1316, h2, hlam]
                              · linarith only [h1287, h1316, hlam]
                            · linarith only [h1281, h1315, hlam]
                          · have p1301_0 := h1301c.1
                            have p1301_1 := h1301c.2.1
                            have p1301_2 := h1301c.2.2.1
                            have p1301_3 := h1301c.2.2.2
                            linarith only [h1281, h1283, h1289, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1301_1, u0elo2]
                          · have p1301_0 := h1301c.1
                            have p1301_1 := h1301c.2.1
                            have p1301_2 := h1301c.2.2.1
                            have p1301_3 := h1301c.2.2.2
                            linarith only [h2, hlam, p1301_1]
                          · have p1301_0 := h1301c.1
                            have p1301_1 := h1301c.2.1
                            have p1301_2 := h1301c.2.2.1
                            have p1301_3 := h1301c.2.2.2
                            linarith only [hlam, p1301_0]
                          · have p1301_0 := h1301c.1
                            have p1301_1 := h1301c.2.1
                            have p1301_2 := h1301c.2.2.1
                            have p1301_3 := h1301c.2.2.2
                            linarith only [h1283, hlam, p1301_0]
                          · have p1301_0 := h1301c.1
                            have p1301_1 := h1301c.2.1
                            have p1301_2 := h1301c.2.2.1
                            have p1301_3 := h1301c.2.2.2
                            linarith only [h1289, hc34, hc45, hlam, hphi, p1301_1]
                          · have p1301_0 := h1301c.1
                            have p1301_1 := h1301c.2.1
                            have p1301_2 := h1301c.2.2.1
                            have p1301_3 := h1301c.2.2.2
                            linarith only [h1289, hlam, p1301_0]
                          · have p1301_0 := h1301c.1
                            have p1301_1 := h1301c.2.1
                            have p1301_2 := h1301c.2.2.1
                            have p1301_3 := h1301c.2.2.2
                            linarith only [h1297, hc23, hlam, hphi, ht01, ht12, p1301_1, u0ehi8]
                          · have p1301_0 := h1301c.1
                            have p1301_1 := h1301c.2.1
                            have p1301_2 := h1301c.2.2.1
                            have p1301_3 := h1301c.2.2.2
                            rcases p1301_3 (m.d 0 4) (by simp) with h1327 | h1327
                            · linarith only [h1327, h921, hlam]
                            · linarith only [h1327, h2, hlam]
                          · have p1301_0 := h1301c.1
                            have p1301_1 := h1301c.2.1
                            have p1301_2 := h1301c.2.2.1
                            have p1301_3 := h1301c.2.2.2
                            linarith only [hlam, p1301_0]
                          · have p1301_0 := h1301c.1
                            have p1301_1 := h1301c.2.1
                            have p1301_2 := h1301c.2.2.1
                            have p1301_3 := h1301c.2.2.2
                            rcases p1301_3 (m.d 0 4) (by simp) with h1331 | h1331
                            · linarith only [h1331, h921, hlam]
                            · linarith only [h1281, h1331, hlam]
                          · have p1301_0 := h1301c.1
                            have p1301_1 := h1301c.2.1
                            have p1301_2 := h1301c.2.2.1
                            have p1301_3 := h1301c.2.2.2
                            linarith only [h1283, h1289, h1297, hc12, hc23, hlam, hphi, p1301_1]
                          · have p1301_0 := h1301c.1
                            have p1301_1 := h1301c.2.1
                            have p1301_2 := h1301c.2.2.1
                            have p1301_3 := h1301c.2.2.2
                            linarith only [h1281, hlam, p1301_1]
                          · have p1301_0 := h1301c.1
                            have p1301_1 := h1301c.2.1
                            have p1301_2 := h1301c.2.2.1
                            have p1301_3 := h1301c.2.2.2
                            linarith only [h1287, hlam, p1301_0]
                          · have p1301_0 := h1301c.1
                            have p1301_1 := h1301c.2.1
                            have p1301_2 := h1301c.2.2.1
                            have p1301_3 := h1301c.2.2.2
                            linarith only [h1297, hlam, p1301_0]
                          · have p1301_0 := h1301c.1
                            have p1301_1 := h1301c.2.1
                            have p1301_2 := h1301c.2.2.1
                            have p1301_3 := h1301c.2.2.2
                            linarith only [hlam, p1301_0]
                          · have p1301_0 := h1301c.1
                            have p1301_1 := h1301c.2.1
                            have p1301_2 := h1301c.2.2.1
                            have p1301_3 := h1301c.2.2.2
                            linarith only [h1299, hlam, p1301_0]
                          · have p1301_0 := h1301c.1
                            have p1301_1 := h1301c.2.1
                            have p1301_2 := h1301c.2.2.1
                            have p1301_3 := h1301c.2.2.2
                            linarith only [h1282, hlam, p1301_0]
                          · have p1301_0 := h1301c.1
                            have p1301_1 := h1301c.2.1
                            have p1301_2 := h1301c.2.2.1
                            have p1301_3 := h1301c.2.2.2
                            linarith only [h1282, h1283, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1301_1, u0elo3]
                          · have p1301_0 := h1301c.1
                            have p1301_1 := h1301c.2.1
                            have p1301_2 := h1301c.2.2.1
                            have p1301_3 := h1301c.2.2.2
                            linarith only [h1298, hlam, p1301_0]
                          · have p1301_0 := h1301c.1
                            have p1301_1 := h1301c.2.1
                            have p1301_2 := h1301c.2.2.1
                            have p1301_3 := h1301c.2.2.2
                            linarith only [h1, h1281, h1282, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1301_1, u1elo0]
                          · have p1301_0 := h1301c.1
                            have p1301_1 := h1301c.2.1
                            have p1301_2 := h1301c.2.2.1
                            have p1301_3 := h1301c.2.2.2
                            linarith only [hlam, p1301_0]
                      · linarith only [h1, h1281, h1282, h1298, h921, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h1297, h3, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1347 | h1347
                  · linarith only [h1287, h1288, h1347, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1349 | h1349
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1350 | h1350
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1351 | h1351
                        · linarith only [h1287, h1288, h1347, h1351, hlam]
                        · linarith only [h1, h1281, h1282, h1287, h1288, h1351, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · linarith only [h1, h1281, h1282, h1350, h921, hlam, hphi, ht01, u0ehi6, u1elo0]
                    · linarith only [h1287, h1349, h3, hlam, hphi, ht01, u0ehi6, u1elo2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1356 | h1356
                · linarith only [h1, h1281, h1287, h1356, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1358 | h1358
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1359 | h1359
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1360 | h1360
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1361 | h1361
                        · rcases h4bigk with h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c
                          · have p1362_0 := h1362c.1
                            have p1362_1 := h1362c.2.1
                            have p1362_2 := h1362c.2.2.1
                            have p1362_3 := h1362c.2.2.2
                            linarith only [hlam, p1362_0]
                          · have p1362_0 := h1362c.1
                            have p1362_1 := h1362c.2.1
                            have p1362_2 := h1362c.2.2.1
                            have p1362_3 := h1362c.2.2.2
                            linarith only [h1, h1281, h1358, hc45, hlam, hphi, ht01, ht0b, ht5b, p1362_1, u1elo0]
                          · have p1362_0 := h1362c.1
                            have p1362_1 := h1362c.2.1
                            have p1362_2 := h1362c.2.2.1
                            have p1362_3 := h1362c.2.2.2
                            linarith only [h921, hlam, p1362_0]
                          · have p1362_0 := h1362c.1
                            have p1362_1 := h1362c.2.1
                            have p1362_2 := h1362c.2.2.1
                            have p1362_3 := h1362c.2.2.2
                            linarith only [h1, h1281, h1356, h1361, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1362_1, u1elo0]
                          · have p1362_0 := h1362c.1
                            have p1362_1 := h1362c.2.1
                            have p1362_2 := h1362c.2.2.1
                            have p1362_3 := h1362c.2.2.2
                            rcases p1362_3 (m.d 0 4) (by simp) with h1367 | h1367
                            · rcases p1362_3 (m.d 1 4) (by simp) with h1368 | h1368
                              · linarith only [h1368, h2, hlam]
                              · linarith only [h1358, h1368, hlam]
                            · linarith only [h1367, hlam, p1362_0]
                          · have p1362_0 := h1362c.1
                            have p1362_1 := h1362c.2.1
                            have p1362_2 := h1362c.2.2.1
                            have p1362_3 := h1362c.2.2.2
                            linarith only [h2, hlam, p1362_1]
                          · have p1362_0 := h1362c.1
                            have p1362_1 := h1362c.2.1
                            have p1362_2 := h1362c.2.2.1
                            have p1362_3 := h1362c.2.2.2
                            linarith only [hlam, p1362_0]
                          · have p1362_0 := h1362c.1
                            have p1362_1 := h1362c.2.1
                            have p1362_2 := h1362c.2.2.1
                            have p1362_3 := h1362c.2.2.2
                            linarith only [h1283, hlam, p1362_0]
                          · have p1362_0 := h1362c.1
                            have p1362_1 := h1362c.2.1
                            have p1362_2 := h1362c.2.2.1
                            have p1362_3 := h1362c.2.2.2
                            linarith only [h1287, hlam, p1362_1]
                          · have p1362_0 := h1362c.1
                            have p1362_1 := h1362c.2.1
                            have p1362_2 := h1362c.2.2.1
                            have p1362_3 := h1362c.2.2.2
                            linarith only [h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p1362_1, u1elo0]
                          · have p1362_0 := h1362c.1
                            have p1362_1 := h1362c.2.1
                            have p1362_2 := h1362c.2.2.1
                            have p1362_3 := h1362c.2.2.2
                            linarith only [h1359, hc23, hlam, hphi, ht01, ht12, p1362_1, u0ehi8]
                          · have p1362_0 := h1362c.1
                            have p1362_1 := h1362c.2.1
                            have p1362_2 := h1362c.2.2.1
                            have p1362_3 := h1362c.2.2.2
                            rcases p1362_3 (m.d 0 4) (by simp) with h1378 | h1378
                            · linarith only [h1378, h921, hlam]
                            · linarith only [h1378, h2, hlam]
                          · have p1362_0 := h1362c.1
                            have p1362_1 := h1362c.2.1
                            have p1362_2 := h1362c.2.2.1
                            have p1362_3 := h1362c.2.2.2
                            linarith only [hlam, p1362_0]
                          · have p1362_0 := h1362c.1
                            have p1362_1 := h1362c.2.1
                            have p1362_2 := h1362c.2.2.1
                            have p1362_3 := h1362c.2.2.2
                            rcases p1362_3 (m.d 0 4) (by simp) with h1382 | h1382
                            · linarith only [h1382, h921, hlam]
                            · linarith only [h1281, h1382, hlam]
                          · have p1362_0 := h1362c.1
                            have p1362_1 := h1362c.2.1
                            have p1362_2 := h1362c.2.2.1
                            have p1362_3 := h1362c.2.2.2
                            rcases p1362_3 (m.d 0 4) (by simp) with h1385 | h1385
                            · linarith only [h1385, h921, hlam]
                            · linarith only [h1282, h1385, hlam]
                          · have p1362_0 := h1362c.1
                            have p1362_1 := h1362c.2.1
                            have p1362_2 := h1362c.2.2.1
                            have p1362_3 := h1362c.2.2.2
                            linarith only [h1281, hlam, p1362_1]
                          · have p1362_0 := h1362c.1
                            have p1362_1 := h1362c.2.1
                            have p1362_2 := h1362c.2.2.1
                            have p1362_3 := h1362c.2.2.2
                            linarith only [h1, h1281, h1285, h1358, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1362_1, u1elo0]
                          · have p1362_0 := h1362c.1
                            have p1362_1 := h1362c.2.1
                            have p1362_2 := h1362c.2.2.1
                            have p1362_3 := h1362c.2.2.2
                            linarith only [h1359, hlam, p1362_0]
                          · have p1362_0 := h1362c.1
                            have p1362_1 := h1362c.2.1
                            have p1362_2 := h1362c.2.2.1
                            have p1362_3 := h1362c.2.2.2
                            linarith only [hlam, p1362_0]
                          · have p1362_0 := h1362c.1
                            have p1362_1 := h1362c.2.1
                            have p1362_2 := h1362c.2.2.1
                            have p1362_3 := h1362c.2.2.2
                            linarith only [h1, h1281, hc45, hlam, hphi, ht01, ht0b, ht5b, p1362_1, u1elo0]
                          · have p1362_0 := h1362c.1
                            have p1362_1 := h1362c.2.1
                            have p1362_2 := h1362c.2.2.1
                            have p1362_3 := h1362c.2.2.2
                            linarith only [h1282, hlam, p1362_0]
                          · have p1362_0 := h1362c.1
                            have p1362_1 := h1362c.2.1
                            have p1362_2 := h1362c.2.2.1
                            have p1362_3 := h1362c.2.2.2
                            linarith only [h1358, hlam, p1362_0]
                          · have p1362_0 := h1362c.1
                            have p1362_1 := h1362c.2.1
                            have p1362_2 := h1362c.2.2.1
                            have p1362_3 := h1362c.2.2.2
                            linarith only [h1360, hlam, p1362_0]
                          · have p1362_0 := h1362c.1
                            have p1362_1 := h1362c.2.1
                            have p1362_2 := h1362c.2.2.1
                            have p1362_3 := h1362c.2.2.2
                            linarith only [h1361, hlam, p1362_0]
                          · have p1362_0 := h1362c.1
                            have p1362_1 := h1362c.2.1
                            have p1362_2 := h1362c.2.2.1
                            have p1362_3 := h1362c.2.2.2
                            linarith only [hlam, p1362_0]
                        · linarith only [h1358, h1361, h2, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · linarith only [h1, h1281, h1287, h1358, h1360, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · linarith only [h1, h1281, h1359, h3, hlam, hphi, ht01, u0ehi6, u1elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1401 | h1401
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1402 | h1402
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1403 | h1403
                        · linarith only [h1, h1281, h1358, h1403, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · linarith only [h1, h1281, h1282, h1287, h1403, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · linarith only [h1, h1281, h1282, h1402, h921, hlam, hphi, ht01, u0ehi6, u1elo0]
                    · linarith only [h1401, h3, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1408 | h1408
          · linarith only [h1408, h921, hlam, hphi, ht01, u0ehi6, u1elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1410 | h1410
            · linarith only [h1196, h1410, hlam, hphi, ht01, u0ehi6, u1elo1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1412 | h1412
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1413 | h1413
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1414 | h1414
                  · linarith only [h1, h1282, h1412, h1414, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1416 | h1416
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1417 | h1417
                      · linarith only [h1282, h1416, h1417, h921, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                      · linarith only [h1417, h921, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                    · linarith only [h1, h1412, h1416, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1421 | h1421
                  · linarith only [h1282, h1421, h921, hlam, hphi, ht01, u0ehi6, u1elo3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1423 | h1423
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1424 | h1424
                      · linarith only [h1282, h1423, h1424, h921, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                      · linarith only [h1424, h921, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                    · linarith only [h1, h1412, h1423, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1428 | h1428
                · linarith only [h1, h1281, h1412, h1428, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1430 | h1430
                  · linarith only [h1, h1281, h1282, h1412, h1430, h921, hlam, hphi, ht01, u0ehi6, u1elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1432 | h1432
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1433 | h1433
                      · linarith only [h1282, h1432, h1433, h921, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                      · linarith only [h1433, h921, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                    · linarith only [h1, h1281, h1432, h3, hlam, hphi, ht01, u0ehi6, u1elo0]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1437 | h1437
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1438 | h1438
          · linarith only [h1438, h921, hlam, hphi, ht01, u0ehi6, u1elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1440 | h1440
            · linarith only [h1196, h1440, hlam, hphi, ht01, u0ehi6, u1elo1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1442 | h1442
              · linarith only [h1281, h1442, hlam, hphi, ht01, u0ehi7, u1elo2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1444 | h1444
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1445 | h1445
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1446 | h1446
                    · linarith only [h1281, h1446, h3, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                    · linarith only [h1446, h3, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                  · linarith only [h1437, h1442, h1444, h1445, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1450 | h1450
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1451 | h1451
                    · linarith only [h1281, h1451, h3, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                    · linarith only [h1451, h3, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1454 | h1454
                    · linarith only [h1281, h1454, h3, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                    · linarith only [h1437, h1438, h1450, h1454, h2, h3, hc12, hc34, hlam, hphi, ht01, ht23, u0ehi6, u1elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1457 | h1457
          · linarith only [h1457, h921, hlam, hphi, ht01, u0ehi6, u1elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1459 | h1459
            · linarith only [h1196, h1457, h1459, h2, hlam, hphi, ht01, u0ehi6, u1elo0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1461 | h1461
              · linarith only [h1, h1281, h1461, h3, hlam, hphi, ht01, u0ehi6, u1elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1463 | h1463
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1464 | h1464
                  · linarith only [h1437, h1464, h2, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h1461, h1463, h1464, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1467 | h1467
                  · linarith only [h1281, h1437, h1467, h2, h3, hlam, hphi, ht01, u0ehi6, u1elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1469 | h1469
                    · linarith only [h1281, h1469, h3, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                    · linarith only [h1469, h3, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]

theorem r1l7_20_11_14_M_LR_L_0_L_I_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
  · exact r1l7_20_11_14_M_LR_L_0_L_I_x0_x0_x0_x0 m hb0 hb1 hb4 h0 h1 h2 h3
  · exact r1l7_20_11_14_M_LR_L_0_L_I_x0_x0_x0_x1 m hb0 hb1 hb4 h0 h1 h2 h3

theorem r1l7_20_11_14_M_LR_L_0_L_I_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  linarith only [h2, hlam, hphi, ht01, u0ehi5, u1elo3]

end R2N4
