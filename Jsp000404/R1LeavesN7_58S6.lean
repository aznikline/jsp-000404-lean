import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_58S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3690000 in
set_option maxHeartbeats 3690000 in
theorem r1l7_13_24_L_R_M_IR_x0_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc05 := m.hcor 0 5 (by decide)
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
  have h3ehi := hb3.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h728 | h728
  · rcases m.htr 0 2 4 (by decide) (by decide) with h729 | h729
    · rcases m.htr 0 3 4 (by decide) (by decide) with h730 | h730
      · rcases m.htr 0 3 5 (by decide) (by decide) with h731 | h731
        · rcases m.htr 0 4 5 (by decide) (by decide) with h732 | h732
          · rcases m.htr 1 2 3 (by decide) (by decide) with h733 | h733
            · linarith only [h0, h1, h733, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h735 | h735
              · linarith only [h0, h1, h733, h735, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
              · linarith only [h0, h1, h729, h733, h735, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h738 | h738
            · linarith only [h0, h1, h738, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h740 | h740
              · linarith only [h0, h1, h738, h740, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
              · linarith only [h0, h1, h729, h738, h740, hc12, hc23, hlam, hphi]
        · linarith only [h730, h731, hc35, hlam, hphi, u3ehi3]
      · linarith only [h1, h728, h730, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h745 | h745
      · rcases m.htr 0 3 5 (by decide) (by decide) with h746 | h746
        · rcases m.htr 0 4 5 (by decide) (by decide) with h747 | h747
          · rcases m.htr 1 2 3 (by decide) (by decide) with h748 | h748
            · linarith only [h0, h1, h748, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h750 | h750
              · linarith only [h0, h1, h729, h748, h750, hc02, hc23, hlam, hphi]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h752 | h752
                · rcases m.htr 1 4 5 (by decide) (by decide) with h753 | h753
                  · linarith only [h1, h728, h748, h753, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                  · linarith only [h1, h728, h747, h748, h753, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · linarith only [h1, h728, h747, h752, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h757 | h757
            · linarith only [h0, h1, h757, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h759 | h759
              · linarith only [h0, h729, h759, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h761 | h761
                · rcases m.htr 1 4 5 (by decide) (by decide) with h762 | h762
                  · linarith only [h728, h747, h762, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h764 | h764
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h765 | h765
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h766 | h766
                        · linarith only [h728, h747, h761, h766, hlam]
                        · rcases h4bigk with h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c
                          · have p768_0 := h768c.1
                            have p768_1 := h768c.2.1
                            have p768_2 := h768c.2.2.1
                            have p768_3 := h768c.2.2.2
                            linarith only [hlam, p768_0]
                          · have p768_0 := h768c.1
                            have p768_1 := h768c.2.1
                            have p768_2 := h768c.2.2.1
                            have p768_3 := h768c.2.2.2
                            linarith only [h747, h761, h765, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p768_1, u3ehi3]
                          · have p768_0 := h768c.1
                            have p768_1 := h768c.2.1
                            have p768_2 := h768c.2.2.1
                            have p768_3 := h768c.2.2.2
                            linarith only [h729, hlam, p768_0]
                          · have p768_0 := h768c.1
                            have p768_1 := h768c.2.1
                            have p768_2 := h768c.2.2.1
                            have p768_3 := h768c.2.2.2
                            linarith only [h747, h765, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p768_1, u3ehi3]
                          · have p768_0 := h768c.1
                            have p768_1 := h768c.2.1
                            have p768_2 := h768c.2.2.1
                            have p768_3 := h768c.2.2.2
                            linarith only [h747, hlam, p768_0]
                          · have p768_0 := h768c.1
                            have p768_1 := h768c.2.1
                            have p768_2 := h768c.2.2.1
                            have p768_3 := h768c.2.2.2
                            linarith only [h728, hlam, p768_1]
                          · have p768_0 := h768c.1
                            have p768_1 := h768c.2.1
                            have p768_2 := h768c.2.2.1
                            have p768_3 := h768c.2.2.2
                            linarith only [hlam, p768_0]
                          · have p768_0 := h768c.1
                            have p768_1 := h768c.2.1
                            have p768_2 := h768c.2.2.1
                            have p768_3 := h768c.2.2.2
                            linarith only [h759, hlam, p768_0]
                          · have p768_0 := h768c.1
                            have p768_1 := h768c.2.1
                            have p768_2 := h768c.2.2.1
                            have p768_3 := h768c.2.2.2
                            linarith only [h1, h728, h757, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p768_1, u3ehi3]
                          · have p768_0 := h768c.1
                            have p768_1 := h768c.2.1
                            have p768_2 := h768c.2.2.1
                            have p768_3 := h768c.2.2.2
                            linarith only [h762, hlam, p768_0]
                          · have p768_0 := h768c.1
                            have p768_1 := h768c.2.1
                            have p768_2 := h768c.2.2.1
                            have p768_3 := h768c.2.2.2
                            rcases p768_3 (m.d 0 4) (by simp) with h779 | h779
                            · linarith only [h729, h779, hlam]
                            · rcases p768_3 (m.d 1 4) (by simp) with h781 | h781
                              · linarith only [h759, h781, hlam]
                              · rcases p768_3 (m.d 2 4) (by simp) with h783 | h783
                                · rcases p768_3 (m.d 3 4) (by simp) with h784 | h784
                                  · linarith only [h764, h784, hlam]
                                  · rcases p768_3 (m.d 4 5) (by simp) with h786 | h786
                                    · linarith only [h765, h786, hlam]
                                    · linarith only [h747, h786, hlam]
                                · linarith only [h729, h783, hlam]
                          · have p768_0 := h768c.1
                            have p768_1 := h768c.2.1
                            have p768_2 := h768c.2.2.1
                            have p768_3 := h768c.2.2.2
                            rcases p768_3 (m.d 0 4) (by simp) with h790 | h790
                            · linarith only [h729, h790, hlam]
                            · linarith only [h728, h790, hlam]
                          · have p768_0 := h768c.1
                            have p768_1 := h768c.2.1
                            have p768_2 := h768c.2.2.1
                            have p768_3 := h768c.2.2.2
                            linarith only [hlam, p768_0]
                          · have p768_0 := h768c.1
                            have p768_1 := h768c.2.1
                            have p768_2 := h768c.2.2.1
                            have p768_3 := h768c.2.2.2
                            rcases p768_3 (m.d 0 4) (by simp) with h794 | h794
                            · linarith only [h729, h794, hlam]
                            · linarith only [h745, h794, hlam]
                          · have p768_0 := h768c.1
                            have p768_1 := h768c.2.1
                            have p768_2 := h768c.2.2.1
                            have p768_3 := h768c.2.2.2
                            linarith only [h729, h747, h764, hc02, hc23, hlam, hphi, p768_1]
                          · have p768_0 := h768c.1
                            have p768_1 := h768c.2.1
                            have p768_2 := h768c.2.2.1
                            have p768_3 := h768c.2.2.2
                            linarith only [h745, hlam, p768_1]
                          · have p768_0 := h768c.1
                            have p768_1 := h768c.2.1
                            have p768_2 := h768c.2.2.1
                            have p768_3 := h768c.2.2.2
                            linarith only [h761, hlam, p768_0]
                          · have p768_0 := h768c.1
                            have p768_1 := h768c.2.1
                            have p768_2 := h768c.2.2.1
                            have p768_3 := h768c.2.2.2
                            linarith only [h764, hlam, p768_0]
                          · have p768_0 := h768c.1
                            have p768_1 := h768c.2.1
                            have p768_2 := h768c.2.2.1
                            have p768_3 := h768c.2.2.2
                            linarith only [hlam, p768_0]
                          · have p768_0 := h768c.1
                            have p768_1 := h768c.2.1
                            have p768_2 := h768c.2.2.1
                            have p768_3 := h768c.2.2.2
                            linarith only [h766, hlam, p768_0]
                          · have p768_0 := h768c.1
                            have p768_1 := h768c.2.1
                            have p768_2 := h768c.2.2.1
                            have p768_3 := h768c.2.2.2
                            linarith only [h728, hc45, hlam, hphi, p768_1, u4ehi1]
                          · have p768_0 := h768c.1
                            have p768_1 := h768c.2.1
                            have p768_2 := h768c.2.2.1
                            have p768_3 := h768c.2.2.2
                            linarith only [h761, hc45, hlam, hphi, ht34, p768_1, u3ehi3]
                          · have p768_0 := h768c.1
                            have p768_1 := h768c.2.1
                            have p768_2 := h768c.2.2.1
                            have p768_3 := h768c.2.2.2
                            linarith only [h765, hlam, p768_0]
                          · have p768_0 := h768c.1
                            have p768_1 := h768c.2.1
                            have p768_2 := h768c.2.2.1
                            have p768_3 := h768c.2.2.2
                            linarith only [h764, h765, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p768_1, u3ehi3]
                          · have p768_0 := h768c.1
                            have p768_1 := h768c.2.1
                            have p768_2 := h768c.2.2.1
                            have p768_3 := h768c.2.2.2
                            linarith only [hlam, p768_0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h808 | h808
                        · linarith only [h1, h728, h757, h761, h765, h808, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                        · rcases h4bigk with h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [hlam, p810_0]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h1, h728, h757, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p810_1, u4ehi1]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h729, hlam, p810_0]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h729, h765, hc45, hlam, hphi, ht34, p810_1, u3ehi3]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h747, hlam, p810_0]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h728, hlam, p810_1]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [hlam, p810_0]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h759, hlam, p810_0]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h1, h728, h757, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p810_1, u3ehi3]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h762, hlam, p810_0]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h765, hc45, hlam, hphi, p810_1, u4ehi0]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h765, hc45, hlam, hphi, p810_1, u4ehi1]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [hlam, p810_0]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h765, hc45, hlam, hphi, ht34, p810_1, u3ehi3]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h765, hlam, p810_0]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h745, hlam, p810_1]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h761, hlam, p810_0]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h764, hlam, p810_0]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [hlam, p810_0]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h808, hlam, p810_0]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h728, h761, hc45, hlam, hphi, ht34, p810_1, u3ehi3]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [h761, hc45, hlam, hphi, ht34, p810_1, u3ehi3]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [hc45, hlam, hphi, p810_1, u4ehi2]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [hc45, hlam, hphi, ht34, p810_1, u3ehi3]
                          · have p810_0 := h810c.1
                            have p810_1 := h810c.2.1
                            have p810_2 := h810c.2.2.1
                            have p810_3 := h810c.2.2.2
                            linarith only [hlam, p810_0]
                    · linarith only [h0, h1, h757, h764, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h1, h728, h745, h761, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
        · linarith only [h745, h746, hc35, hlam, hphi, u3ehi3]
      · linarith only [h1, h728, h745, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h840 | h840
    · linarith only [h0, h728, h840, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h842 | h842
      · rcases m.htr 0 3 5 (by decide) (by decide) with h843 | h843
        · rcases m.htr 0 4 5 (by decide) (by decide) with h844 | h844
          · rcases m.htr 1 2 3 (by decide) (by decide) with h845 | h845
            · linarith only [h0, h1, h845, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h847 | h847
              · linarith only [h0, h1, h840, h845, h847, hc02, hc23, hlam, hphi]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h849 | h849
                · rcases m.htr 1 4 5 (by decide) (by decide) with h850 | h850
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h851 | h851
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h852 | h852
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h853 | h853
                        · rcases h4bigk with h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c
                          · have p854_0 := h854c.1
                            have p854_1 := h854c.2.1
                            have p854_2 := h854c.2.2.1
                            have p854_3 := h854c.2.2.2
                            linarith only [hlam, p854_0]
                          · have p854_0 := h854c.1
                            have p854_1 := h854c.2.1
                            have p854_2 := h854c.2.2.1
                            have p854_3 := h854c.2.2.2
                            linarith only [h728, hlam, p854_0]
                          · have p854_0 := h854c.1
                            have p854_1 := h854c.2.1
                            have p854_2 := h854c.2.2.1
                            have p854_3 := h854c.2.2.2
                            linarith only [h840, hlam, p854_0]
                          · have p854_0 := h854c.1
                            have p854_1 := h854c.2.1
                            have p854_2 := h854c.2.2.1
                            have p854_3 := h854c.2.2.2
                            linarith only [h853, hc04, hlam, hphi, ht0b, ht45, ht5b, p854_1, u4ehi4]
                          · have p854_0 := h854c.1
                            have p854_1 := h854c.2.1
                            have p854_2 := h854c.2.2.1
                            have p854_3 := h854c.2.2.2
                            rcases p854_3 (m.d 0 4) (by simp) with h859 | h859
                            · rcases p854_3 (m.d 1 4) (by simp) with h860 | h860
                              · rcases p854_3 (m.d 2 4) (by simp) with h861 | h861
                                · rcases p854_3 (m.d 3 4) (by simp) with h862 | h862
                                  · linarith only [h842, h862, hlam]
                                  · linarith only [h853, h862, hlam]
                                · linarith only [h852, h861, hlam]
                              · linarith only [h850, h860, hlam]
                            · linarith only [h859, hlam, p854_0]
                          · have p854_0 := h854c.1
                            have p854_1 := h854c.2.1
                            have p854_2 := h854c.2.2.1
                            have p854_3 := h854c.2.2.2
                            linarith only [h0, h728, h845, h849, hc12, hc23, hlam, hphi, p854_1]
                          · have p854_0 := h854c.1
                            have p854_1 := h854c.2.1
                            have p854_2 := h854c.2.2.1
                            have p854_3 := h854c.2.2.2
                            linarith only [hlam, p854_0]
                          · have p854_0 := h854c.1
                            have p854_1 := h854c.2.1
                            have p854_2 := h854c.2.2.1
                            have p854_3 := h854c.2.2.2
                            linarith only [h847, hlam, p854_0]
                          · have p854_0 := h854c.1
                            have p854_1 := h854c.2.1
                            have p854_2 := h854c.2.2.1
                            have p854_3 := h854c.2.2.2
                            linarith only [h845, h849, h853, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p854_1, u4ehi4]
                          · have p854_0 := h854c.1
                            have p854_1 := h854c.2.1
                            have p854_2 := h854c.2.2.1
                            have p854_3 := h854c.2.2.2
                            rcases p854_3 (m.d 0 4) (by simp) with h872 | h872
                            · linarith only [h728, h872, hlam]
                            · linarith only [h844, h872, hlam]
                          · have p854_0 := h854c.1
                            have p854_1 := h854c.2.1
                            have p854_2 := h854c.2.2.1
                            have p854_3 := h854c.2.2.2
                            linarith only [h842, h853, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p854_1, u4ehi4]
                          · have p854_0 := h854c.1
                            have p854_1 := h854c.2.1
                            have p854_2 := h854c.2.2.1
                            have p854_3 := h854c.2.2.2
                            linarith only [h0, h728, hc12, hc24, hlam, hphi, p854_1]
                          · have p854_0 := h854c.1
                            have p854_1 := h854c.2.1
                            have p854_2 := h854c.2.2.1
                            have p854_3 := h854c.2.2.2
                            linarith only [hlam, p854_0]
                          · have p854_0 := h854c.1
                            have p854_1 := h854c.2.1
                            have p854_2 := h854c.2.2.1
                            have p854_3 := h854c.2.2.2
                            linarith only [h851, h853, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p854_1, u4ehi4]
                          · have p854_0 := h854c.1
                            have p854_1 := h854c.2.1
                            have p854_2 := h854c.2.2.1
                            have p854_3 := h854c.2.2.2
                            rcases p854_3 (m.d 0 4) (by simp) with h879 | h879
                            · linarith only [h840, h879, hlam]
                            · linarith only [h844, h879, hlam]
                          · have p854_0 := h854c.1
                            have p854_1 := h854c.2.1
                            have p854_2 := h854c.2.2.1
                            have p854_3 := h854c.2.2.2
                            linarith only [h842, hlam, p854_1]
                          · have p854_0 := h854c.1
                            have p854_1 := h854c.2.1
                            have p854_2 := h854c.2.2.1
                            have p854_3 := h854c.2.2.2
                            linarith only [h849, hlam, p854_0]
                          · have p854_0 := h854c.1
                            have p854_1 := h854c.2.1
                            have p854_2 := h854c.2.2.1
                            have p854_3 := h854c.2.2.2
                            linarith only [h851, hlam, p854_0]
                          · have p854_0 := h854c.1
                            have p854_1 := h854c.2.1
                            have p854_2 := h854c.2.2.1
                            have p854_3 := h854c.2.2.2
                            linarith only [hlam, p854_0]
                          · have p854_0 := h854c.1
                            have p854_1 := h854c.2.1
                            have p854_2 := h854c.2.2.1
                            have p854_3 := h854c.2.2.2
                            linarith only [h1, h842, h845, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p854_1, u4ehi4]
                          · have p854_0 := h854c.1
                            have p854_1 := h854c.2.1
                            have p854_2 := h854c.2.2.1
                            have p854_3 := h854c.2.2.2
                            linarith only [h844, hlam, p854_0]
                          · have p854_0 := h854c.1
                            have p854_1 := h854c.2.1
                            have p854_2 := h854c.2.2.1
                            have p854_3 := h854c.2.2.2
                            linarith only [h850, hlam, p854_0]
                          · have p854_0 := h854c.1
                            have p854_1 := h854c.2.1
                            have p854_2 := h854c.2.2.1
                            have p854_3 := h854c.2.2.2
                            linarith only [h852, hlam, p854_0]
                          · have p854_0 := h854c.1
                            have p854_1 := h854c.2.1
                            have p854_2 := h854c.2.2.1
                            have p854_3 := h854c.2.2.2
                            linarith only [h853, hlam, p854_0]
                          · have p854_0 := h854c.1
                            have p854_1 := h854c.2.1
                            have p854_2 := h854c.2.2.1
                            have p854_3 := h854c.2.2.2
                            linarith only [hlam, p854_0]
                        · rcases h4bigk with h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [hlam, p892_0]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h728, hlam, p892_0]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h840, hlam, p892_0]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            rcases p892_3 (m.d 0 4) (by simp) with h896 | h896
                            · rcases p892_3 (m.d 1 4) (by simp) with h897 | h897
                              · rcases p892_3 (m.d 2 4) (by simp) with h898 | h898
                                · rcases p892_3 (m.d 3 4) (by simp) with h899 | h899
                                  · linarith only [h842, h899, hlam]
                                  · rcases p892_3 (m.d 4 5) (by simp) with h901 | h901
                                    · linarith only [h844, h901, hlam]
                                    · linarith only [h853, h901, hlam]
                                · linarith only [h851, h898, hlam]
                              · linarith only [h849, h897, hlam]
                            · linarith only [h842, h896, hlam]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h1, h842, h845, h853, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p892_1, u3ehi3]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h0, h728, h847, h851, hc12, hc23, hlam, hphi, p892_1]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [hlam, p892_0]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h847, hlam, p892_0]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            rcases p892_3 (m.d 0 4) (by simp) with h911 | h911
                            · linarith only [h728, h911, hlam]
                            · linarith only [h842, h911, hlam]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h847, h851, h853, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p892_1, u3ehi3]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h844, h851, h853, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p892_1, u3ehi3]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h0, h728, h851, hc12, hc23, hlam, hphi, p892_1]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [hlam, p892_0]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            rcases p892_3 (m.d 0 4) (by simp) with h918 | h918
                            · linarith only [h840, h918, hlam]
                            · linarith only [h842, h918, hlam]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h851, h853, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p892_1, u3ehi3]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h842, hlam, p892_1]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h849, hlam, p892_0]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h851, hlam, p892_0]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [hlam, p892_0]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h853, hlam, p892_0]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h844, hlam, p892_0]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h850, hlam, p892_0]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h852, hlam, p892_0]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [h844, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p892_1, u3ehi3]
                          · have p892_0 := h892c.1
                            have p892_1 := h892c.2.1
                            have p892_2 := h892c.2.2.1
                            have p892_3 := h892c.2.2.2
                            linarith only [hlam, p892_0]
                      · linarith only [h0, h1, h728, h842, h844, h845, h847, h852, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h845, h851, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h0, h728, h842, h844, h850, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h1, h842, h849, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h936 | h936
            · linarith only [h0, h728, h936, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h938 | h938
              · linarith only [h0, h728, h844, h938, hc45, hlam, hphi, u4ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h940 | h940
                · rcases m.htr 1 4 5 (by decide) (by decide) with h941 | h941
                  · linarith only [h0, h728, h844, h936, h940, h941, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h728, h941, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h0, h1, h842, h940, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · linarith only [h842, h843, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h946 | h946
        · linarith only [h842, h946, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h948 | h948
          · rcases m.htr 1 2 3 (by decide) (by decide) with h949 | h949
            · linarith only [h0, h1, h949, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h951 | h951
              · linarith only [h0, h1, h842, h951, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h953 | h953
                · linarith only [h0, h1, h842, h949, h953, hc12, hc23, hlam, hphi]
                · linarith only [h0, h1, h953, hc12, hc34, hlam, hphi, ht23]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h956 | h956
            · linarith only [h0, h1, h956, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h958 | h958
              · linarith only [h0, h1, h842, h948, h958, hc45, hlam, hphi, u4ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h960 | h960
                · linarith only [h0, h1, h842, h956, h960, hc12, hc23, hlam, hphi]
                · linarith only [h0, h1, h960, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 3690000 in
set_option maxHeartbeats 3690000 in
theorem r1l7_13_24_L_R_M_IR_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc05 := m.hcor 0 5 (by decide)
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
  have h3ehi := hb3.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_13_24_L_R_M_IR_x0_x0 m hb3 hb4 h0 h1
  · exact r1l7_13_24_L_R_M_IR_x0_x1 m hb3 hb4 h0 h1

set_option maxHeartbeats 3690000 in
set_option maxHeartbeats 3690000 in
theorem r1l7_13_24_L_R_M_IR_x1_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h963 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h3ehi := hb3.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h964 | h964
  · rcases m.htr 0 2 4 (by decide) (by decide) with h965 | h965
    · rcases m.htr 0 3 4 (by decide) (by decide) with h966 | h966
      · rcases m.htr 0 3 5 (by decide) (by decide) with h967 | h967
        · rcases m.htr 0 4 5 (by decide) (by decide) with h968 | h968
          · rcases m.htr 1 2 3 (by decide) (by decide) with h969 | h969
            · rcases m.htr 1 2 4 (by decide) (by decide) with h970 | h970
              · rcases m.htr 1 3 4 (by decide) (by decide) with h971 | h971
                · linarith only [h0, h963, h971, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h0, h963, h966, h971, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
              · linarith only [h0, h964, h970, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · linarith only [h0, h964, h969, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h976 | h976
            · rcases m.htr 1 2 4 (by decide) (by decide) with h977 | h977
              · rcases m.htr 1 3 4 (by decide) (by decide) with h978 | h978
                · linarith only [h0, h963, h978, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h0, h963, h966, h976, h978, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h964, h977, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · linarith only [h0, h963, h966, h976, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
        · linarith only [h966, h967, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h984 | h984
        · linarith only [h966, h984, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h986 | h986
          · rcases m.htr 1 2 3 (by decide) (by decide) with h987 | h987
            · rcases m.htr 1 2 4 (by decide) (by decide) with h988 | h988
              · rcases m.htr 1 3 4 (by decide) (by decide) with h989 | h989
                · linarith only [h0, h963, h966, h989, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h991 | h991
                  · linarith only [h0, h964, h991, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h0, h964, h986, h991, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
              · linarith only [h0, h963, h987, h988, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h0, h963, h987, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h996 | h996
            · rcases m.htr 1 2 4 (by decide) (by decide) with h997 | h997
              · rcases m.htr 1 3 4 (by decide) (by decide) with h998 | h998
                · linarith only [h963, h966, h998, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1000 | h1000
                  · linarith only [h1000, h964, h986, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1002 | h1002
                    · linarith only [h1002, h963, h966, h996, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1004 | h1004
                      · linarith only [h1004, h965, h986, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1006 | h1006
                        · linarith only [h1006, h964, h986, h996, h998, hc34, hlam, hphi, u3ehi2]
                        · linarith only [h1006, h963, h966, h996, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h0, h964, h997, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · linarith only [h0, h963, h996, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
    · linarith only [h0, h964, h965, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1012 | h1012
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1013 | h1013
      · linarith only [h1013, h963, h964, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1015 | h1015
        · linarith only [h1013, h1015, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1017 | h1017
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1018 | h1018
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1019 | h1019
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1020 | h1020
                · linarith only [h1013, h1020, h963, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                · linarith only [h1018, h1020, h963, h964, hc34, hlam, hphi, u3ehi2]
              · linarith only [h0, h1012, h1019, hlam]
            · linarith only [h0, h1018, h963, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · linarith only [h1017, h963, h964, hc45, hlam, hphi, ht34, u3ehi1]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1026 | h1026
      · linarith only [h0, h1012, h1026, h963, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1028 | h1028
        · linarith only [h1026, h1028, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1030 | h1030
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1031 | h1031
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1032 | h1032
              · linarith only [h0, h1012, h1031, h1032, h963, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h1031, h1032, h963, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h0, h1031, h963, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · linarith only [h0, h1012, h1030, h963, hc45, hlam, hphi, ht34, u3ehi1]

end R2N4
