import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_59S8

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3542000 in
set_option maxHeartbeats 3542000 in
theorem r1l7_20_11_14_M_LR_L_I_L_I_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
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
  rcases m.htr 0 1 4 (by decide) (by decide) with h660 | h660
  · rcases m.htr 0 2 3 (by decide) (by decide) with h661 | h661
    · linarith only [h0, h1, h661, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h663 | h663
      · rcases m.htr 0 3 4 (by decide) (by decide) with h664 | h664
        · rcases m.htr 0 4 5 (by decide) (by decide) with h665 | h665
          · rcases m.htr 1 2 3 (by decide) (by decide) with h666 | h666
            · linarith only [h661, h663, h665, h666, hc12, hlam, hphi, ht01, u0ehi9]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h668 | h668
              · rcases m.htr 1 3 4 (by decide) (by decide) with h669 | h669
                · rcases m.htr 1 4 5 (by decide) (by decide) with h670 | h670
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h671 | h671
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h672 | h672
                      · linarith only [h0, h668, h672, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h0, h1, h666, h668, h670, h671, h672, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h1, h666, h671, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h676 | h676
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h677 | h677
                      · linarith only [h0, h1, h663, h666, h670, h677, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h679 | h679
                        · linarith only [h668, h670, h676, h679, hlam]
                        · rcases h4bigk with h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c
                          · have p681_0 := h681c.1
                            have p681_1 := h681c.2.1
                            have p681_2 := h681c.2.2.1
                            have p681_3 := h681c.2.2.2
                            linarith only [hlam, p681_0]
                          · have p681_0 := h681c.1
                            have p681_1 := h681c.2.1
                            have p681_2 := h681c.2.2.1
                            have p681_3 := h681c.2.2.2
                            rcases p681_3 (m.d 0 4) (by simp) with h683 | h683
                            · rcases p681_3 (m.d 1 4) (by simp) with h684 | h684
                              · linarith only [h660, h684, hlam]
                              · rcases p681_3 (m.d 2 4) (by simp) with h686 | h686
                                · linarith only [h663, h686, hlam]
                                · rcases p681_3 (m.d 3 4) (by simp) with h688 | h688
                                  · linarith only [h664, h688, hlam]
                                  · rcases p681_3 (m.d 4 5) (by simp) with h690 | h690
                                    · linarith only [h665, h690, hlam]
                                    · linarith only [h670, h690, hlam]
                            · linarith only [h660, h683, hlam]
                          · have p681_0 := h681c.1
                            have p681_1 := h681c.2.1
                            have p681_2 := h681c.2.2.1
                            have p681_3 := h681c.2.2.2
                            rcases p681_3 (m.d 0 4) (by simp) with h694 | h694
                            · rcases p681_3 (m.d 1 4) (by simp) with h695 | h695
                              · linarith only [h660, h695, hlam]
                              · linarith only [h668, h695, hlam]
                            · linarith only [h663, h694, hlam]
                          · have p681_0 := h681c.1
                            have p681_1 := h681c.2.1
                            have p681_2 := h681c.2.2.1
                            have p681_3 := h681c.2.2.2
                            rcases p681_3 (m.d 0 4) (by simp) with h699 | h699
                            · rcases p681_3 (m.d 1 4) (by simp) with h700 | h700
                              · linarith only [h660, h700, hlam]
                              · linarith only [h669, h700, hlam]
                            · linarith only [h664, h699, hlam]
                          · have p681_0 := h681c.1
                            have p681_1 := h681c.2.1
                            have p681_2 := h681c.2.2.1
                            have p681_3 := h681c.2.2.2
                            linarith only [h0, h1, h663, h666, h668, h670, h676, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p681_1]
                          · have p681_0 := h681c.1
                            have p681_1 := h681c.2.1
                            have p681_2 := h681c.2.2.1
                            have p681_3 := h681c.2.2.2
                            linarith only [h660, hlam, p681_1]
                          · have p681_0 := h681c.1
                            have p681_1 := h681c.2.1
                            have p681_2 := h681c.2.2.1
                            have p681_3 := h681c.2.2.2
                            linarith only [hlam, p681_0]
                          · have p681_0 := h681c.1
                            have p681_1 := h681c.2.1
                            have p681_2 := h681c.2.2.1
                            have p681_3 := h681c.2.2.2
                            linarith only [h670, h676, hc34, hc45, hlam, hphi, p681_1]
                          · have p681_0 := h681c.1
                            have p681_1 := h681c.2.1
                            have p681_2 := h681c.2.2.1
                            have p681_3 := h681c.2.2.2
                            linarith only [h0, h1, h666, h668, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p681_1]
                          · have p681_0 := h681c.1
                            have p681_1 := h681c.2.1
                            have p681_2 := h681c.2.2.1
                            have p681_3 := h681c.2.2.2
                            linarith only [h670, hlam, p681_0]
                          · have p681_0 := h681c.1
                            have p681_1 := h681c.2.1
                            have p681_2 := h681c.2.2.1
                            have p681_3 := h681c.2.2.2
                            linarith only [h663, hlam, p681_1]
                          · have p681_0 := h681c.1
                            have p681_1 := h681c.2.1
                            have p681_2 := h681c.2.2.1
                            have p681_3 := h681c.2.2.2
                            linarith only [h668, hlam, p681_1]
                          · have p681_0 := h681c.1
                            have p681_1 := h681c.2.1
                            have p681_2 := h681c.2.2.1
                            have p681_3 := h681c.2.2.2
                            linarith only [hlam, p681_0]
                          · have p681_0 := h681c.1
                            have p681_1 := h681c.2.1
                            have p681_2 := h681c.2.2.1
                            have p681_3 := h681c.2.2.2
                            linarith only [h0, h1, h663, h666, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p681_1]
                          · have p681_0 := h681c.1
                            have p681_1 := h681c.2.1
                            have p681_2 := h681c.2.2.1
                            have p681_3 := h681c.2.2.2
                            linarith only [h677, hlam, p681_0]
                          · have p681_0 := h681c.1
                            have p681_1 := h681c.2.1
                            have p681_2 := h681c.2.2.1
                            have p681_3 := h681c.2.2.2
                            linarith only [h664, hlam, p681_1]
                          · have p681_0 := h681c.1
                            have p681_1 := h681c.2.1
                            have p681_2 := h681c.2.2.1
                            have p681_3 := h681c.2.2.2
                            linarith only [h669, hlam, p681_0]
                          · have p681_0 := h681c.1
                            have p681_1 := h681c.2.1
                            have p681_2 := h681c.2.2.1
                            have p681_3 := h681c.2.2.2
                            linarith only [h676, hlam, p681_0]
                          · have p681_0 := h681c.1
                            have p681_1 := h681c.2.1
                            have p681_2 := h681c.2.2.1
                            have p681_3 := h681c.2.2.2
                            linarith only [hlam, p681_0]
                          · have p681_0 := h681c.1
                            have p681_1 := h681c.2.1
                            have p681_2 := h681c.2.2.1
                            have p681_3 := h681c.2.2.2
                            linarith only [h679, hlam, p681_0]
                          · have p681_0 := h681c.1
                            have p681_1 := h681c.2.1
                            have p681_2 := h681c.2.2.1
                            have p681_3 := h681c.2.2.2
                            linarith only [h665, hlam, p681_0]
                          · have p681_0 := h681c.1
                            have p681_1 := h681c.2.1
                            have p681_2 := h681c.2.2.1
                            have p681_3 := h681c.2.2.2
                            linarith only [h0, h1, h663, h665, h666, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p681_1]
                          · have p681_0 := h681c.1
                            have p681_1 := h681c.2.1
                            have p681_2 := h681c.2.2.1
                            have p681_3 := h681c.2.2.2
                            linarith only [h0, h1, h663, h665, h666, h676, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p681_1]
                          · have p681_0 := h681c.1
                            have p681_1 := h681c.2.1
                            have p681_2 := h681c.2.2.1
                            have p681_3 := h681c.2.2.2
                            linarith only [h0, h1, h663, h665, h666, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p681_1]
                          · have p681_0 := h681c.1
                            have p681_1 := h681c.2.1
                            have p681_2 := h681c.2.2.1
                            have p681_3 := h681c.2.2.2
                            linarith only [hlam, p681_0]
                    · linarith only [h0, h1, h666, h676, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h1, h664, h669, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
              · linarith only [h0, h1, h663, h666, h668, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h728 | h728
            · linarith only [h661, h728, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h730 | h730
              · rcases m.htr 1 3 4 (by decide) (by decide) with h731 | h731
                · rcases m.htr 1 4 5 (by decide) (by decide) with h732 | h732
                  · linarith only [h665, h732, hc14, hlam, hphi, ht01, u0ehi8]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h734 | h734
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h735 | h735
                      · linarith only [h0, h1, h665, h728, h730, h735, hc23, hlam, hphi, ht01, ht12, u0ehi8]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h737 | h737
                        · linarith only [h0, h1, h665, h728, h730, h734, h737, hc23, hlam, hphi, ht01, ht12, u0ehi8]
                        · rcases h4bigk with h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c
                          · have p739_0 := h739c.1
                            have p739_1 := h739c.2.1
                            have p739_2 := h739c.2.2.1
                            have p739_3 := h739c.2.2.2
                            linarith only [hlam, p739_0]
                          · have p739_0 := h739c.1
                            have p739_1 := h739c.2.1
                            have p739_2 := h739c.2.2.1
                            have p739_3 := h739c.2.2.2
                            linarith only [h665, hc14, hc45, hlam, hphi, p739_1]
                          · have p739_0 := h739c.1
                            have p739_1 := h739c.2.1
                            have p739_2 := h739c.2.2.1
                            have p739_3 := h739c.2.2.2
                            linarith only [h665, hc24, hc45, hlam, hphi, p739_1]
                          · have p739_0 := h739c.1
                            have p739_1 := h739c.2.1
                            have p739_2 := h739c.2.2.1
                            have p739_3 := h739c.2.2.2
                            linarith only [h665, hc34, hc45, hlam, hphi, p739_1]
                          · have p739_0 := h739c.1
                            have p739_1 := h739c.2.1
                            have p739_2 := h739c.2.2.1
                            have p739_3 := h739c.2.2.2
                            linarith only [h665, hlam, p739_0]
                          · have p739_0 := h739c.1
                            have p739_1 := h739c.2.1
                            have p739_2 := h739c.2.2.1
                            have p739_3 := h739c.2.2.2
                            linarith only [h660, hlam, p739_1]
                          · have p739_0 := h739c.1
                            have p739_1 := h739c.2.1
                            have p739_2 := h739c.2.2.1
                            have p739_3 := h739c.2.2.2
                            linarith only [hlam, p739_0]
                          · have p739_0 := h739c.1
                            have p739_1 := h739c.2.1
                            have p739_2 := h739c.2.2.1
                            have p739_3 := h739c.2.2.2
                            linarith only [h1, h660, h728, h734, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p739_1]
                          · have p739_0 := h739c.1
                            have p739_1 := h739c.2.1
                            have p739_2 := h739c.2.2.1
                            have p739_3 := h739c.2.2.2
                            linarith only [h0, h1, h728, h730, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p739_1]
                          · have p739_0 := h739c.1
                            have p739_1 := h739c.2.1
                            have p739_2 := h739c.2.2.1
                            have p739_3 := h739c.2.2.2
                            linarith only [h732, hlam, p739_0]
                          · have p739_0 := h739c.1
                            have p739_1 := h739c.2.1
                            have p739_2 := h739c.2.2.1
                            have p739_3 := h739c.2.2.2
                            linarith only [h663, hlam, p739_1]
                          · have p739_0 := h739c.1
                            have p739_1 := h739c.2.1
                            have p739_2 := h739c.2.2.1
                            have p739_3 := h739c.2.2.2
                            linarith only [h730, hlam, p739_1]
                          · have p739_0 := h739c.1
                            have p739_1 := h739c.2.1
                            have p739_2 := h739c.2.2.1
                            have p739_3 := h739c.2.2.2
                            linarith only [hlam, p739_0]
                          · have p739_0 := h739c.1
                            have p739_1 := h739c.2.1
                            have p739_2 := h739c.2.2.1
                            have p739_3 := h739c.2.2.2
                            linarith only [h663, hc34, hlam, hphi, ht0b, ht45, ht5b, p739_1, u0elo1]
                          · have p739_0 := h739c.1
                            have p739_1 := h739c.2.1
                            have p739_2 := h739c.2.2.1
                            have p739_3 := h739c.2.2.2
                            linarith only [h735, hlam, p739_0]
                          · have p739_0 := h739c.1
                            have p739_1 := h739c.2.1
                            have p739_2 := h739c.2.2.1
                            have p739_3 := h739c.2.2.2
                            linarith only [h664, hlam, p739_1]
                          · have p739_0 := h739c.1
                            have p739_1 := h739c.2.1
                            have p739_2 := h739c.2.2.1
                            have p739_3 := h739c.2.2.2
                            linarith only [h731, hlam, p739_0]
                          · have p739_0 := h739c.1
                            have p739_1 := h739c.2.1
                            have p739_2 := h739c.2.2.1
                            have p739_3 := h739c.2.2.2
                            linarith only [h734, hlam, p739_0]
                          · have p739_0 := h739c.1
                            have p739_1 := h739c.2.1
                            have p739_2 := h739c.2.2.1
                            have p739_3 := h739c.2.2.2
                            linarith only [hlam, p739_0]
                          · have p739_0 := h739c.1
                            have p739_1 := h739c.2.1
                            have p739_2 := h739c.2.2.1
                            have p739_3 := h739c.2.2.2
                            linarith only [h737, hlam, p739_0]
                          · have p739_0 := h739c.1
                            have p739_1 := h739c.2.1
                            have p739_2 := h739c.2.2.1
                            have p739_3 := h739c.2.2.2
                            linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p739_1, u0ehi8]
                          · have p739_0 := h739c.1
                            have p739_1 := h739c.2.1
                            have p739_2 := h739c.2.2.1
                            have p739_3 := h739c.2.2.2
                            rcases p739_3 (m.d 0 4) (by simp) with h761 | h761
                            · linarith only [h665, h761, hlam]
                            · linarith only [h660, h761, hlam]
                          · have p739_0 := h739c.1
                            have p739_1 := h739c.2.1
                            have p739_2 := h739c.2.2.1
                            have p739_3 := h739c.2.2.2
                            rcases p739_3 (m.d 0 4) (by simp) with h764 | h764
                            · linarith only [h665, h764, hlam]
                            · linarith only [h663, h764, hlam]
                          · have p739_0 := h739c.1
                            have p739_1 := h739c.2.1
                            have p739_2 := h739c.2.2.1
                            have p739_3 := h739c.2.2.2
                            rcases p739_3 (m.d 0 4) (by simp) with h767 | h767
                            · linarith only [h665, h767, hlam]
                            · linarith only [h664, h767, hlam]
                          · have p739_0 := h739c.1
                            have p739_1 := h739c.2.1
                            have p739_2 := h739c.2.2.1
                            have p739_3 := h739c.2.2.2
                            linarith only [hlam, p739_0]
                    · linarith only [h0, h1, h728, h734, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h0, h1, h664, h730, h731, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
              · linarith only [h0, h1, h663, h728, h730, hc12, hc23, hlam, hphi]
        · linarith only [h1, h660, h664, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h775 | h775
        · rcases m.htr 0 4 5 (by decide) (by decide) with h776 | h776
          · rcases m.htr 1 2 3 (by decide) (by decide) with h777 | h777
            · linarith only [h0, h661, h777, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h779 | h779
              · linarith only [h0, h1, h663, h777, h779, hc23, hlam, hphi, ht01, ht12, u0ehi6]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h781 | h781
                · rcases m.htr 1 4 5 (by decide) (by decide) with h782 | h782
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h783 | h783
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h784 | h784
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h785 | h785
                        · rcases h4bigk with h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c
                          · have p786_0 := h786c.1
                            have p786_1 := h786c.2.1
                            have p786_2 := h786c.2.2.1
                            have p786_3 := h786c.2.2.2
                            linarith only [hlam, p786_0]
                          · have p786_0 := h786c.1
                            have p786_1 := h786c.2.1
                            have p786_2 := h786c.2.2.1
                            have p786_3 := h786c.2.2.2
                            linarith only [h1, h660, h777, h779, hc12, hc23, hlam, hphi, p786_1]
                          · have p786_0 := h786c.1
                            have p786_1 := h786c.2.1
                            have p786_2 := h786c.2.2.1
                            have p786_3 := h786c.2.2.2
                            linarith only [h663, hlam, p786_0]
                          · have p786_0 := h786c.1
                            have p786_1 := h786c.2.1
                            have p786_2 := h786c.2.2.1
                            have p786_3 := h786c.2.2.2
                            linarith only [h1, h660, h777, h785, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p786_1]
                          · have p786_0 := h786c.1
                            have p786_1 := h786c.2.1
                            have p786_2 := h786c.2.2.1
                            have p786_3 := h786c.2.2.2
                            rcases p786_3 (m.d 0 4) (by simp) with h791 | h791
                            · rcases p786_3 (m.d 1 4) (by simp) with h792 | h792
                              · linarith only [h660, h792, hlam]
                              · linarith only [h782, h792, hlam]
                            · linarith only [h791, hlam, p786_0]
                          · have p786_0 := h786c.1
                            have p786_1 := h786c.2.1
                            have p786_2 := h786c.2.2.1
                            have p786_3 := h786c.2.2.2
                            linarith only [h660, hlam, p786_1]
                          · have p786_0 := h786c.1
                            have p786_1 := h786c.2.1
                            have p786_2 := h786c.2.2.1
                            have p786_3 := h786c.2.2.2
                            linarith only [hlam, p786_0]
                          · have p786_0 := h786c.1
                            have p786_1 := h786c.2.1
                            have p786_2 := h786c.2.2.1
                            have p786_3 := h786c.2.2.2
                            linarith only [h779, hlam, p786_0]
                          · have p786_0 := h786c.1
                            have p786_1 := h786c.2.1
                            have p786_2 := h786c.2.2.1
                            have p786_3 := h786c.2.2.2
                            linarith only [h1, h660, h777, h785, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p786_1]
                          · have p786_0 := h786c.1
                            have p786_1 := h786c.2.1
                            have p786_2 := h786c.2.2.1
                            have p786_3 := h786c.2.2.2
                            linarith only [h1, h660, h777, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p786_1]
                          · have p786_0 := h786c.1
                            have p786_1 := h786c.2.1
                            have p786_2 := h786c.2.2.1
                            have p786_3 := h786c.2.2.2
                            linarith only [hc24, hlam, hphi, ht01, ht12, p786_1, u0ehi8]
                          · have p786_0 := h786c.1
                            have p786_1 := h786c.2.1
                            have p786_2 := h786c.2.2.1
                            have p786_3 := h786c.2.2.2
                            rcases p786_3 (m.d 0 4) (by simp) with h802 | h802
                            · linarith only [h663, h802, hlam]
                            · linarith only [h660, h802, hlam]
                          · have p786_0 := h786c.1
                            have p786_1 := h786c.2.1
                            have p786_2 := h786c.2.2.1
                            have p786_3 := h786c.2.2.2
                            linarith only [hlam, p786_0]
                          · have p786_0 := h786c.1
                            have p786_1 := h786c.2.1
                            have p786_2 := h786c.2.2.1
                            have p786_3 := h786c.2.2.2
                            rcases p786_3 (m.d 0 4) (by simp) with h806 | h806
                            · linarith only [h663, h806, hlam]
                            · linarith only [h775, h806, hlam]
                          · have p786_0 := h786c.1
                            have p786_1 := h786c.2.1
                            have p786_2 := h786c.2.2.1
                            have p786_3 := h786c.2.2.2
                            rcases p786_3 (m.d 0 4) (by simp) with h809 | h809
                            · linarith only [h663, h809, hlam]
                            · linarith only [h776, h809, hlam]
                          · have p786_0 := h786c.1
                            have p786_1 := h786c.2.1
                            have p786_2 := h786c.2.2.1
                            have p786_3 := h786c.2.2.2
                            linarith only [h775, hlam, p786_1]
                          · have p786_0 := h786c.1
                            have p786_1 := h786c.2.1
                            have p786_2 := h786c.2.2.1
                            have p786_3 := h786c.2.2.2
                            linarith only [h781, hlam, p786_0]
                          · have p786_0 := h786c.1
                            have p786_1 := h786c.2.1
                            have p786_2 := h786c.2.2.1
                            have p786_3 := h786c.2.2.2
                            linarith only [h783, hlam, p786_0]
                          · have p786_0 := h786c.1
                            have p786_1 := h786c.2.1
                            have p786_2 := h786c.2.2.1
                            have p786_3 := h786c.2.2.2
                            linarith only [hlam, p786_0]
                          · have p786_0 := h786c.1
                            have p786_1 := h786c.2.1
                            have p786_2 := h786c.2.2.1
                            have p786_3 := h786c.2.2.2
                            linarith only [h775, hc45, hlam, hphi, ht0b, ht5b, p786_1, u0elo2]
                          · have p786_0 := h786c.1
                            have p786_1 := h786c.2.1
                            have p786_2 := h786c.2.2.1
                            have p786_3 := h786c.2.2.2
                            linarith only [h776, hlam, p786_0]
                          · have p786_0 := h786c.1
                            have p786_1 := h786c.2.1
                            have p786_2 := h786c.2.2.1
                            have p786_3 := h786c.2.2.2
                            linarith only [h782, hlam, p786_0]
                          · have p786_0 := h786c.1
                            have p786_1 := h786c.2.1
                            have p786_2 := h786c.2.2.1
                            have p786_3 := h786c.2.2.2
                            linarith only [h784, hlam, p786_0]
                          · have p786_0 := h786c.1
                            have p786_1 := h786c.2.1
                            have p786_2 := h786c.2.2.1
                            have p786_3 := h786c.2.2.2
                            linarith only [h785, hlam, p786_0]
                          · have p786_0 := h786c.1
                            have p786_1 := h786c.2.1
                            have p786_2 := h786c.2.2.1
                            have p786_3 := h786c.2.2.2
                            linarith only [hlam, p786_0]
                        · linarith only [h1, h660, h777, h782, h785, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h1, h660, h777, h782, h784, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h1, h660, h777, h782, h783, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                  · linarith only [h1, h660, h776, h777, h779, h782, hc12, hc23, hlam, hphi]
                · linarith only [h1, h781, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h827 | h827
            · linarith only [h661, h827, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h829 | h829
              · linarith only [h0, h663, h829, hlam, hphi, u0ehi6, u0elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h831 | h831
                · rcases m.htr 1 4 5 (by decide) (by decide) with h832 | h832
                  · linarith only [h1, h660, h663, h776, h827, h832, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h834 | h834
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h835 | h835
                      · linarith only [h663, h776, h835, hc24, hlam, hphi, ht01, ht12, u0ehi6]
                      · linarith only [h663, h835, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                    · linarith only [h1, h660, h827, h831, h834, hlam]
                · linarith only [h1, h660, h829, h831, hc12, hc34, hlam, hphi, ht23]
        · linarith only [h1, h660, h775, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h841 | h841
    · linarith only [h0, h1, h841, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h843 | h843
      · linarith only [h0, h660, h843, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h845 | h845
        · rcases m.htr 0 4 5 (by decide) (by decide) with h846 | h846
          · rcases m.htr 1 2 3 (by decide) (by decide) with h847 | h847
            · linarith only [h841, h847, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h849 | h849
              · linarith only [h0, h843, h849, hlam, hphi, u0ehi6, u0elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h851 | h851
                · rcases m.htr 1 4 5 (by decide) (by decide) with h852 | h852
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h853 | h853
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h854 | h854
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h855 | h855
                        · rcases h4bigk with h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [hlam, p856_0]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [h660, hlam, p856_0]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [h843, hlam, p856_0]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [h845, h855, hc45, hlam, hphi, ht0b, ht5b, p856_1, u0elo2]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            rcases p856_3 (m.d 0 4) (by simp) with h861 | h861
                            · rcases p856_3 (m.d 1 4) (by simp) with h862 | h862
                              · rcases p856_3 (m.d 2 4) (by simp) with h863 | h863
                                · rcases p856_3 (m.d 3 4) (by simp) with h864 | h864
                                  · linarith only [h845, h864, hlam]
                                  · linarith only [h855, h864, hlam]
                                · linarith only [h854, h863, hlam]
                              · linarith only [h852, h862, hlam]
                            · linarith only [h861, hlam, p856_0]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [h847, h851, hc23, hlam, hphi, ht01, ht12, p856_1, u0ehi8]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [hlam, p856_0]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [h849, hlam, p856_0]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            rcases p856_3 (m.d 0 4) (by simp) with h873 | h873
                            · linarith only [h660, h873, hlam]
                            · linarith only [h845, h873, hlam]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            rcases p856_3 (m.d 0 4) (by simp) with h876 | h876
                            · linarith only [h660, h876, hlam]
                            · linarith only [h846, h876, hlam]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [h0, h660, hc12, hc24, hlam, hphi, p856_1]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [h0, h660, hc24, hlam, hphi, ht01, ht12, p856_1, u0ehi6]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [hlam, p856_0]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            rcases p856_3 (m.d 0 4) (by simp) with h882 | h882
                            · linarith only [h843, h882, hlam]
                            · linarith only [h845, h882, hlam]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            rcases p856_3 (m.d 0 4) (by simp) with h885 | h885
                            · linarith only [h843, h885, hlam]
                            · linarith only [h846, h885, hlam]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [h845, hlam, p856_1]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [h851, hlam, p856_0]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [h853, hlam, p856_0]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [hlam, p856_0]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [h845, hc45, hlam, hphi, ht0b, ht5b, p856_1, u0elo2]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [h846, hlam, p856_0]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [h852, hlam, p856_0]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [h854, hlam, p856_0]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [h855, hlam, p856_0]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [hlam, p856_0]
                        · rcases h4bigk with h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [hlam, p898_0]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [h660, hlam, p898_0]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [h843, hlam, p898_0]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            rcases p898_3 (m.d 0 4) (by simp) with h902 | h902
                            · rcases p898_3 (m.d 1 4) (by simp) with h903 | h903
                              · rcases p898_3 (m.d 2 4) (by simp) with h904 | h904
                                · rcases p898_3 (m.d 3 4) (by simp) with h905 | h905
                                  · linarith only [h845, h905, hlam]
                                  · rcases p898_3 (m.d 4 5) (by simp) with h907 | h907
                                    · linarith only [h846, h907, hlam]
                                    · linarith only [h855, h907, hlam]
                                · linarith only [h853, h904, hlam]
                              · linarith only [h851, h903, hlam]
                            · linarith only [h845, h902, hlam]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [h855, hc34, hlam, hphi, ht0b, ht45, ht5b, p898_1, u0elo3]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [hc14, hlam, hphi, ht01, p898_1, u0ehi8]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [hlam, p898_0]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [h849, hlam, p898_0]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            rcases p898_3 (m.d 0 4) (by simp) with h917 | h917
                            · linarith only [h660, h917, hlam]
                            · linarith only [h845, h917, hlam]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            rcases p898_3 (m.d 0 4) (by simp) with h920 | h920
                            · linarith only [h660, h920, hlam]
                            · linarith only [h846, h920, hlam]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [h0, h660, h853, hc23, hlam, hphi, ht01, ht12, p898_1, u0ehi6]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [h0, h660, h853, hc23, hlam, hphi, ht01, ht12, p898_1, u0ehi6]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [hlam, p898_0]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            rcases p898_3 (m.d 0 4) (by simp) with h926 | h926
                            · linarith only [h843, h926, hlam]
                            · linarith only [h845, h926, hlam]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            rcases p898_3 (m.d 0 4) (by simp) with h929 | h929
                            · linarith only [h843, h929, hlam]
                            · linarith only [h846, h929, hlam]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [h845, hlam, p898_1]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [h851, hlam, p898_0]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [h853, hlam, p898_0]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [hlam, p898_0]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [h855, hlam, p898_0]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [h846, hlam, p898_0]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [h852, hlam, p898_0]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [h854, hlam, p898_0]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [h846, hc34, hlam, hphi, ht0b, ht45, ht5b, p898_1, u0elo3]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [hlam, p898_0]
                      · linarith only [h843, h845, h846, h854, hlam, hphi, u0ehi6, u0elo2]
                    · linarith only [h0, h1, h847, h853, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                  · linarith only [h0, h660, h845, h846, h852, hlam, hphi, u0ehi6, u0elo2]
                · linarith only [h0, h1, h845, h851, hlam, hphi, u0ehi6, u0elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h946 | h946
            · linarith only [h841, h946, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h948 | h948
              · linarith only [h0, h660, h846, h948, hc24, hc45, hlam, hphi]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h950 | h950
                · rcases m.htr 1 4 5 (by decide) (by decide) with h951 | h951
                  · linarith only [h0, h660, h846, h950, h951, hc13, hlam, hphi, ht01, u0ehi6]
                  · linarith only [h0, h660, h951, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                · linarith only [h0, h1, h845, h950, hlam, hphi, u0ehi6, u0elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h955 | h955
          · rcases m.htr 1 2 3 (by decide) (by decide) with h956 | h956
            · linarith only [h0, h841, h956, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h958 | h958
              · linarith only [h0, h1, h843, h845, h958, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h960 | h960
                · linarith only [h0, h1, h845, h956, h960, hc12, hc23, hlam, hphi]
                · linarith only [h0, h1, h960, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h963 | h963
            · linarith only [h0, h660, h955, h963, hc23, hc45, hlam, hphi, ht34]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h965 | h965
              · linarith only [h0, h1, h845, h955, h965, hc24, hc45, hlam, hphi]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h967 | h967
                · linarith only [h0, h1, h845, h963, h967, hc12, hc23, hlam, hphi]
                · linarith only [h0, h1, h967, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]

set_option maxHeartbeats 3542000 in
set_option maxHeartbeats 3542000 in
theorem r1l7_20_11_14_M_LR_L_I_L_I_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
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
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_20_11_14_M_LR_L_I_L_I_x0_x0 m hb0 hb1 hb4 h0 h1
  · exact r1l7_20_11_14_M_LR_L_I_L_I_x0_x1 m hb0 hb1 hb4 h0 h1

end R2N4
