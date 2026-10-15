import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_66S9
import Jsp000404.R1LeavesN7_66S10

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_14_M_LI_L_R_L_I_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h282 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2ehi := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h664 | h664
  · rcases m.htr 0 1 5 (by decide) (by decide) with h665 | h665
    · rcases m.htr 0 2 3 (by decide) (by decide) with h666 | h666
      · rcases m.htr 0 2 4 (by decide) (by decide) with h667 | h667
        · rcases m.htr 0 2 5 (by decide) (by decide) with h668 | h668
          · rcases m.htr 0 3 4 (by decide) (by decide) with h669 | h669
            · rcases m.htr 0 3 5 (by decide) (by decide) with h670 | h670
              · rcases m.htr 0 4 5 (by decide) (by decide) with h671 | h671
                · rcases m.htr 1 2 3 (by decide) (by decide) with h672 | h672
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h673 | h673
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h674 | h674
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h675 | h675
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h676 | h676
                          · linarith only [h666, h673, h676, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                          · linarith only [h666, h673, h675, h676, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h664, h671, h675, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi3]
                      · linarith only [h666, h670, h674, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                    · linarith only [h666, h669, h673, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                  · linarith only [h0, h666, h672, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h683 | h683
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h684 | h684
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h685 | h685
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h686 | h686
                        · linarith only [h667, h671, h686, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h688 | h688
                          · linarith only [h666, h667, h671, h684, h688, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                          · rcases h0bigk with h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c | h690c
                            · have p690_0 := h690c.1
                              have p690_1 := h690c.2.1
                              have p690_2 := h690c.2.2.1
                              have p690_3 := h690c.2.2.2
                              linarith only [hlam, p690_0]
                            · have p690_0 := h690c.1
                              have p690_1 := h690c.2.1
                              have p690_2 := h690c.2.2.1
                              have p690_3 := h690c.2.2.2
                              linarith only [h0, hlam, p690_1]
                            · have p690_0 := h690c.1
                              have p690_1 := h690c.2.1
                              have p690_2 := h690c.2.2.1
                              have p690_3 := h690c.2.2.2
                              linarith only [h282, hlam, p690_0]
                            · have p690_0 := h690c.1
                              have p690_1 := h690c.2.1
                              have p690_2 := h690c.2.2.1
                              have p690_3 := h690c.2.2.2
                              linarith only [h667, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p690_1, u0elo0, u2ehi3]
                            · have p690_0 := h690c.1
                              have p690_1 := h690c.2.1
                              have p690_2 := h690c.2.2.1
                              have p690_3 := h690c.2.2.2
                              linarith only [h282, h666, h667, h671, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p690_1, u0elo1, u2ehi3]
                            · have p690_0 := h690c.1
                              have p690_1 := h690c.2.1
                              have p690_2 := h690c.2.2.1
                              have p690_3 := h690c.2.2.2
                              linarith only [h665, hc15, hlam, hphi, ht0b, ht5b, p690_1, u0elo1]
                            · have p690_0 := h690c.1
                              have p690_1 := h690c.2.1
                              have p690_2 := h690c.2.2.1
                              have p690_3 := h690c.2.2.2
                              linarith only [hlam, p690_0]
                            · have p690_0 := h690c.1
                              have p690_1 := h690c.2.1
                              have p690_2 := h690c.2.2.1
                              have p690_3 := h690c.2.2.2
                              linarith only [h282, h665, hc15, hlam, hphi, ht0b, ht5b, p690_1, u0elo1]
                            · have p690_0 := h690c.1
                              have p690_1 := h690c.2.1
                              have p690_2 := h690c.2.2.1
                              have p690_3 := h690c.2.2.2
                              linarith only [h667, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p690_1, u0elo1, u2ehi3]
                            · have p690_0 := h690c.1
                              have p690_1 := h690c.2.1
                              have p690_2 := h690c.2.2.1
                              have p690_3 := h690c.2.2.2
                              linarith only [h667, h671, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p690_1, u0elo1, u2ehi3]
                            · have p690_0 := h690c.1
                              have p690_1 := h690c.2.1
                              have p690_2 := h690c.2.2.1
                              have p690_3 := h690c.2.2.2
                              linarith only [h665, h667, h671, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p690_1, u0elo2, u2ehi3]
                            · have p690_0 := h690c.1
                              have p690_1 := h690c.2.1
                              have p690_2 := h690c.2.2.1
                              have p690_3 := h690c.2.2.2
                              linarith only [h666, hlam, p690_1]
                            · have p690_0 := h690c.1
                              have p690_1 := h690c.2.1
                              have p690_2 := h690c.2.2.1
                              have p690_3 := h690c.2.2.2
                              linarith only [hlam, p690_0]
                            · have p690_0 := h690c.1
                              have p690_1 := h690c.2.1
                              have p690_2 := h690c.2.2.1
                              have p690_3 := h690c.2.2.2
                              linarith only [h666, h667, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p690_1, u0elo1, u2ehi3]
                            · have p690_0 := h690c.1
                              have p690_1 := h690c.2.1
                              have p690_2 := h690c.2.2.1
                              have p690_3 := h690c.2.2.2
                              linarith only [h666, h667, h671, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p690_1, u0elo1, u2ehi3]
                            · have p690_0 := h690c.1
                              have p690_1 := h690c.2.1
                              have p690_2 := h690c.2.2.1
                              have p690_3 := h690c.2.2.2
                              linarith only [h664, hlam, p690_0]
                            · have p690_0 := h690c.1
                              have p690_1 := h690c.2.1
                              have p690_2 := h690c.2.2.1
                              have p690_3 := h690c.2.2.2
                              linarith only [h667, hlam, p690_0]
                            · have p690_0 := h690c.1
                              have p690_1 := h690c.2.1
                              have p690_2 := h690c.2.2.1
                              have p690_3 := h690c.2.2.2
                              linarith only [h669, hlam, p690_0]
                            · have p690_0 := h690c.1
                              have p690_1 := h690c.2.1
                              have p690_2 := h690c.2.2.1
                              have p690_3 := h690c.2.2.2
                              linarith only [hlam, p690_0]
                            · have p690_0 := h690c.1
                              have p690_1 := h690c.2.1
                              have p690_2 := h690c.2.2.1
                              have p690_3 := h690c.2.2.2
                              linarith only [h671, hlam, p690_0]
                            · have p690_0 := h690c.1
                              have p690_1 := h690c.2.1
                              have p690_2 := h690c.2.2.1
                              have p690_3 := h690c.2.2.2
                              linarith only [h665, hlam, p690_0]
                            · have p690_0 := h690c.1
                              have p690_1 := h690c.2.1
                              have p690_2 := h690c.2.2.1
                              have p690_3 := h690c.2.2.2
                              linarith only [h668, hlam, p690_1]
                            · have p690_0 := h690c.1
                              have p690_1 := h690c.2.1
                              have p690_2 := h690c.2.2.1
                              have p690_3 := h690c.2.2.2
                              linarith only [h670, hlam, p690_0]
                            · have p690_0 := h690c.1
                              have p690_1 := h690c.2.1
                              have p690_2 := h690c.2.2.1
                              have p690_3 := h690c.2.2.2
                              linarith only [h665, h667, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p690_1, u0elo0, u2ehi3]
                            · have p690_0 := h690c.1
                              have p690_1 := h690c.2.1
                              have p690_2 := h690c.2.2.1
                              have p690_3 := h690c.2.2.2
                              linarith only [hlam, p690_0]
                      · linarith only [h666, h670, h685, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                    · linarith only [h666, h669, h684, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                  · linarith only [h0, h664, h667, h683, hc23, hlam, hphi, u2ehi3]
              · linarith only [h282, h665, h670, hlam]
            · linarith only [h282, h664, h669, hlam]
          · linarith only [h666, h668, hc25, hlam, hphi, u2ehi2]
        · linarith only [h666, h667, hc24, hlam, hphi, u2ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h723 | h723
        · linarith only [h666, h723, hc23, hlam, hphi, u2ehi3]
        · linarith only [h0, h664, h723, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h726 | h726
      · rcases m.htr 0 2 4 (by decide) (by decide) with h727 | h727
        · rcases m.htr 0 2 5 (by decide) (by decide) with h728 | h728
          · rcases m.htr 0 3 4 (by decide) (by decide) with h729 | h729
            · rcases m.htr 0 3 5 (by decide) (by decide) with h730 | h730
              · rcases m.htr 0 4 5 (by decide) (by decide) with h731 | h731
                · linarith only [h664, h665, h731, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h733 | h733
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h734 | h734
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h735 | h735
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h736 | h736
                        · linarith only [h726, h731, h734, h736, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h738 | h738
                          · linarith only [h726, h727, h731, h734, h738, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                          · rcases h0bigk with h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c
                            · have p740_0 := h740c.1
                              have p740_1 := h740c.2.1
                              have p740_2 := h740c.2.2.1
                              have p740_3 := h740c.2.2.2
                              linarith only [hlam, p740_0]
                            · have p740_0 := h740c.1
                              have p740_1 := h740c.2.1
                              have p740_2 := h740c.2.2.1
                              have p740_3 := h740c.2.2.2
                              linarith only [h0, hlam, p740_1]
                            · have p740_0 := h740c.1
                              have p740_1 := h740c.2.1
                              have p740_2 := h740c.2.2.1
                              have p740_3 := h740c.2.2.2
                              linarith only [h282, hlam, p740_0]
                            · have p740_0 := h740c.1
                              have p740_1 := h740c.2.1
                              have p740_2 := h740c.2.2.1
                              have p740_3 := h740c.2.2.2
                              linarith only [h727, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p740_1, u0elo0, u2ehi3]
                            · have p740_0 := h740c.1
                              have p740_1 := h740c.2.1
                              have p740_2 := h740c.2.2.1
                              have p740_3 := h740c.2.2.2
                              linarith only [h665, hlam, p740_1]
                            · have p740_0 := h740c.1
                              have p740_1 := h740c.2.1
                              have p740_2 := h740c.2.2.1
                              have p740_3 := h740c.2.2.2
                              linarith only [h664, hc14, hlam, hphi, ht0b, ht45, ht5b, p740_1, u0elo1]
                            · have p740_0 := h740c.1
                              have p740_1 := h740c.2.1
                              have p740_2 := h740c.2.2.1
                              have p740_3 := h740c.2.2.2
                              linarith only [hlam, p740_0]
                            · have p740_0 := h740c.1
                              have p740_1 := h740c.2.1
                              have p740_2 := h740c.2.2.1
                              have p740_3 := h740c.2.2.2
                              linarith only [h726, h735, h738, hc34, hlam, hphi, ht0b, ht45, ht5b, p740_1, u0elo1]
                            · have p740_0 := h740c.1
                              have p740_1 := h740c.2.1
                              have p740_2 := h740c.2.2.1
                              have p740_3 := h740c.2.2.2
                              linarith only [h727, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p740_1, u0elo1, u2ehi3]
                            · have p740_0 := h740c.1
                              have p740_1 := h740c.2.1
                              have p740_2 := h740c.2.2.1
                              have p740_3 := h740c.2.2.2
                              linarith only [h664, h665, h727, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p740_1, u0elo1, u2ehi3]
                            · have p740_0 := h740c.1
                              have p740_1 := h740c.2.1
                              have p740_2 := h740c.2.2.1
                              have p740_3 := h740c.2.2.2
                              linarith only [h664, h727, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p740_1, u0elo2, u2ehi3]
                            · have p740_0 := h740c.1
                              have p740_1 := h740c.2.1
                              have p740_2 := h740c.2.2.1
                              have p740_3 := h740c.2.2.2
                              linarith only [h726, hlam, p740_1]
                            · have p740_0 := h740c.1
                              have p740_1 := h740c.2.1
                              have p740_2 := h740c.2.2.1
                              have p740_3 := h740c.2.2.2
                              linarith only [hlam, p740_0]
                            · have p740_0 := h740c.1
                              have p740_1 := h740c.2.1
                              have p740_2 := h740c.2.2.1
                              have p740_3 := h740c.2.2.2
                              linarith only [h726, h727, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p740_1, u0elo1, u2ehi3]
                            · have p740_0 := h740c.1
                              have p740_1 := h740c.2.1
                              have p740_2 := h740c.2.2.1
                              have p740_3 := h740c.2.2.2
                              linarith only [h664, h665, h726, h727, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p740_1, u0elo1, u2ehi3]
                            · have p740_0 := h740c.1
                              have p740_1 := h740c.2.1
                              have p740_2 := h740c.2.2.1
                              have p740_3 := h740c.2.2.2
                              linarith only [h664, hlam, p740_0]
                            · have p740_0 := h740c.1
                              have p740_1 := h740c.2.1
                              have p740_2 := h740c.2.2.1
                              have p740_3 := h740c.2.2.2
                              linarith only [h727, hlam, p740_0]
                            · have p740_0 := h740c.1
                              have p740_1 := h740c.2.1
                              have p740_2 := h740c.2.2.1
                              have p740_3 := h740c.2.2.2
                              linarith only [h729, hlam, p740_0]
                            · have p740_0 := h740c.1
                              have p740_1 := h740c.2.1
                              have p740_2 := h740c.2.2.1
                              have p740_3 := h740c.2.2.2
                              linarith only [hlam, p740_0]
                            · have p740_0 := h740c.1
                              have p740_1 := h740c.2.1
                              have p740_2 := h740c.2.2.1
                              have p740_3 := h740c.2.2.2
                              linarith only [h731, hlam, p740_0]
                            · have p740_0 := h740c.1
                              have p740_1 := h740c.2.1
                              have p740_2 := h740c.2.2.1
                              have p740_3 := h740c.2.2.2
                              linarith only [h664, h727, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p740_1, u0elo4, u2ehi3]
                            · have p740_0 := h740c.1
                              have p740_1 := h740c.2.1
                              have p740_2 := h740c.2.2.1
                              have p740_3 := h740c.2.2.2
                              linarith only [h728, hlam, p740_1]
                            · have p740_0 := h740c.1
                              have p740_1 := h740c.2.1
                              have p740_2 := h740c.2.2.1
                              have p740_3 := h740c.2.2.2
                              linarith only [h730, hlam, p740_0]
                            · have p740_0 := h740c.1
                              have p740_1 := h740c.2.1
                              have p740_2 := h740c.2.2.1
                              have p740_3 := h740c.2.2.2
                              linarith only [h726, h727, h730, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p740_1, u0elo1, u2ehi3]
                            · have p740_0 := h740c.1
                              have p740_1 := h740c.2.1
                              have p740_2 := h740c.2.2.1
                              have p740_3 := h740c.2.2.2
                              linarith only [hlam, p740_0]
                      · linarith only [h726, h730, h734, h735, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                    · linarith only [h726, h729, h734, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                  · linarith only [h0, h728, h733, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h769 | h769
                · linarith only [h282, h664, h730, h769, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h771 | h771
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h772 | h772
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h773 | h773
                      · linarith only [h282, h664, h726, h727, h730, h773, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h775 | h775
                        · linarith only [h727, h769, h775, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h777 | h777
                          · linarith only [h726, h727, h769, h772, h777, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi3]
                          · rcases h0bigk with h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c | h779c
                            · have p779_0 := h779c.1
                              have p779_1 := h779c.2.1
                              have p779_2 := h779c.2.2.1
                              have p779_3 := h779c.2.2.2
                              linarith only [hlam, p779_0]
                            · have p779_0 := h779c.1
                              have p779_1 := h779c.2.1
                              have p779_2 := h779c.2.2.1
                              have p779_3 := h779c.2.2.2
                              linarith only [h0, hlam, p779_1]
                            · have p779_0 := h779c.1
                              have p779_1 := h779c.2.1
                              have p779_2 := h779c.2.2.1
                              have p779_3 := h779c.2.2.2
                              linarith only [h282, hlam, p779_0]
                            · have p779_0 := h779c.1
                              have p779_1 := h779c.2.1
                              have p779_2 := h779c.2.2.1
                              have p779_3 := h779c.2.2.2
                              linarith only [h727, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p779_1, u0elo0, u2ehi3]
                            · have p779_0 := h779c.1
                              have p779_1 := h779c.2.1
                              have p779_2 := h779c.2.2.1
                              have p779_3 := h779c.2.2.2
                              linarith only [h665, hlam, p779_1]
                            · have p779_0 := h779c.1
                              have p779_1 := h779c.2.1
                              have p779_2 := h779c.2.2.1
                              have p779_3 := h779c.2.2.2
                              linarith only [h664, hc14, hlam, hphi, ht0b, ht45, ht5b, p779_1, u0elo1]
                            · have p779_0 := h779c.1
                              have p779_1 := h779c.2.1
                              have p779_2 := h779c.2.2.1
                              have p779_3 := h779c.2.2.2
                              linarith only [hlam, p779_0]
                            · have p779_0 := h779c.1
                              have p779_1 := h779c.2.1
                              have p779_2 := h779c.2.2.1
                              have p779_3 := h779c.2.2.2
                              linarith only [h282, h664, h727, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p779_1, u0elo1, u2ehi3]
                            · have p779_0 := h779c.1
                              have p779_1 := h779c.2.1
                              have p779_2 := h779c.2.2.1
                              have p779_3 := h779c.2.2.2
                              linarith only [h727, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p779_1, u0elo1, u2ehi3]
                            · have p779_0 := h779c.1
                              have p779_1 := h779c.2.1
                              have p779_2 := h779c.2.2.1
                              have p779_3 := h779c.2.2.2
                              linarith only [h664, h665, h727, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p779_1, u0elo1, u2ehi3]
                            · have p779_0 := h779c.1
                              have p779_1 := h779c.2.1
                              have p779_2 := h779c.2.2.1
                              have p779_3 := h779c.2.2.2
                              linarith only [h664, h727, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p779_1, u0elo2, u2ehi3]
                            · have p779_0 := h779c.1
                              have p779_1 := h779c.2.1
                              have p779_2 := h779c.2.2.1
                              have p779_3 := h779c.2.2.2
                              linarith only [h726, hlam, p779_1]
                            · have p779_0 := h779c.1
                              have p779_1 := h779c.2.1
                              have p779_2 := h779c.2.2.1
                              have p779_3 := h779c.2.2.2
                              linarith only [hlam, p779_0]
                            · have p779_0 := h779c.1
                              have p779_1 := h779c.2.1
                              have p779_2 := h779c.2.2.1
                              have p779_3 := h779c.2.2.2
                              linarith only [h726, h727, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p779_1, u0elo1, u2ehi3]
                            · have p779_0 := h779c.1
                              have p779_1 := h779c.2.1
                              have p779_2 := h779c.2.2.1
                              have p779_3 := h779c.2.2.2
                              linarith only [h730, hlam, p779_1]
                            · have p779_0 := h779c.1
                              have p779_1 := h779c.2.1
                              have p779_2 := h779c.2.2.1
                              have p779_3 := h779c.2.2.2
                              linarith only [h664, hlam, p779_0]
                            · have p779_0 := h779c.1
                              have p779_1 := h779c.2.1
                              have p779_2 := h779c.2.2.1
                              have p779_3 := h779c.2.2.2
                              linarith only [h727, hlam, p779_0]
                            · have p779_0 := h779c.1
                              have p779_1 := h779c.2.1
                              have p779_2 := h779c.2.2.1
                              have p779_3 := h779c.2.2.2
                              linarith only [h729, hlam, p779_0]
                            · have p779_0 := h779c.1
                              have p779_1 := h779c.2.1
                              have p779_2 := h779c.2.2.1
                              have p779_3 := h779c.2.2.2
                              linarith only [hlam, p779_0]
                            · have p779_0 := h779c.1
                              have p779_1 := h779c.2.1
                              have p779_2 := h779c.2.2.1
                              have p779_3 := h779c.2.2.2
                              linarith only [h769, hlam, p779_0]
                            · have p779_0 := h779c.1
                              have p779_1 := h779c.2.1
                              have p779_2 := h779c.2.2.1
                              have p779_3 := h779c.2.2.2
                              linarith only [h664, h727, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p779_1, u0elo4, u2ehi3]
                            · have p779_0 := h779c.1
                              have p779_1 := h779c.2.1
                              have p779_2 := h779c.2.2.1
                              have p779_3 := h779c.2.2.2
                              linarith only [h728, hlam, p779_1]
                            · have p779_0 := h779c.1
                              have p779_1 := h779c.2.1
                              have p779_2 := h779c.2.2.1
                              have p779_3 := h779c.2.2.2
                              linarith only [h282, h664, h727, h728, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p779_1, u0elo1, u2ehi3]
                            · have p779_0 := h779c.1
                              have p779_1 := h779c.2.1
                              have p779_2 := h779c.2.2.1
                              have p779_3 := h779c.2.2.2
                              linarith only [h727, h728, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p779_1, u0elo1, u2ehi3]
                            · have p779_0 := h779c.1
                              have p779_1 := h779c.2.1
                              have p779_2 := h779c.2.2.1
                              have p779_3 := h779c.2.2.2
                              linarith only [hlam, p779_0]
                    · linarith only [h729, h772, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi2]
                  · linarith only [h0, h664, h727, h771, hc23, hlam, hphi, u2ehi3]
            · linarith only [h282, h664, h729, hlam]
          · linarith only [h726, h728, hc25, hlam, hphi, u2ehi2]
        · linarith only [h726, h727, hc24, hlam, hphi, u2ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h810 | h810
        · linarith only [h726, h810, hc23, hlam, hphi, u2ehi3]
        · linarith only [h0, h664, h810, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h813 | h813
    · rcases m.htr 0 2 3 (by decide) (by decide) with h814 | h814
      · rcases m.htr 0 2 4 (by decide) (by decide) with h815 | h815
        · rcases m.htr 0 2 5 (by decide) (by decide) with h816 | h816
          · rcases m.htr 0 3 4 (by decide) (by decide) with h817 | h817
            · rcases m.htr 0 3 5 (by decide) (by decide) with h818 | h818
              · rcases m.htr 0 4 5 (by decide) (by decide) with h819 | h819
                · rcases m.htr 1 2 3 (by decide) (by decide) with h820 | h820
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h821 | h821
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h822 | h822
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h823 | h823
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h824 | h824
                          · linarith only [h814, h821, h824, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                          · linarith only [h814, h821, h823, h824, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h817, h819, h823, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi3]
                      · linarith only [h814, h818, h821, h822, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                    · linarith only [h814, h817, h821, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                  · linarith only [h0, h813, h816, h820, hc23, hlam, hphi, u2ehi4]
                · linarith only [h664, h813, h819, hlam]
              · linarith only [h282, h813, h818, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h833 | h833
              · rcases m.htr 0 4 5 (by decide) (by decide) with h834 | h834
                · rcases m.htr 1 2 3 (by decide) (by decide) with h835 | h835
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h836 | h836
                    · linarith only [h814, h817, h836, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h838 | h838
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h839 | h839
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h840 | h840
                          · rcases h0bigk with h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c
                            · have p841_0 := h841c.1
                              have p841_1 := h841c.2.1
                              have p841_2 := h841c.2.2.1
                              have p841_3 := h841c.2.2.2
                              linarith only [hlam, p841_0]
                            · have p841_0 := h841c.1
                              have p841_1 := h841c.2.1
                              have p841_2 := h841c.2.2.1
                              have p841_3 := h841c.2.2.2
                              linarith only [h0, hlam, p841_1]
                            · have p841_0 := h841c.1
                              have p841_1 := h841c.2.1
                              have p841_2 := h841c.2.2.1
                              have p841_3 := h841c.2.2.2
                              linarith only [h282, hlam, p841_0]
                            · have p841_0 := h841c.1
                              have p841_1 := h841c.2.1
                              have p841_2 := h841c.2.2.1
                              have p841_3 := h841c.2.2.2
                              linarith only [h664, hlam, p841_1]
                            · have p841_0 := h841c.1
                              have p841_1 := h841c.2.1
                              have p841_2 := h841c.2.2.1
                              have p841_3 := h841c.2.2.2
                              linarith only [h816, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p841_1, u0elo0, u2ehi4]
                            · have p841_0 := h841c.1
                              have p841_1 := h841c.2.1
                              have p841_2 := h841c.2.2.1
                              have p841_3 := h841c.2.2.2
                              linarith only [h813, hc15, hlam, hphi, ht0b, ht5b, p841_1, u0elo1]
                            · have p841_0 := h841c.1
                              have p841_1 := h841c.2.1
                              have p841_2 := h841c.2.2.1
                              have p841_3 := h841c.2.2.2
                              linarith only [hlam, p841_0]
                            · have p841_0 := h841c.1
                              have p841_1 := h841c.2.1
                              have p841_2 := h841c.2.2.1
                              have p841_3 := h841c.2.2.2
                              linarith only [h282, h813, h816, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p841_1, u0elo1, u2ehi4]
                            · have p841_0 := h841c.1
                              have p841_1 := h841c.2.1
                              have p841_2 := h841c.2.2.1
                              have p841_3 := h841c.2.2.2
                              linarith only [h814, h817, h838, hc35, hlam, hphi, ht0b, ht5b, p841_1, u0elo1]
                            · have p841_0 := h841c.1
                              have p841_1 := h841c.2.1
                              have p841_2 := h841c.2.2.1
                              have p841_3 := h841c.2.2.2
                              linarith only [h816, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p841_1, u0elo1, u2ehi4]
                            · have p841_0 := h841c.1
                              have p841_1 := h841c.2.1
                              have p841_2 := h841c.2.2.1
                              have p841_3 := h841c.2.2.2
                              linarith only [h813, h816, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p841_1, u0elo2, u2ehi4]
                            · have p841_0 := h841c.1
                              have p841_1 := h841c.2.1
                              have p841_2 := h841c.2.2.1
                              have p841_3 := h841c.2.2.2
                              linarith only [h814, hlam, p841_1]
                            · have p841_0 := h841c.1
                              have p841_1 := h841c.2.1
                              have p841_2 := h841c.2.2.1
                              have p841_3 := h841c.2.2.2
                              linarith only [hlam, p841_0]
                            · have p841_0 := h841c.1
                              have p841_1 := h841c.2.1
                              have p841_2 := h841c.2.2.1
                              have p841_3 := h841c.2.2.2
                              linarith only [h817, hlam, p841_1]
                            · have p841_0 := h841c.1
                              have p841_1 := h841c.2.1
                              have p841_2 := h841c.2.2.1
                              have p841_3 := h841c.2.2.2
                              linarith only [h816, h817, hc34, hlam, hphi, ht23, p841_1, u2ehi4]
                            · have p841_0 := h841c.1
                              have p841_1 := h841c.2.1
                              have p841_2 := h841c.2.2.1
                              have p841_3 := h841c.2.2.2
                              linarith only [h813, h815, h816, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p841_1, u0elo1, u2ehi4]
                            · have p841_0 := h841c.1
                              have p841_1 := h841c.2.1
                              have p841_2 := h841c.2.2.1
                              have p841_3 := h841c.2.2.2
                              linarith only [h815, hlam, p841_0]
                            · have p841_0 := h841c.1
                              have p841_1 := h841c.2.1
                              have p841_2 := h841c.2.2.1
                              have p841_3 := h841c.2.2.2
                              linarith only [h282, h813, h815, h816, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p841_1, u0elo1, u2ehi4]
                            · have p841_0 := h841c.1
                              have p841_1 := h841c.2.1
                              have p841_2 := h841c.2.2.1
                              have p841_3 := h841c.2.2.2
                              linarith only [hlam, p841_0]
                            · have p841_0 := h841c.1
                              have p841_1 := h841c.2.1
                              have p841_2 := h841c.2.2.1
                              have p841_3 := h841c.2.2.2
                              linarith only [h815, h816, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p841_1, u0elo1, u2ehi4]
                            · have p841_0 := h841c.1
                              have p841_1 := h841c.2.1
                              have p841_2 := h841c.2.2.1
                              have p841_3 := h841c.2.2.2
                              linarith only [h813, hlam, p841_0]
                            · have p841_0 := h841c.1
                              have p841_1 := h841c.2.1
                              have p841_2 := h841c.2.2.1
                              have p841_3 := h841c.2.2.2
                              linarith only [h816, hlam, p841_1]
                            · have p841_0 := h841c.1
                              have p841_1 := h841c.2.1
                              have p841_2 := h841c.2.2.1
                              have p841_3 := h841c.2.2.2
                              linarith only [h833, hlam, p841_0]
                            · have p841_0 := h841c.1
                              have p841_1 := h841c.2.1
                              have p841_2 := h841c.2.2.1
                              have p841_3 := h841c.2.2.2
                              linarith only [h834, hlam, p841_1]
                            · have p841_0 := h841c.1
                              have p841_1 := h841c.2.1
                              have p841_2 := h841c.2.2.1
                              have p841_3 := h841c.2.2.2
                              linarith only [hlam, p841_0]
                          · linarith only [h282, h813, h816, h817, h840, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                        · linarith only [h282, h813, h817, h834, h839, hc34, hlam, hphi, ht23, u2ehi3]
                      · linarith only [h817, h833, h838, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h814, h835, hlam]
                · linarith only [h282, h813, h817, h834, hlam]
              · linarith only [h282, h813, h833, hlam]
          · linarith only [h814, h816, hc25, hlam, hphi, u2ehi2]
        · linarith only [h814, h815, hc24, hlam, hphi, u2ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h875 | h875
        · linarith only [h814, h875, hc23, hlam, hphi, u2ehi3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h877 | h877
          · linarith only [h814, h877, hc23, hlam, hphi, u2ehi4]
          · linarith only [h0, h813, h877, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h880 | h880
      · rcases m.htr 0 2 4 (by decide) (by decide) with h881 | h881
        · rcases m.htr 0 2 5 (by decide) (by decide) with h882 | h882
          · rcases m.htr 0 3 4 (by decide) (by decide) with h883 | h883
            · rcases m.htr 0 3 5 (by decide) (by decide) with h884 | h884
              · rcases m.htr 0 4 5 (by decide) (by decide) with h885 | h885
                · rcases m.htr 1 2 3 (by decide) (by decide) with h886 | h886
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h887 | h887
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h888 | h888
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h889 | h889
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h890 | h890
                          · linarith only [h880, h887, h890, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                          · linarith only [h880, h887, h889, h890, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h880, h883, h885, h889, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                      · linarith only [h880, h884, h888, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                    · linarith only [h880, h883, h887, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                  · linarith only [h0, h880, h886, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h897 | h897
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h898 | h898
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h899 | h899
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h900 | h900
                        · linarith only [h881, h885, h900, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h902 | h902
                          · linarith only [h881, h885, h902, hc34, hlam, hphi, ht23, u2ehi3]
                          · rcases h0bigk with h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c
                            · have p904_0 := h904c.1
                              have p904_1 := h904c.2.1
                              have p904_2 := h904c.2.2.1
                              have p904_3 := h904c.2.2.2
                              linarith only [hlam, p904_0]
                            · have p904_0 := h904c.1
                              have p904_1 := h904c.2.1
                              have p904_2 := h904c.2.2.1
                              have p904_3 := h904c.2.2.2
                              linarith only [h0, hlam, p904_1]
                            · have p904_0 := h904c.1
                              have p904_1 := h904c.2.1
                              have p904_2 := h904c.2.2.1
                              have p904_3 := h904c.2.2.2
                              linarith only [h282, hlam, p904_0]
                            · have p904_0 := h904c.1
                              have p904_1 := h904c.2.1
                              have p904_2 := h904c.2.2.1
                              have p904_3 := h904c.2.2.2
                              linarith only [h664, hlam, p904_1]
                            · have p904_0 := h904c.1
                              have p904_1 := h904c.2.1
                              have p904_2 := h904c.2.2.1
                              have p904_3 := h904c.2.2.2
                              linarith only [h813, hlam, p904_1]
                            · have p904_0 := h904c.1
                              have p904_1 := h904c.2.1
                              have p904_2 := h904c.2.2.1
                              have p904_3 := h904c.2.2.2
                              rcases p904_3 (m.d 0 1) (by simp) with h910 | h910
                              · linarith only [h0, h910, hlam]
                              · rcases p904_3 (m.d 0 2) (by simp) with h912 | h912
                                · rcases p904_3 (m.d 0 3) (by simp) with h913 | h913
                                  · linarith only [h880, h913, hlam]
                                  · linarith only [h282, h913, hlam]
                                · linarith only [h0, h912, hlam]
                            · have p904_0 := h904c.1
                              have p904_1 := h904c.2.1
                              have p904_2 := h904c.2.2.1
                              have p904_3 := h904c.2.2.2
                              linarith only [hlam, p904_0]
                            · have p904_0 := h904c.1
                              have p904_1 := h904c.2.1
                              have p904_2 := h904c.2.2.1
                              have p904_3 := h904c.2.2.2
                              linarith only [h881, h884, h885, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p904_1, u0elo1, u2ehi3]
                            · have p904_0 := h904c.1
                              have p904_1 := h904c.2.1
                              have p904_2 := h904c.2.2.1
                              have p904_3 := h904c.2.2.2
                              linarith only [h881, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p904_1, u0elo1, u2ehi3]
                            · have p904_0 := h904c.1
                              have p904_1 := h904c.2.1
                              have p904_2 := h904c.2.2.1
                              have p904_3 := h904c.2.2.2
                              linarith only [h881, h885, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p904_1, u0elo1, u2ehi3]
                            · have p904_0 := h904c.1
                              have p904_1 := h904c.2.1
                              have p904_2 := h904c.2.2.1
                              have p904_3 := h904c.2.2.2
                              rcases p904_3 (m.d 0 1) (by simp) with h921 | h921
                              · linarith only [h282, h921, hlam]
                              · rcases p904_3 (m.d 0 2) (by simp) with h923 | h923
                                · rcases p904_3 (m.d 0 3) (by simp) with h924 | h924
                                  · rcases p904_3 (m.d 0 4) (by simp) with h925 | h925
                                    · linarith only [h883, h925, hlam]
                                    · linarith only [h664, h925, hlam]
                                  · linarith only [h282, h924, hlam]
                                · linarith only [h0, h923, hlam]
                            · have p904_0 := h904c.1
                              have p904_1 := h904c.2.1
                              have p904_2 := h904c.2.2.1
                              have p904_3 := h904c.2.2.2
                              linarith only [h880, hlam, p904_1]
                            · have p904_0 := h904c.1
                              have p904_1 := h904c.2.1
                              have p904_2 := h904c.2.2.1
                              have p904_3 := h904c.2.2.2
                              linarith only [hlam, p904_0]
                            · have p904_0 := h904c.1
                              have p904_1 := h904c.2.1
                              have p904_2 := h904c.2.2.1
                              have p904_3 := h904c.2.2.2
                              linarith only [h881, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p904_1, u0elo2, u2ehi3]
                            · have p904_0 := h904c.1
                              have p904_1 := h904c.2.1
                              have p904_2 := h904c.2.2.1
                              have p904_3 := h904c.2.2.2
                              linarith only [h880, h881, h885, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p904_1, u0elo1, u2ehi3]
                            · have p904_0 := h904c.1
                              have p904_1 := h904c.2.1
                              have p904_2 := h904c.2.2.1
                              have p904_3 := h904c.2.2.2
                              linarith only [h885, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p904_1]
                            · have p904_0 := h904c.1
                              have p904_1 := h904c.2.1
                              have p904_2 := h904c.2.2.1
                              have p904_3 := h904c.2.2.2
                              linarith only [h881, hlam, p904_0]
                            · have p904_0 := h904c.1
                              have p904_1 := h904c.2.1
                              have p904_2 := h904c.2.2.1
                              have p904_3 := h904c.2.2.2
                              linarith only [h883, hlam, p904_0]
                            · have p904_0 := h904c.1
                              have p904_1 := h904c.2.1
                              have p904_2 := h904c.2.2.1
                              have p904_3 := h904c.2.2.2
                              linarith only [hlam, p904_0]
                            · have p904_0 := h904c.1
                              have p904_1 := h904c.2.1
                              have p904_2 := h904c.2.2.1
                              have p904_3 := h904c.2.2.2
                              linarith only [h885, hlam, p904_0]
                            · have p904_0 := h904c.1
                              have p904_1 := h904c.2.1
                              have p904_2 := h904c.2.2.1
                              have p904_3 := h904c.2.2.2
                              rcases p904_3 (m.d 0 1) (by simp) with h939 | h939
                              · linarith only [h813, h939, hlam]
                              · rcases p904_3 (m.d 0 2) (by simp) with h941 | h941
                                · rcases p904_3 (m.d 0 3) (by simp) with h942 | h942
                                  · rcases p904_3 (m.d 0 4) (by simp) with h943 | h943
                                    · linarith only [h885, h943, hlam]
                                    · linarith only [h664, h943, hlam]
                                  · linarith only [h282, h942, hlam]
                                · linarith only [h0, h941, hlam]
                            · have p904_0 := h904c.1
                              have p904_1 := h904c.2.1
                              have p904_2 := h904c.2.2.1
                              have p904_3 := h904c.2.2.2
                              linarith only [h882, hlam, p904_1]
                            · have p904_0 := h904c.1
                              have p904_1 := h904c.2.1
                              have p904_2 := h904c.2.2.1
                              have p904_3 := h904c.2.2.2
                              linarith only [h884, hlam, p904_0]
                            · have p904_0 := h904c.1
                              have p904_1 := h904c.2.1
                              have p904_2 := h904c.2.2.1
                              have p904_3 := h904c.2.2.2
                              linarith only [h881, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p904_1, u0elo4, u2ehi3]
                            · have p904_0 := h904c.1
                              have p904_1 := h904c.2.1
                              have p904_2 := h904c.2.2.1
                              have p904_3 := h904c.2.2.2
                              linarith only [hlam, p904_0]
                      · linarith only [h880, h884, h899, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                    · linarith only [h880, h883, h898, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                  · linarith only [h0, h880, h897, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h955 | h955
                · linarith only [h883, h884, h955, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h957 | h957
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h958 | h958
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h959 | h959
                      · linarith only [h880, h884, h959, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h961 | h961
                        · linarith only [h881, h955, h961, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h963 | h963
                          · linarith only [h881, h955, h963, hc34, hlam, hphi, ht23, u2ehi3]
                          · rcases h0bigk with h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c
                            · have p965_0 := h965c.1
                              have p965_1 := h965c.2.1
                              have p965_2 := h965c.2.2.1
                              have p965_3 := h965c.2.2.2
                              linarith only [hlam, p965_0]
                            · have p965_0 := h965c.1
                              have p965_1 := h965c.2.1
                              have p965_2 := h965c.2.2.1
                              have p965_3 := h965c.2.2.2
                              linarith only [h0, hlam, p965_1]
                            · have p965_0 := h965c.1
                              have p965_1 := h965c.2.1
                              have p965_2 := h965c.2.2.1
                              have p965_3 := h965c.2.2.2
                              linarith only [h282, hlam, p965_0]
                            · have p965_0 := h965c.1
                              have p965_1 := h965c.2.1
                              have p965_2 := h965c.2.2.1
                              have p965_3 := h965c.2.2.2
                              linarith only [h664, hlam, p965_1]
                            · have p965_0 := h965c.1
                              have p965_1 := h965c.2.1
                              have p965_2 := h965c.2.2.1
                              have p965_3 := h965c.2.2.2
                              linarith only [h813, hlam, p965_1]
                            · have p965_0 := h965c.1
                              have p965_1 := h965c.2.1
                              have p965_2 := h965c.2.2.1
                              have p965_3 := h965c.2.2.2
                              rcases p965_3 (m.d 0 1) (by simp) with h971 | h971
                              · linarith only [h0, h971, hlam]
                              · rcases p965_3 (m.d 0 2) (by simp) with h973 | h973
                                · rcases p965_3 (m.d 0 3) (by simp) with h974 | h974
                                  · linarith only [h880, h974, hlam]
                                  · linarith only [h282, h974, hlam]
                                · linarith only [h0, h973, hlam]
                            · have p965_0 := h965c.1
                              have p965_1 := h965c.2.1
                              have p965_2 := h965c.2.2.1
                              have p965_3 := h965c.2.2.2
                              linarith only [hlam, p965_0]
                            · have p965_0 := h965c.1
                              have p965_1 := h965c.2.1
                              have p965_2 := h965c.2.2.1
                              have p965_3 := h965c.2.2.2
                              linarith only [h880, h958, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p965_1, u0elo1, u2ehi3]
                            · have p965_0 := h965c.1
                              have p965_1 := h965c.2.1
                              have p965_2 := h965c.2.2.1
                              have p965_3 := h965c.2.2.2
                              linarith only [h881, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p965_1, u0elo1, u2ehi3]
                            · have p965_0 := h965c.1
                              have p965_1 := h965c.2.1
                              have p965_2 := h965c.2.2.1
                              have p965_3 := h965c.2.2.2
                              linarith only [h880, h884, h958, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p965_1, u0elo1, u2ehi3]
                            · have p965_0 := h965c.1
                              have p965_1 := h965c.2.1
                              have p965_2 := h965c.2.2.1
                              have p965_3 := h965c.2.2.2
                              linarith only [h884, hc01, hc35, hlam, hphi, ht12, ht23, p965_1]
                            · have p965_0 := h965c.1
                              have p965_1 := h965c.2.1
                              have p965_2 := h965c.2.2.1
                              have p965_3 := h965c.2.2.2
                              linarith only [h880, hlam, p965_1]
                            · have p965_0 := h965c.1
                              have p965_1 := h965c.2.1
                              have p965_2 := h965c.2.2.1
                              have p965_3 := h965c.2.2.2
                              linarith only [hlam, p965_0]
                            · have p965_0 := h965c.1
                              have p965_1 := h965c.2.1
                              have p965_2 := h965c.2.2.1
                              have p965_3 := h965c.2.2.2
                              linarith only [h881, h884, h963, hc45, hlam, hphi, ht23, ht34, p965_1, u2ehi3]
                            · have p965_0 := h965c.1
                              have p965_1 := h965c.2.1
                              have p965_2 := h965c.2.2.1
                              have p965_3 := h965c.2.2.2
                              linarith only [h884, hlam, p965_1]
                            · have p965_0 := h965c.1
                              have p965_1 := h965c.2.1
                              have p965_2 := h965c.2.2.1
                              have p965_3 := h965c.2.2.2
                              linarith only [h883, h884, h963, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p965_1]
                            · have p965_0 := h965c.1
                              have p965_1 := h965c.2.1
                              have p965_2 := h965c.2.2.1
                              have p965_3 := h965c.2.2.2
                              linarith only [h881, hlam, p965_0]
                            · have p965_0 := h965c.1
                              have p965_1 := h965c.2.1
                              have p965_2 := h965c.2.2.1
                              have p965_3 := h965c.2.2.2
                              linarith only [h883, hlam, p965_0]
                            · have p965_0 := h965c.1
                              have p965_1 := h965c.2.1
                              have p965_2 := h965c.2.2.1
                              have p965_3 := h965c.2.2.2
                              linarith only [hlam, p965_0]
                            · have p965_0 := h965c.1
                              have p965_1 := h965c.2.1
                              have p965_2 := h965c.2.2.1
                              have p965_3 := h965c.2.2.2
                              linarith only [h955, hlam, p965_0]
                            · have p965_0 := h965c.1
                              have p965_1 := h965c.2.1
                              have p965_2 := h965c.2.2.1
                              have p965_3 := h965c.2.2.2
                              rcases p965_3 (m.d 0 1) (by simp) with h992 | h992
                              · linarith only [h813, h992, hlam]
                              · rcases p965_3 (m.d 0 2) (by simp) with h994 | h994
                                · rcases p965_3 (m.d 0 3) (by simp) with h995 | h995
                                  · linarith only [h884, h995, hlam]
                                  · linarith only [h282, h995, hlam]
                                · linarith only [h0, h994, hlam]
                            · have p965_0 := h965c.1
                              have p965_1 := h965c.2.1
                              have p965_2 := h965c.2.2.1
                              have p965_3 := h965c.2.2.2
                              linarith only [h882, hlam, p965_1]
                            · have p965_0 := h965c.1
                              have p965_1 := h965c.2.1
                              have p965_2 := h965c.2.2.1
                              have p965_3 := h965c.2.2.2
                              linarith only [h880, h958, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p965_1, u0elo4, u2ehi3]
                            · have p965_0 := h965c.1
                              have p965_1 := h965c.2.1
                              have p965_2 := h965c.2.2.1
                              have p965_3 := h965c.2.2.2
                              linarith only [h881, h882, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p965_1, u0elo1, u2ehi3]
                            · have p965_0 := h965c.1
                              have p965_1 := h965c.2.1
                              have p965_2 := h965c.2.2.1
                              have p965_3 := h965c.2.2.2
                              linarith only [hlam, p965_0]
                    · linarith only [h883, h958, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi2]
                  · linarith only [h0, h882, h957, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1005 | h1005
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1006 | h1006
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1007 | h1007
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1008 | h1008
                    · linarith only [h1005, h1008, h882, h883, hc23, hlam, hphi, u2ehi4]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1010 | h1010
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1011 | h1011
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1012 | h1012
                          · rcases h0bigk with h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [hlam, p1013_0]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [h0, hlam, p1013_1]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [h282, hlam, p1013_0]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [h664, hlam, p1013_1]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [h813, hlam, p1013_1]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              rcases p1013_3 (m.d 0 1) (by simp) with h1019 | h1019
                              · linarith only [h0, h1019, hlam]
                              · rcases p1013_3 (m.d 0 2) (by simp) with h1021 | h1021
                                · rcases p1013_3 (m.d 0 3) (by simp) with h1022 | h1022
                                  · linarith only [h1022, h880, hlam]
                                  · linarith only [h1022, h282, hlam]
                                · linarith only [h0, h1021, hlam]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [hlam, p1013_0]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [h1005, h882, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1013_1, u0elo1, u2ehi4]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [h1005, h882, h883, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1013_1, u0elo1, u2ehi4]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [h882, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1013_1, u0elo1, u2ehi4]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [h883, hc01, hc34, hlam, hphi, ht12, ht23, p1013_1]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [h880, hlam, p1013_1]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [hlam, p1013_0]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [h883, hlam, p1013_1]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [h882, h883, hc34, hlam, hphi, ht23, p1013_1, u2ehi4]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              rcases p1013_3 (m.d 0 1) (by simp) with h1035 | h1035
                              · linarith only [h1035, h664, hlam]
                              · rcases p1013_3 (m.d 0 2) (by simp) with h1037 | h1037
                                · rcases p1013_3 (m.d 0 3) (by simp) with h1038 | h1038
                                  · linarith only [h1038, h883, hlam]
                                  · linarith only [h1038, h282, hlam]
                                · linarith only [h0, h1037, hlam]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [h881, hlam, p1013_0]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [h1010, h880, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1013_1, u0elo3, u2ehi4]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [hlam, p1013_0]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [h881, h882, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1013_1, u0elo1, u2ehi4]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [h1005, h883, hc01, hc34, hlam, hphi, ht12, ht23, p1013_1]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [h882, hlam, p1013_1]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [h1005, hlam, p1013_0]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [h1006, hlam, p1013_1]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [hlam, p1013_0]
                          · linarith only [h1010, h1012, h880, h883, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                        · linarith only [h1005, h1006, h1008, h1010, h1011, h883, hc34, hlam, hphi, ht23, u2ehi4]
                      · linarith only [h1005, h1010, h883, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h1007, h880, hlam]
                · linarith only [h1005, h1006, h883, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1056 | h1056
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1057 | h1057
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1058 | h1058
                    · linarith only [h1058, h880, h883, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1060 | h1060
                      · linarith only [h1005, h1060, h880, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1062 | h1062
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1063 | h1063
                          · rcases h0bigk with h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h0, hlam, p1064_1]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h282, hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h664, hlam, p1064_1]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h813, hlam, p1064_1]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              rcases p1064_3 (m.d 0 1) (by simp) with h1070 | h1070
                              · linarith only [h0, h1070, hlam]
                              · rcases p1064_3 (m.d 0 2) (by simp) with h1072 | h1072
                                · rcases p1064_3 (m.d 0 3) (by simp) with h1073 | h1073
                                  · linarith only [h1073, h880, hlam]
                                  · linarith only [h1073, h282, hlam]
                                · linarith only [h0, h1072, hlam]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h880, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1064_1, u0elo1, u2ehi2]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h1060, h1062, h881, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1064_1, u0elo1, u2ehi2]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h1060, h882, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1064_1, u0elo1, u2ehi2]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h1005, h1063, hc01, hc34, hlam, hphi, ht12, ht23, p1064_1]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h880, hlam, p1064_1]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h883, hlam, p1064_1]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h1005, hlam, p1064_1]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              rcases p1064_3 (m.d 0 1) (by simp) with h1086 | h1086
                              · linarith only [h1086, h664, hlam]
                              · rcases p1064_3 (m.d 0 2) (by simp) with h1088 | h1088
                                · rcases p1064_3 (m.d 0 3) (by simp) with h1089 | h1089
                                  · linarith only [h1089, h883, hlam]
                                  · linarith only [h1089, h282, hlam]
                                · linarith only [h0, h1088, hlam]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h881, hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h880, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1064_1, u0elo3, u2ehi2]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h1005, h880, h881, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1064_1, u0elo1, u2ehi2]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              rcases p1064_3 (m.d 0 1) (by simp) with h1097 | h1097
                              · linarith only [h1097, h813, hlam]
                              · rcases p1064_3 (m.d 0 2) (by simp) with h1099 | h1099
                                · rcases p1064_3 (m.d 0 3) (by simp) with h1100 | h1100
                                  · linarith only [h1005, h1100, hlam]
                                  · linarith only [h1100, h282, hlam]
                                · linarith only [h0, h1099, hlam]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h882, hlam, p1064_1]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h880, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1064_1, u0elo4, u2ehi2]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h1056, hlam, p1064_1]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [hlam, p1064_0]
                          · linarith only [h1062, h1063, h881, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h1056, h1062, h881, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                  · linarith only [h0, h1057, h880, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1111 | h1111
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1112 | h1112
                    · linarith only [h1112, h880, h883, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1114 | h1114
                      · linarith only [h1005, h1114, h880, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1116 | h1116
                        · linarith only [h1056, h1116, h881, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1118 | h1118
                          · linarith only [h1056, h1118, h880, h883, hc34, hlam, hphi, ht23, u2ehi2]
                          · linarith only [h1118, h880, h883, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h0, h1111, h880, h883, hc34, hlam, hphi, ht23, u2ehi0]
          · linarith only [h880, h882, hc25, hlam, hphi, u2ehi2]
        · linarith only [h880, h881, hc24, hlam, hphi, u2ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1124 | h1124
        · linarith only [h1124, h880, hc23, hlam, hphi, u2ehi3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1126 | h1126
          · linarith only [h1126, h880, hc23, hlam, hphi, u2ehi4]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1128 | h1128
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1129 | h1129
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1130 | h1130
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1131 | h1131
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1132 | h1132
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1133 | h1133
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1134 | h1134
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1135 | h1135
                          · rcases h0bigk with h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [hlam, p1136_0]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h0, hlam, p1136_1]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h282, hlam, p1136_0]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h664, hlam, p1136_1]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h813, hlam, p1136_1]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h1126, h1131, h1132, h1134, hc01, hc12, hlam, hphi, p1136_1]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [hlam, p1136_0]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h880, hlam, p1136_0]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h1124, hlam, p1136_1]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h1126, hlam, p1136_0]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h1131, h880, hc01, hc12, hlam, hphi, p1136_1]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h1131, h880, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1136_1, u2ehi0]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [hlam, p1136_0]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h1126, h1130, h1131, h880, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1136_1, u2ehi0]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h1126, h1131, h880, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1136_1, u2ehi0]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h1124, h1131, h1132, hc01, hc12, hlam, hphi, p1136_1]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h1124, h1131, h1132, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1136_1, u2ehi0]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h1128, hlam, p1136_0]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [hlam, p1136_0]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h1124, h1126, h1131, h1132, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1136_1, u2ehi0]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h1126, h1131, h1132, h1134, hc01, hc12, hlam, hphi, p1136_1]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h1126, h1131, h1132, h1134, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1136_1, u2ehi0]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h1129, hlam, p1136_0]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h1130, hlam, p1136_1]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [hlam, p1136_0]
                          · rcases h0bigk with h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c
                            · have p1162_0 := h1162c.1
                              have p1162_1 := h1162c.2.1
                              have p1162_2 := h1162c.2.2.1
                              have p1162_3 := h1162c.2.2.2
                              linarith only [hlam, p1162_0]
                            · have p1162_0 := h1162c.1
                              have p1162_1 := h1162c.2.1
                              have p1162_2 := h1162c.2.2.1
                              have p1162_3 := h1162c.2.2.2
                              linarith only [h0, hlam, p1162_1]
                            · have p1162_0 := h1162c.1
                              have p1162_1 := h1162c.2.1
                              have p1162_2 := h1162c.2.2.1
                              have p1162_3 := h1162c.2.2.2
                              linarith only [h282, hlam, p1162_0]
                            · have p1162_0 := h1162c.1
                              have p1162_1 := h1162c.2.1
                              have p1162_2 := h1162c.2.2.1
                              have p1162_3 := h1162c.2.2.2
                              linarith only [h664, hlam, p1162_1]
                            · have p1162_0 := h1162c.1
                              have p1162_1 := h1162c.2.1
                              have p1162_2 := h1162c.2.2.1
                              have p1162_3 := h1162c.2.2.2
                              linarith only [h813, hlam, p1162_1]
                            · have p1162_0 := h1162c.1
                              have p1162_1 := h1162c.2.1
                              have p1162_2 := h1162c.2.2.1
                              have p1162_3 := h1162c.2.2.2
                              linarith only [h1131, h880, hc01, hc12, hlam, hphi, p1162_1]
                            · have p1162_0 := h1162c.1
                              have p1162_1 := h1162c.2.1
                              have p1162_2 := h1162c.2.2.1
                              have p1162_3 := h1162c.2.2.2
                              linarith only [hlam, p1162_0]
                            · have p1162_0 := h1162c.1
                              have p1162_1 := h1162c.2.1
                              have p1162_2 := h1162c.2.2.1
                              have p1162_3 := h1162c.2.2.2
                              linarith only [h880, hlam, p1162_0]
                            · have p1162_0 := h1162c.1
                              have p1162_1 := h1162c.2.1
                              have p1162_2 := h1162c.2.2.1
                              have p1162_3 := h1162c.2.2.2
                              linarith only [h1124, hlam, p1162_1]
                            · have p1162_0 := h1162c.1
                              have p1162_1 := h1162c.2.1
                              have p1162_2 := h1162c.2.2.1
                              have p1162_3 := h1162c.2.2.2
                              linarith only [h1126, hlam, p1162_0]
                            · have p1162_0 := h1162c.1
                              have p1162_1 := h1162c.2.1
                              have p1162_2 := h1162c.2.2.1
                              have p1162_3 := h1162c.2.2.2
                              linarith only [h1131, h880, hc01, hc12, hlam, hphi, p1162_1]
                            · have p1162_0 := h1162c.1
                              have p1162_1 := h1162c.2.1
                              have p1162_2 := h1162c.2.2.1
                              have p1162_3 := h1162c.2.2.2
                              linarith only [h1131, h880, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1162_1, u2ehi0]
                            · have p1162_0 := h1162c.1
                              have p1162_1 := h1162c.2.1
                              have p1162_2 := h1162c.2.2.1
                              have p1162_3 := h1162c.2.2.2
                              linarith only [hlam, p1162_0]
                            · have p1162_0 := h1162c.1
                              have p1162_1 := h1162c.2.1
                              have p1162_2 := h1162c.2.2.1
                              have p1162_3 := h1162c.2.2.2
                              linarith only [h1131, h664, h880, hc01, hc12, hlam, hphi, p1162_1]
                            · have p1162_0 := h1162c.1
                              have p1162_1 := h1162c.2.1
                              have p1162_2 := h1162c.2.2.1
                              have p1162_3 := h1162c.2.2.2
                              linarith only [h1131, h813, h880, hc01, hc12, hlam, hphi, p1162_1]
                            · have p1162_0 := h1162c.1
                              have p1162_1 := h1162c.2.1
                              have p1162_2 := h1162c.2.2.1
                              have p1162_3 := h1162c.2.2.2
                              linarith only [h1124, h1131, h1132, hc01, hc12, hlam, hphi, p1162_1]
                            · have p1162_0 := h1162c.1
                              have p1162_1 := h1162c.2.1
                              have p1162_2 := h1162c.2.2.1
                              have p1162_3 := h1162c.2.2.2
                              linarith only [h1124, h1131, h1132, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1162_1, u2ehi0]
                            · have p1162_0 := h1162c.1
                              have p1162_1 := h1162c.2.1
                              have p1162_2 := h1162c.2.2.1
                              have p1162_3 := h1162c.2.2.2
                              linarith only [h1128, hlam, p1162_0]
                            · have p1162_0 := h1162c.1
                              have p1162_1 := h1162c.2.1
                              have p1162_2 := h1162c.2.2.1
                              have p1162_3 := h1162c.2.2.2
                              linarith only [hlam, p1162_0]
                            · have p1162_0 := h1162c.1
                              have p1162_1 := h1162c.2.1
                              have p1162_2 := h1162c.2.2.1
                              have p1162_3 := h1162c.2.2.2
                              linarith only [h1124, h1126, h1131, h1132, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1162_1, u2ehi0]
                            · have p1162_0 := h1162c.1
                              have p1162_1 := h1162c.2.1
                              have p1162_2 := h1162c.2.2.1
                              have p1162_3 := h1162c.2.2.2
                              linarith only [h1126, h1131, h1132, h1134, hc01, hc12, hlam, hphi, p1162_1]
                            · have p1162_0 := h1162c.1
                              have p1162_1 := h1162c.2.1
                              have p1162_2 := h1162c.2.2.1
                              have p1162_3 := h1162c.2.2.2
                              linarith only [h1126, h1131, h1132, h1134, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1162_1, u2ehi0]
                            · have p1162_0 := h1162c.1
                              have p1162_1 := h1162c.2.1
                              have p1162_2 := h1162c.2.2.1
                              have p1162_3 := h1162c.2.2.2
                              linarith only [h1129, hlam, p1162_0]
                            · have p1162_0 := h1162c.1
                              have p1162_1 := h1162c.2.1
                              have p1162_2 := h1162c.2.2.1
                              have p1162_3 := h1162c.2.2.2
                              linarith only [h1130, hlam, p1162_1]
                            · have p1162_0 := h1162c.1
                              have p1162_1 := h1162c.2.1
                              have p1162_2 := h1162c.2.2.1
                              have p1162_3 := h1162c.2.2.2
                              linarith only [hlam, p1162_0]
                        · linarith only [h1124, h1134, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                      · linarith only [h1133, h880, hc35, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h1132, h880, hc34, hlam, hphi, ht23, u2ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1191 | h1191
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1192 | h1192
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1193 | h1193
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1194 | h1194
                          · rcases h0bigk with h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [hlam, p1195_0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h0, hlam, p1195_1]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h282, hlam, p1195_0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h664, hlam, p1195_1]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h813, hlam, p1195_1]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h1126, h1193, hc01, hc24, hlam, hphi, ht12, p1195_1]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [hlam, p1195_0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h880, hlam, p1195_0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h1124, hlam, p1195_1]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h1126, hlam, p1195_0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              rcases p1195_3 (m.d 0 1) (by simp) with h1206 | h1206
                              · linarith only [h1206, h282, hlam]
                              · rcases p1195_3 (m.d 0 2) (by simp) with h1208 | h1208
                                · linarith only [h1208, h880, hlam]
                                · linarith only [h0, h1208, hlam]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1195_1, u0elo2, u2ehi0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [hlam, p1195_0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h1126, h1130, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1195_1, u0elo2, u2ehi0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h1126, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1195_1, u0elo2, u2ehi0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              rcases p1195_3 (m.d 0 1) (by simp) with h1215 | h1215
                              · linarith only [h1215, h664, hlam]
                              · rcases p1195_3 (m.d 0 2) (by simp) with h1217 | h1217
                                · linarith only [h1124, h1217, hlam]
                                · linarith only [h0, h1217, hlam]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1195_1, u0elo3, u2ehi0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h1128, hlam, p1195_0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [hlam, p1195_0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h1126, h1128, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1195_1, u0elo2, u2ehi0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              rcases p1195_3 (m.d 0 1) (by simp) with h1224 | h1224
                              · linarith only [h1224, h813, hlam]
                              · rcases p1195_3 (m.d 0 2) (by simp) with h1226 | h1226
                                · linarith only [h1126, h1226, hlam]
                                · linarith only [h0, h1226, hlam]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1195_1, u0elo4, u2ehi0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h1129, hlam, p1195_0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h1130, hlam, p1195_1]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [hlam, p1195_0]
                          · rcases h0bigk with h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [hlam, p1233_0]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [h0, hlam, p1233_1]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [h282, hlam, p1233_0]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [h664, hlam, p1233_1]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [h813, hlam, p1233_1]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [h880, hc01, hc23, hlam, hphi, ht12, p1233_1]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [hlam, p1233_0]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [h880, hlam, p1233_0]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [h1124, hlam, p1233_1]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [h1126, hlam, p1233_0]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              rcases p1233_3 (m.d 0 1) (by simp) with h1244 | h1244
                              · linarith only [h1244, h282, hlam]
                              · rcases p1233_3 (m.d 0 2) (by simp) with h1246 | h1246
                                · linarith only [h1246, h880, hlam]
                                · linarith only [h0, h1246, hlam]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1233_1, u0elo2, u2ehi0]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [hlam, p1233_0]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [h1130, h1194, hc34, hlam, hphi, ht0b, ht45, ht5b, p1233_1, u0elo2]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [h1126, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1233_1, u0elo2, u2ehi0]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              rcases p1233_3 (m.d 0 1) (by simp) with h1253 | h1253
                              · linarith only [h1253, h664, hlam]
                              · rcases p1233_3 (m.d 0 2) (by simp) with h1255 | h1255
                                · linarith only [h1124, h1255, hlam]
                                · linarith only [h0, h1255, hlam]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1233_1, u0elo3, u2ehi0]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [h1128, hlam, p1233_0]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [hlam, p1233_0]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [h1126, h1128, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1233_1, u0elo2, u2ehi0]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              rcases p1233_3 (m.d 0 1) (by simp) with h1262 | h1262
                              · linarith only [h1262, h813, hlam]
                              · rcases p1233_3 (m.d 0 2) (by simp) with h1264 | h1264
                                · linarith only [h1126, h1264, hlam]
                                · linarith only [h0, h1264, hlam]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1233_1, u0elo4, u2ehi0]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [h1129, hlam, p1233_0]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [h1130, hlam, p1233_1]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [hlam, p1233_0]
                        · linarith only [h1124, h1193, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                      · linarith only [h1192, h880, hc35, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h1191, h880, hc34, hlam, hphi, ht23, u2ehi0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1274 | h1274
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1275 | h1275
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1276 | h1276
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1277 | h1277
                        · linarith only [h1130, h1274, h1275, h1277, h664, hc01, hc12, hlam, hphi]
                        · linarith only [h1124, h1277, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                      · linarith only [h1124, h1129, h1275, h1276, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi0]
                    · linarith only [h1275, h880, hc34, hlam, hphi, ht23, u2ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1282 | h1282
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1283 | h1283
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1284 | h1284
                        · linarith only [h1124, h1130, h1284, hc24, hlam, hphi, u2ehi0]
                        · linarith only [h1124, h1284, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                      · linarith only [h0, h1129, h1274, h1283, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h1128, h1282, h880, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi0]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1289 | h1289
                · linarith only [h1128, h1129, h1289, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1291 | h1291
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1292 | h1292
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1293 | h1293
                      · linarith only [h1128, h1129, h1291, h1293, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h1293, h880, hc35, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h1292, h880, hc34, hlam, hphi, ht23, u2ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1297 | h1297
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1298 | h1298
                      · linarith only [h1124, h1128, h1129, h1298, hc23, hlam, hphi, u2ehi0]
                      · linarith only [h1298, h880, hc35, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h0, h1128, h1291, h1297, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1302 | h1302
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1303 | h1303
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1304 | h1304
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1305 | h1305
                    · linarith only [h1128, h1302, h1304, h1305, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h1305, h880, hc34, hlam, hphi, ht23, u2ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1308 | h1308
                    · linarith only [h1126, h1128, h1302, h1308, hc23, hlam, hphi, u2ehi0]
                    · linarith only [h1308, h880, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h1128, h1302, h1303, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1312 | h1312
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1313 | h1313
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1314 | h1314
                    · linarith only [h1128, h1313, h1314, h282, hc01, hc12, hlam, hphi]
                    · linarith only [h1314, h880, hc34, hlam, hphi, ht23, u2ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1317 | h1317
                    · linarith only [h1128, h1317, h880, hc23, hlam, hphi, u2ehi0]
                    · linarith only [h1317, h880, hc34, hlam, hphi, ht23, u2ehi0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1320 | h1320
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1321 | h1321
                    · linarith only [h1128, h1320, h1321, h880, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h1321, h880, hc34, hlam, hphi, ht23, u2ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1324 | h1324
                    · linarith only [h1128, h1324, h880, hc23, hlam, hphi, u2ehi0]
                    · linarith only [h1324, h880, hc34, hlam, hphi, ht23, u2ehi0]

theorem r1l7_20_12_14_M_LI_L_R_L_I_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2ehi := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h282 | h282
  · exact r1l7_20_12_14_M_LI_L_R_L_I_x1_x0 m hb0 hb2 hb4 h0 h282
  · exact r1l7_20_12_14_M_LI_L_R_L_I_x1_x1 m hb0 hb2 hb4 h0 h282

theorem r1l7_20_12_14_M_LI_L_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2ehi := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_14_M_LI_L_R_L_I_x0 m hb0 hb2 hb4 h0
  · exact r1l7_20_12_14_M_LI_L_R_L_I_x1 m hb0 hb2 hb4 h0

end R2N4
