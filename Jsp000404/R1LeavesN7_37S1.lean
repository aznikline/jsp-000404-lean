import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_37S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7470000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h656 | h656
  · rcases m.htr 0 2 5 (by decide) (by decide) with h657 | h657
    · linarith only [h4, h657, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h659 | h659
      · rcases m.htr 0 4 5 (by decide) (by decide) with h660 | h660
        · linarith only [h4, h656, h660, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h662 | h662
          · linarith only [h0, h4, h656, h662, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h664 | h664
            · rcases m.htr 1 2 5 (by decide) (by decide) with h665 | h665
              · linarith only [h0, h3, h4, h657, h665, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h667 | h667
                · rcases m.htr 1 3 5 (by decide) (by decide) with h668 | h668
                  · linarith only [h1, h668, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h670 | h670
                    · linarith only [h2, h660, h670, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h672 | h672
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h673 | h673
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h674 | h674
                          · linarith only [h660, h662, h664, h668, h673, h674, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h676 | h676
                            · linarith only [h657, h662, h664, h668, h672, h673, h674, h676, hc02, hc23, hlam, hphi]
                            · rcases h1bigk with h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [hlam, p678_0]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                rcases p678_3 (m.d 0 1) (by simp) with h680 | h680
                                · rcases p678_3 (m.d 1 2) (by simp) with h681 | h681
                                  · linarith only [h681, hlam, p678_0]
                                  · rcases p678_3 (m.d 1 3) (by simp) with h683 | h683
                                    · linarith only [h1, h683, hlam]
                                    · linarith only [h662, h683, hlam]
                                · linarith only [h680, hlam, p678_0]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                rcases p678_3 (m.d 0 1) (by simp) with h687 | h687
                                · rcases p678_3 (m.d 1 2) (by simp) with h688 | h688
                                  · linarith only [h0, h688, hlam]
                                  · rcases p678_3 (m.d 1 3) (by simp) with h690 | h690
                                    · linarith only [h690, hlam, p678_0]
                                    · rcases p678_3 (m.d 1 4) (by simp) with h692 | h692
                                      · linarith only [h2, h692, hlam]
                                      · rcases p678_3 (m.d 1 5) (by simp) with h694 | h694
                                        · linarith only [h3, h694, hlam]
                                        · linarith only [h668, h694, hlam]
                                · linarith only [h687, hlam, p678_0]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                rcases p678_3 (m.d 0 1) (by simp) with h698 | h698
                                · rcases p678_3 (m.d 1 2) (by simp) with h699 | h699
                                  · linarith only [h0, h699, hlam]
                                  · linarith only [h664, h699, hlam]
                                · linarith only [h698, hlam, p678_0]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht5b, p678_1, u5ehi1]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [h0, hlam, p678_0]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [hlam, p678_0]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [h662, hlam, p678_1]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [h662, h668, h673, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p678_1]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [h665, hlam, p678_1]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [h1, hlam, p678_0]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [h668, h673, hc12, hc23, hlam, hphi, p678_1]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [hlam, p678_0]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [h664, h668, h672, h673, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p678_1]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [h668, hlam, p678_1]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [h2, hlam, p678_0]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [h664, hlam, p678_0]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [h667, hlam, p678_1]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [hlam, p678_0]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [h670, hlam, p678_1]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [h3, hlam, p678_0]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [h3, h664, h672, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p678_1]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [h3, h657, h662, h664, h672, h674, hc34, hc45, hlam, hphi, p678_1]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                rcases p678_3 (m.d 0 1) (by simp) with h722 | h722
                                · rcases p678_3 (m.d 1 2) (by simp) with h723 | h723
                                  · linarith only [h665, h723, hlam]
                                  · linarith only [h664, h723, hlam]
                                · linarith only [h2, h722, hlam]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [hlam, p678_0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h728 | h728
                          · linarith only [h0, h664, h728, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h730 | h730
                            · linarith only [h0, h4, h664, h672, h673, h728, h730, hlam]
                            · linarith only [h0, h4, h664, h673, h730, hc24, hc45, hlam, hphi]
                      · linarith only [h4, h659, h672, hlam]
                · linarith only [h659, h660, h662, h664, h667, hc24, hc45, hlam, hphi]
            · linarith only [h4, h656, h664, hc12, hc23, hlam, hphi]
      · linarith only [h4, h656, h659, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h737 | h737
    · linarith only [h656, h737, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h739 | h739
      · rcases m.htr 0 4 5 (by decide) (by decide) with h740 | h740
        · rcases m.htr 1 2 3 (by decide) (by decide) with h741 | h741
          · linarith only [h0, h4, h741, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h743 | h743
            · linarith only [h0, h656, h743, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h745 | h745
              · linarith only [h0, h737, h745, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h747 | h747
                · rcases m.htr 1 3 5 (by decide) (by decide) with h748 | h748
                  · linarith only [h1, h748, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h750 | h750
                    · linarith only [h2, h750, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h752 | h752
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h753 | h753
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h754 | h754
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h755 | h755
                            · linarith only [h747, h750, h755, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                            · rcases h1bigk with h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c | h757c
                              · have p757_0 := h757c.1
                                have p757_1 := h757c.2.1
                                have p757_2 := h757c.2.2.1
                                have p757_3 := h757c.2.2.2
                                linarith only [hlam, p757_0]
                              · have p757_0 := h757c.1
                                have p757_1 := h757c.2.1
                                have p757_2 := h757c.2.2.1
                                have p757_3 := h757c.2.2.2
                                rcases p757_3 (m.d 0 1) (by simp) with h759 | h759
                                · rcases p757_3 (m.d 1 2) (by simp) with h760 | h760
                                  · linarith only [h760, hlam, p757_0]
                                  · rcases p757_3 (m.d 1 3) (by simp) with h762 | h762
                                    · linarith only [h1, h762, hlam]
                                    · linarith only [h741, h762, hlam]
                                · linarith only [h759, hlam, p757_0]
                              · have p757_0 := h757c.1
                                have p757_1 := h757c.2.1
                                have p757_2 := h757c.2.2.1
                                have p757_3 := h757c.2.2.2
                                rcases p757_3 (m.d 0 1) (by simp) with h766 | h766
                                · rcases p757_3 (m.d 1 2) (by simp) with h767 | h767
                                  · linarith only [h0, h767, hlam]
                                  · rcases p757_3 (m.d 1 3) (by simp) with h769 | h769
                                    · linarith only [h769, hlam, p757_0]
                                    · rcases p757_3 (m.d 1 4) (by simp) with h771 | h771
                                      · linarith only [h2, h771, hlam]
                                      · rcases p757_3 (m.d 1 5) (by simp) with h773 | h773
                                        · linarith only [h3, h773, hlam]
                                        · linarith only [h748, h773, hlam]
                                · linarith only [h766, hlam, p757_0]
                              · have p757_0 := h757c.1
                                have p757_1 := h757c.2.1
                                have p757_2 := h757c.2.2.1
                                have p757_3 := h757c.2.2.2
                                rcases p757_3 (m.d 0 1) (by simp) with h777 | h777
                                · rcases p757_3 (m.d 1 2) (by simp) with h778 | h778
                                  · linarith only [h0, h778, hlam]
                                  · rcases p757_3 (m.d 1 3) (by simp) with h780 | h780
                                    · linarith only [h1, h780, hlam]
                                    · linarith only [h747, h780, hlam]
                                · linarith only [h777, hlam, p757_0]
                              · have p757_0 := h757c.1
                                have p757_1 := h757c.2.1
                                have p757_2 := h757c.2.2.1
                                have p757_3 := h757c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht5b, p757_1, u5ehi1]
                              · have p757_0 := h757c.1
                                have p757_1 := h757c.2.1
                                have p757_2 := h757c.2.2.1
                                have p757_3 := h757c.2.2.2
                                linarith only [h0, hlam, p757_0]
                              · have p757_0 := h757c.1
                                have p757_1 := h757c.2.1
                                have p757_2 := h757c.2.2.1
                                have p757_3 := h757c.2.2.2
                                linarith only [hlam, p757_0]
                              · have p757_0 := h757c.1
                                have p757_1 := h757c.2.1
                                have p757_2 := h757c.2.2.1
                                have p757_3 := h757c.2.2.2
                                linarith only [h741, hlam, p757_1]
                              · have p757_0 := h757c.1
                                have p757_1 := h757c.2.1
                                have p757_2 := h757c.2.2.1
                                have p757_3 := h757c.2.2.2
                                linarith only [h743, hlam, p757_1]
                              · have p757_0 := h757c.1
                                have p757_1 := h757c.2.1
                                have p757_2 := h757c.2.2.1
                                have p757_3 := h757c.2.2.2
                                linarith only [h745, hlam, p757_1]
                              · have p757_0 := h757c.1
                                have p757_1 := h757c.2.1
                                have p757_2 := h757c.2.2.1
                                have p757_3 := h757c.2.2.2
                                linarith only [h1, hlam, p757_0]
                              · have p757_0 := h757c.1
                                have p757_1 := h757c.2.1
                                have p757_2 := h757c.2.2.1
                                have p757_3 := h757c.2.2.2
                                linarith only [h739, h740, h748, h755, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p757_1]
                              · have p757_0 := h757c.1
                                have p757_1 := h757c.2.1
                                have p757_2 := h757c.2.2.1
                                have p757_3 := h757c.2.2.2
                                linarith only [hlam, p757_0]
                              · have p757_0 := h757c.1
                                have p757_1 := h757c.2.1
                                have p757_2 := h757c.2.2.1
                                have p757_3 := h757c.2.2.2
                                linarith only [h739, h740, h748, h755, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b, p757_1]
                              · have p757_0 := h757c.1
                                have p757_1 := h757c.2.1
                                have p757_2 := h757c.2.2.1
                                have p757_3 := h757c.2.2.2
                                linarith only [h748, hlam, p757_1]
                              · have p757_0 := h757c.1
                                have p757_1 := h757c.2.1
                                have p757_2 := h757c.2.2.1
                                have p757_3 := h757c.2.2.2
                                linarith only [h2, hlam, p757_0]
                              · have p757_0 := h757c.1
                                have p757_1 := h757c.2.1
                                have p757_2 := h757c.2.2.1
                                have p757_3 := h757c.2.2.2
                                linarith only [h4, h739, h740, h747, h748, h755, hc12, hc23, hlam, hphi, p757_1]
                              · have p757_0 := h757c.1
                                have p757_1 := h757c.2.1
                                have p757_2 := h757c.2.2.1
                                have p757_3 := h757c.2.2.2
                                linarith only [h747, hlam, p757_1]
                              · have p757_0 := h757c.1
                                have p757_1 := h757c.2.1
                                have p757_2 := h757c.2.2.1
                                have p757_3 := h757c.2.2.2
                                linarith only [hlam, p757_0]
                              · have p757_0 := h757c.1
                                have p757_1 := h757c.2.1
                                have p757_2 := h757c.2.2.1
                                have p757_3 := h757c.2.2.2
                                linarith only [h750, hlam, p757_1]
                              · have p757_0 := h757c.1
                                have p757_1 := h757c.2.1
                                have p757_2 := h757c.2.2.1
                                have p757_3 := h757c.2.2.2
                                linarith only [h3, hlam, p757_0]
                              · have p757_0 := h757c.1
                                have p757_1 := h757c.2.1
                                have p757_2 := h757c.2.2.1
                                have p757_3 := h757c.2.2.2
                                linarith only [h4, h739, h740, h748, h755, hc12, hc23, hlam, hphi, p757_1]
                              · have p757_0 := h757c.1
                                have p757_1 := h757c.2.1
                                have p757_2 := h757c.2.2.1
                                have p757_3 := h757c.2.2.2
                                linarith only [h4, h739, h740, h747, h748, h755, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p757_1]
                              · have p757_0 := h757c.1
                                have p757_1 := h757c.2.1
                                have p757_2 := h757c.2.2.1
                                have p757_3 := h757c.2.2.2
                                linarith only [h4, h739, h740, h743, h748, h755, hc12, hc23, hlam, hphi, p757_1]
                              · have p757_0 := h757c.1
                                have p757_1 := h757c.2.1
                                have p757_2 := h757c.2.2.1
                                have p757_3 := h757c.2.2.2
                                linarith only [hlam, p757_0]
                          · linarith only [h4, h656, h739, h740, h754, hc02, hc23, hlam, hphi]
                        · linarith only [h4, h739, h740, h750, h753, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                      · linarith only [h4, h739, h740, h747, h750, h752, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h808 | h808
                  · linarith only [h1, h739, h747, h808, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h810 | h810
                    · linarith only [h2, h810, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h812 | h812
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h813 | h813
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h814 | h814
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h815 | h815
                            · linarith only [h4, h739, h810, h815, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                            · linarith only [h656, h740, h741, h747, h815, hc12, hc24, hlam, hphi]
                          · linarith only [h0, h4, h656, h739, h740, h814, hc12, hc23, hlam, hphi]
                        · linarith only [h4, h739, h740, h810, h813, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                      · linarith only [h4, h739, h740, h810, h812, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h821 | h821
          · linarith only [h0, h4, h821, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h823 | h823
            · linarith only [h0, h656, h823, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h825 | h825
              · linarith only [h0, h737, h825, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h827 | h827
                · rcases m.htr 1 3 5 (by decide) (by decide) with h828 | h828
                  · linarith only [h1, h828, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h830 | h830
                    · linarith only [h2, h830, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h832 | h832
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h833 | h833
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h834 | h834
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h835 | h835
                            · linarith only [h740, h827, h828, h833, h835, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases h1bigk with h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c
                              · have p837_0 := h837c.1
                                have p837_1 := h837c.2.1
                                have p837_2 := h837c.2.2.1
                                have p837_3 := h837c.2.2.2
                                linarith only [hlam, p837_0]
                              · have p837_0 := h837c.1
                                have p837_1 := h837c.2.1
                                have p837_2 := h837c.2.2.1
                                have p837_3 := h837c.2.2.2
                                rcases p837_3 (m.d 0 1) (by simp) with h839 | h839
                                · rcases p837_3 (m.d 1 2) (by simp) with h840 | h840
                                  · linarith only [h840, hlam, p837_0]
                                  · rcases p837_3 (m.d 1 3) (by simp) with h842 | h842
                                    · linarith only [h1, h842, hlam]
                                    · linarith only [h821, h842, hlam]
                                · linarith only [h839, hlam, p837_0]
                              · have p837_0 := h837c.1
                                have p837_1 := h837c.2.1
                                have p837_2 := h837c.2.2.1
                                have p837_3 := h837c.2.2.2
                                rcases p837_3 (m.d 0 1) (by simp) with h846 | h846
                                · rcases p837_3 (m.d 1 2) (by simp) with h847 | h847
                                  · linarith only [h0, h847, hlam]
                                  · rcases p837_3 (m.d 1 3) (by simp) with h849 | h849
                                    · linarith only [h849, hlam, p837_0]
                                    · rcases p837_3 (m.d 1 4) (by simp) with h851 | h851
                                      · linarith only [h2, h851, hlam]
                                      · rcases p837_3 (m.d 1 5) (by simp) with h853 | h853
                                        · linarith only [h3, h853, hlam]
                                        · linarith only [h828, h853, hlam]
                                · linarith only [h846, hlam, p837_0]
                              · have p837_0 := h837c.1
                                have p837_1 := h837c.2.1
                                have p837_2 := h837c.2.2.1
                                have p837_3 := h837c.2.2.2
                                rcases p837_3 (m.d 0 1) (by simp) with h857 | h857
                                · rcases p837_3 (m.d 1 2) (by simp) with h858 | h858
                                  · linarith only [h0, h858, hlam]
                                  · rcases p837_3 (m.d 1 3) (by simp) with h860 | h860
                                    · linarith only [h1, h860, hlam]
                                    · linarith only [h827, h860, hlam]
                                · linarith only [h857, hlam, p837_0]
                              · have p837_0 := h837c.1
                                have p837_1 := h837c.2.1
                                have p837_2 := h837c.2.2.1
                                have p837_3 := h837c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht5b, p837_1, u5ehi1]
                              · have p837_0 := h837c.1
                                have p837_1 := h837c.2.1
                                have p837_2 := h837c.2.2.1
                                have p837_3 := h837c.2.2.2
                                linarith only [h0, hlam, p837_0]
                              · have p837_0 := h837c.1
                                have p837_1 := h837c.2.1
                                have p837_2 := h837c.2.2.1
                                have p837_3 := h837c.2.2.2
                                linarith only [hlam, p837_0]
                              · have p837_0 := h837c.1
                                have p837_1 := h837c.2.1
                                have p837_2 := h837c.2.2.1
                                have p837_3 := h837c.2.2.2
                                linarith only [h821, hlam, p837_1]
                              · have p837_0 := h837c.1
                                have p837_1 := h837c.2.1
                                have p837_2 := h837c.2.2.1
                                have p837_3 := h837c.2.2.2
                                linarith only [h823, hlam, p837_1]
                              · have p837_0 := h837c.1
                                have p837_1 := h837c.2.1
                                have p837_2 := h837c.2.2.1
                                have p837_3 := h837c.2.2.2
                                linarith only [h825, hlam, p837_1]
                              · have p837_0 := h837c.1
                                have p837_1 := h837c.2.1
                                have p837_2 := h837c.2.2.1
                                have p837_3 := h837c.2.2.2
                                linarith only [h1, hlam, p837_0]
                              · have p837_0 := h837c.1
                                have p837_1 := h837c.2.1
                                have p837_2 := h837c.2.2.1
                                have p837_3 := h837c.2.2.2
                                linarith only [h828, h832, h834, h835, hc12, hc23, hlam, hphi, p837_1]
                              · have p837_0 := h837c.1
                                have p837_1 := h837c.2.1
                                have p837_2 := h837c.2.2.1
                                have p837_3 := h837c.2.2.2
                                linarith only [hlam, p837_0]
                              · have p837_0 := h837c.1
                                have p837_1 := h837c.2.1
                                have p837_2 := h837c.2.2.1
                                have p837_3 := h837c.2.2.2
                                linarith only [h823, h828, h832, h834, h835, hc12, hc23, hlam, hphi, p837_1]
                              · have p837_0 := h837c.1
                                have p837_1 := h837c.2.1
                                have p837_2 := h837c.2.2.1
                                have p837_3 := h837c.2.2.2
                                linarith only [h828, hlam, p837_1]
                              · have p837_0 := h837c.1
                                have p837_1 := h837c.2.1
                                have p837_2 := h837c.2.2.1
                                have p837_3 := h837c.2.2.2
                                linarith only [h2, hlam, p837_0]
                              · have p837_0 := h837c.1
                                have p837_1 := h837c.2.1
                                have p837_2 := h837c.2.2.1
                                have p837_3 := h837c.2.2.2
                                linarith only [h2, h740, h832, h834, hc12, hc23, hlam, hphi, p837_1]
                              · have p837_0 := h837c.1
                                have p837_1 := h837c.2.1
                                have p837_2 := h837c.2.2.1
                                have p837_3 := h837c.2.2.2
                                linarith only [h827, hlam, p837_1]
                              · have p837_0 := h837c.1
                                have p837_1 := h837c.2.1
                                have p837_2 := h837c.2.2.1
                                have p837_3 := h837c.2.2.2
                                linarith only [hlam, p837_0]
                              · have p837_0 := h837c.1
                                have p837_1 := h837c.2.1
                                have p837_2 := h837c.2.2.1
                                have p837_3 := h837c.2.2.2
                                linarith only [h830, hlam, p837_1]
                              · have p837_0 := h837c.1
                                have p837_1 := h837c.2.1
                                have p837_2 := h837c.2.2.1
                                have p837_3 := h837c.2.2.2
                                linarith only [h3, hlam, p837_0]
                              · have p837_0 := h837c.1
                                have p837_1 := h837c.2.1
                                have p837_2 := h837c.2.2.1
                                have p837_3 := h837c.2.2.2
                                linarith only [h3, h740, h832, h834, hc12, hc23, hlam, hphi, p837_1]
                              · have p837_0 := h837c.1
                                have p837_1 := h837c.2.1
                                have p837_2 := h837c.2.2.1
                                have p837_3 := h837c.2.2.2
                                linarith only [h3, h740, h827, h832, h834, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p837_1]
                              · have p837_0 := h837c.1
                                have p837_1 := h837c.2.1
                                have p837_2 := h837c.2.2.1
                                have p837_3 := h837c.2.2.2
                                linarith only [h3, h740, h823, h832, h834, hc12, hc23, hlam, hphi, p837_1]
                              · have p837_0 := h837c.1
                                have p837_1 := h837c.2.1
                                have p837_2 := h837c.2.2.1
                                have p837_3 := h837c.2.2.2
                                linarith only [hlam, p837_0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h885 | h885
                            · linarith only [h1, h737, h827, h834, h885, hc03, hlam, hphi, ht0b, ht5b, u5ehi0]
                            · rcases h1bigk with h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c
                              · have p887_0 := h887c.1
                                have p887_1 := h887c.2.1
                                have p887_2 := h887c.2.2.1
                                have p887_3 := h887c.2.2.2
                                linarith only [hlam, p887_0]
                              · have p887_0 := h887c.1
                                have p887_1 := h887c.2.1
                                have p887_2 := h887c.2.2.1
                                have p887_3 := h887c.2.2.2
                                rcases p887_3 (m.d 0 1) (by simp) with h889 | h889
                                · rcases p887_3 (m.d 1 2) (by simp) with h890 | h890
                                  · linarith only [h890, hlam, p887_0]
                                  · rcases p887_3 (m.d 1 3) (by simp) with h892 | h892
                                    · linarith only [h1, h892, hlam]
                                    · linarith only [h821, h892, hlam]
                                · linarith only [h889, hlam, p887_0]
                              · have p887_0 := h887c.1
                                have p887_1 := h887c.2.1
                                have p887_2 := h887c.2.2.1
                                have p887_3 := h887c.2.2.2
                                rcases p887_3 (m.d 0 1) (by simp) with h896 | h896
                                · rcases p887_3 (m.d 1 2) (by simp) with h897 | h897
                                  · linarith only [h0, h897, hlam]
                                  · rcases p887_3 (m.d 1 3) (by simp) with h899 | h899
                                    · linarith only [h899, hlam, p887_0]
                                    · rcases p887_3 (m.d 1 4) (by simp) with h901 | h901
                                      · linarith only [h2, h901, hlam]
                                      · rcases p887_3 (m.d 1 5) (by simp) with h903 | h903
                                        · linarith only [h3, h903, hlam]
                                        · linarith only [h828, h903, hlam]
                                · linarith only [h896, hlam, p887_0]
                              · have p887_0 := h887c.1
                                have p887_1 := h887c.2.1
                                have p887_2 := h887c.2.2.1
                                have p887_3 := h887c.2.2.2
                                rcases p887_3 (m.d 0 1) (by simp) with h907 | h907
                                · rcases p887_3 (m.d 1 2) (by simp) with h908 | h908
                                  · linarith only [h0, h908, hlam]
                                  · rcases p887_3 (m.d 1 3) (by simp) with h910 | h910
                                    · linarith only [h1, h910, hlam]
                                    · linarith only [h827, h910, hlam]
                                · linarith only [h907, hlam, p887_0]
                              · have p887_0 := h887c.1
                                have p887_1 := h887c.2.1
                                have p887_2 := h887c.2.2.1
                                have p887_3 := h887c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht5b, p887_1, u5ehi1]
                              · have p887_0 := h887c.1
                                have p887_1 := h887c.2.1
                                have p887_2 := h887c.2.2.1
                                have p887_3 := h887c.2.2.2
                                linarith only [h0, hlam, p887_0]
                              · have p887_0 := h887c.1
                                have p887_1 := h887c.2.1
                                have p887_2 := h887c.2.2.1
                                have p887_3 := h887c.2.2.2
                                linarith only [hlam, p887_0]
                              · have p887_0 := h887c.1
                                have p887_1 := h887c.2.1
                                have p887_2 := h887c.2.2.1
                                have p887_3 := h887c.2.2.2
                                linarith only [h821, hlam, p887_1]
                              · have p887_0 := h887c.1
                                have p887_1 := h887c.2.1
                                have p887_2 := h887c.2.2.1
                                have p887_3 := h887c.2.2.2
                                linarith only [h823, hlam, p887_1]
                              · have p887_0 := h887c.1
                                have p887_1 := h887c.2.1
                                have p887_2 := h887c.2.2.1
                                have p887_3 := h887c.2.2.2
                                linarith only [h825, hlam, p887_1]
                              · have p887_0 := h887c.1
                                have p887_1 := h887c.2.1
                                have p887_2 := h887c.2.2.1
                                have p887_3 := h887c.2.2.2
                                linarith only [h1, hlam, p887_0]
                              · have p887_0 := h887c.1
                                have p887_1 := h887c.2.1
                                have p887_2 := h887c.2.2.1
                                have p887_3 := h887c.2.2.2
                                linarith only [h828, h833, hc12, hc23, hlam, hphi, p887_1]
                              · have p887_0 := h887c.1
                                have p887_1 := h887c.2.1
                                have p887_2 := h887c.2.2.1
                                have p887_3 := h887c.2.2.2
                                linarith only [hlam, p887_0]
                              · have p887_0 := h887c.1
                                have p887_1 := h887c.2.1
                                have p887_2 := h887c.2.2.1
                                have p887_3 := h887c.2.2.2
                                linarith only [h823, h828, h833, hc12, hc23, hlam, hphi, p887_1]
                              · have p887_0 := h887c.1
                                have p887_1 := h887c.2.1
                                have p887_2 := h887c.2.2.1
                                have p887_3 := h887c.2.2.2
                                linarith only [h828, hlam, p887_1]
                              · have p887_0 := h887c.1
                                have p887_1 := h887c.2.1
                                have p887_2 := h887c.2.2.1
                                have p887_3 := h887c.2.2.2
                                linarith only [h2, hlam, p887_0]
                              · have p887_0 := h887c.1
                                have p887_1 := h887c.2.1
                                have p887_2 := h887c.2.2.1
                                have p887_3 := h887c.2.2.2
                                linarith only [h2, h656, h834, hc12, hc45, hlam, hphi, ht23, ht34, p887_1]
                              · have p887_0 := h887c.1
                                have p887_1 := h887c.2.1
                                have p887_2 := h887c.2.2.1
                                have p887_3 := h887c.2.2.2
                                linarith only [h827, hlam, p887_1]
                              · have p887_0 := h887c.1
                                have p887_1 := h887c.2.1
                                have p887_2 := h887c.2.2.1
                                have p887_3 := h887c.2.2.2
                                linarith only [hlam, p887_0]
                              · have p887_0 := h887c.1
                                have p887_1 := h887c.2.1
                                have p887_2 := h887c.2.2.1
                                have p887_3 := h887c.2.2.2
                                linarith only [h830, hlam, p887_1]
                              · have p887_0 := h887c.1
                                have p887_1 := h887c.2.1
                                have p887_2 := h887c.2.2.1
                                have p887_3 := h887c.2.2.2
                                linarith only [h3, hlam, p887_0]
                              · have p887_0 := h887c.1
                                have p887_1 := h887c.2.1
                                have p887_2 := h887c.2.2.1
                                have p887_3 := h887c.2.2.2
                                linarith only [h828, h833, hc12, hc23, hlam, hphi, p887_1]
                              · have p887_0 := h887c.1
                                have p887_1 := h887c.2.1
                                have p887_2 := h887c.2.2.1
                                have p887_3 := h887c.2.2.2
                                linarith only [h827, h828, h833, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p887_1]
                              · have p887_0 := h887c.1
                                have p887_1 := h887c.2.1
                                have p887_2 := h887c.2.2.1
                                have p887_3 := h887c.2.2.2
                                linarith only [h823, h828, h833, hc12, hc23, hlam, hphi, p887_1]
                              · have p887_0 := h887c.1
                                have p887_1 := h887c.2.1
                                have p887_2 := h887c.2.2.1
                                have p887_3 := h887c.2.2.2
                                linarith only [hlam, p887_0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h935 | h935
                          · linarith only [h740, h832, h833, h935, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h937 | h937
                            · linarith only [h827, h935, h937, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                            · rcases h1bigk with h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c
                              · have p939_0 := h939c.1
                                have p939_1 := h939c.2.1
                                have p939_2 := h939c.2.2.1
                                have p939_3 := h939c.2.2.2
                                linarith only [hlam, p939_0]
                              · have p939_0 := h939c.1
                                have p939_1 := h939c.2.1
                                have p939_2 := h939c.2.2.1
                                have p939_3 := h939c.2.2.2
                                rcases p939_3 (m.d 0 1) (by simp) with h941 | h941
                                · rcases p939_3 (m.d 1 2) (by simp) with h942 | h942
                                  · linarith only [h942, hlam, p939_0]
                                  · rcases p939_3 (m.d 1 3) (by simp) with h944 | h944
                                    · linarith only [h1, h944, hlam]
                                    · linarith only [h821, h944, hlam]
                                · linarith only [h941, hlam, p939_0]
                              · have p939_0 := h939c.1
                                have p939_1 := h939c.2.1
                                have p939_2 := h939c.2.2.1
                                have p939_3 := h939c.2.2.2
                                rcases p939_3 (m.d 0 1) (by simp) with h948 | h948
                                · rcases p939_3 (m.d 1 2) (by simp) with h949 | h949
                                  · linarith only [h0, h949, hlam]
                                  · rcases p939_3 (m.d 1 3) (by simp) with h951 | h951
                                    · linarith only [h951, hlam, p939_0]
                                    · rcases p939_3 (m.d 1 4) (by simp) with h953 | h953
                                      · linarith only [h2, h953, hlam]
                                      · rcases p939_3 (m.d 1 5) (by simp) with h955 | h955
                                        · linarith only [h3, h955, hlam]
                                        · linarith only [h828, h955, hlam]
                                · linarith only [h948, hlam, p939_0]
                              · have p939_0 := h939c.1
                                have p939_1 := h939c.2.1
                                have p939_2 := h939c.2.2.1
                                have p939_3 := h939c.2.2.2
                                rcases p939_3 (m.d 0 1) (by simp) with h959 | h959
                                · rcases p939_3 (m.d 1 2) (by simp) with h960 | h960
                                  · linarith only [h0, h960, hlam]
                                  · rcases p939_3 (m.d 1 3) (by simp) with h962 | h962
                                    · linarith only [h1, h962, hlam]
                                    · linarith only [h827, h962, hlam]
                                · linarith only [h959, hlam, p939_0]
                              · have p939_0 := h939c.1
                                have p939_1 := h939c.2.1
                                have p939_2 := h939c.2.2.1
                                have p939_3 := h939c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht5b, p939_1, u5ehi1]
                              · have p939_0 := h939c.1
                                have p939_1 := h939c.2.1
                                have p939_2 := h939c.2.2.1
                                have p939_3 := h939c.2.2.2
                                linarith only [h0, hlam, p939_0]
                              · have p939_0 := h939c.1
                                have p939_1 := h939c.2.1
                                have p939_2 := h939c.2.2.1
                                have p939_3 := h939c.2.2.2
                                linarith only [hlam, p939_0]
                              · have p939_0 := h939c.1
                                have p939_1 := h939c.2.1
                                have p939_2 := h939c.2.2.1
                                have p939_3 := h939c.2.2.2
                                linarith only [h821, hlam, p939_1]
                              · have p939_0 := h939c.1
                                have p939_1 := h939c.2.1
                                have p939_2 := h939c.2.2.1
                                have p939_3 := h939c.2.2.2
                                linarith only [h823, hlam, p939_1]
                              · have p939_0 := h939c.1
                                have p939_1 := h939c.2.1
                                have p939_2 := h939c.2.2.1
                                have p939_3 := h939c.2.2.2
                                linarith only [h825, hlam, p939_1]
                              · have p939_0 := h939c.1
                                have p939_1 := h939c.2.1
                                have p939_2 := h939c.2.2.1
                                have p939_3 := h939c.2.2.2
                                linarith only [h1, hlam, p939_0]
                              · have p939_0 := h939c.1
                                have p939_1 := h939c.2.1
                                have p939_2 := h939c.2.2.1
                                have p939_3 := h939c.2.2.2
                                linarith only [h1, h4, h833, h937, hc12, hc45, hlam, hphi, ht23, ht34, p939_1]
                              · have p939_0 := h939c.1
                                have p939_1 := h939c.2.1
                                have p939_2 := h939c.2.2.1
                                have p939_3 := h939c.2.2.2
                                linarith only [hlam, p939_0]
                              · have p939_0 := h939c.1
                                have p939_1 := h939c.2.1
                                have p939_2 := h939c.2.2.1
                                have p939_3 := h939c.2.2.2
                                linarith only [h1, h4, h823, h833, h937, hc12, hc45, hlam, hphi, ht23, ht34, p939_1]
                              · have p939_0 := h939c.1
                                have p939_1 := h939c.2.1
                                have p939_2 := h939c.2.2.1
                                have p939_3 := h939c.2.2.2
                                linarith only [h828, hlam, p939_1]
                              · have p939_0 := h939c.1
                                have p939_1 := h939c.2.1
                                have p939_2 := h939c.2.2.1
                                have p939_3 := h939c.2.2.2
                                linarith only [h2, hlam, p939_0]
                              · have p939_0 := h939c.1
                                have p939_1 := h939c.2.1
                                have p939_2 := h939c.2.2.1
                                have p939_3 := h939c.2.2.2
                                linarith only [h2, h4, h739, h833, h937, hc12, hc45, hlam, hphi, ht23, ht34, p939_1]
                              · have p939_0 := h939c.1
                                have p939_1 := h939c.2.1
                                have p939_2 := h939c.2.2.1
                                have p939_3 := h939c.2.2.2
                                linarith only [h827, hlam, p939_1]
                              · have p939_0 := h939c.1
                                have p939_1 := h939c.2.1
                                have p939_2 := h939c.2.2.1
                                have p939_3 := h939c.2.2.2
                                linarith only [hlam, p939_0]
                              · have p939_0 := h939c.1
                                have p939_1 := h939c.2.1
                                have p939_2 := h939c.2.2.1
                                have p939_3 := h939c.2.2.2
                                linarith only [h830, hlam, p939_1]
                              · have p939_0 := h939c.1
                                have p939_1 := h939c.2.1
                                have p939_2 := h939c.2.2.1
                                have p939_3 := h939c.2.2.2
                                linarith only [h3, hlam, p939_0]
                              · have p939_0 := h939c.1
                                have p939_1 := h939c.2.1
                                have p939_2 := h939c.2.2.1
                                have p939_3 := h939c.2.2.2
                                rcases p939_3 (m.d 0 1) (by simp) with h983 | h983
                                · rcases p939_3 (m.d 1 2) (by simp) with h984 | h984
                                  · linarith only [h825, h984, hlam]
                                  · rcases p939_3 (m.d 1 3) (by simp) with h986 | h986
                                    · linarith only [h828, h986, hlam]
                                    · linarith only [h821, h986, hlam]
                                · linarith only [h0, h983, hlam]
                              · have p939_0 := h939c.1
                                have p939_1 := h939c.2.1
                                have p939_2 := h939c.2.2.1
                                have p939_3 := h939c.2.2.2
                                linarith only [h3, h827, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p939_1]
                              · have p939_0 := h939c.1
                                have p939_1 := h939c.2.1
                                have p939_2 := h939c.2.2.1
                                have p939_3 := h939c.2.2.2
                                rcases p939_3 (m.d 0 1) (by simp) with h991 | h991
                                · rcases p939_3 (m.d 1 2) (by simp) with h992 | h992
                                  · linarith only [h825, h992, hlam]
                                  · rcases p939_3 (m.d 1 3) (by simp) with h994 | h994
                                    · linarith only [h828, h994, hlam]
                                    · linarith only [h827, h994, hlam]
                                · linarith only [h2, h991, hlam]
                              · have p939_0 := h939c.1
                                have p939_1 := h939c.2.1
                                have p939_2 := h939c.2.2.1
                                have p939_3 := h939c.2.2.2
                                linarith only [hlam, p939_0]
                      · linarith only [h0, h1, h4, h827, h832, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1000 | h1000
                  · linarith only [h1, h1000, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1002 | h1002
                    · linarith only [h1002, h739, h740, h827, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1004 | h1004
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1005 | h1005
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1006 | h1006
                          · linarith only [h1006, h739, h740, h821, h827, hc12, hc24, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1008 | h1008
                            · linarith only [h1006, h1008, h656, h739, hlam]
                            · rcases h1bigk with h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [hlam, p1010_0]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                rcases p1010_3 (m.d 0 1) (by simp) with h1012 | h1012
                                · rcases p1010_3 (m.d 1 2) (by simp) with h1013 | h1013
                                  · linarith only [h1013, hlam, p1010_0]
                                  · rcases p1010_3 (m.d 1 3) (by simp) with h1015 | h1015
                                    · linarith only [h1, h1015, hlam]
                                    · linarith only [h1015, h821, hlam]
                                · linarith only [h1012, hlam, p1010_0]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                rcases p1010_3 (m.d 0 1) (by simp) with h1019 | h1019
                                · rcases p1010_3 (m.d 1 2) (by simp) with h1020 | h1020
                                  · linarith only [h0, h1020, hlam]
                                  · rcases p1010_3 (m.d 1 3) (by simp) with h1022 | h1022
                                    · linarith only [h1022, hlam, p1010_0]
                                    · rcases p1010_3 (m.d 1 4) (by simp) with h1024 | h1024
                                      · linarith only [h1024, h2, hlam]
                                      · linarith only [h1024, h827, hlam]
                                · linarith only [h1019, hlam, p1010_0]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                rcases p1010_3 (m.d 0 1) (by simp) with h1028 | h1028
                                · rcases p1010_3 (m.d 1 2) (by simp) with h1029 | h1029
                                  · linarith only [h0, h1029, hlam]
                                  · rcases p1010_3 (m.d 1 3) (by simp) with h1031 | h1031
                                    · linarith only [h1, h1031, hlam]
                                    · rcases p1010_3 (m.d 1 4) (by simp) with h1033 | h1033
                                      · linarith only [h1033, hlam, p1010_0]
                                      · rcases p1010_3 (m.d 1 5) (by simp) with h1035 | h1035
                                        · linarith only [h1035, h3, hlam]
                                        · linarith only [h1002, h1035, hlam]
                                · linarith only [h1028, hlam, p1010_0]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht5b, p1010_1, u5ehi1]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [h0, hlam, p1010_0]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [hlam, p1010_0]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [h821, hlam, p1010_1]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [h823, hlam, p1010_1]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [h825, hlam, p1010_1]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [h1, hlam, p1010_0]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [h656, h739, h827, hc12, hc24, hlam, hphi, p1010_1]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [hlam, p1010_0]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [h827, hlam, p1010_0]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [h1000, hlam, p1010_1]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [h2, hlam, p1010_0]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [h1006, h656, h739, h827, hc12, hc45, hlam, hphi, ht23, ht34, p1010_1]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [h1006, h656, h739, h827, hc13, hc45, hlam, hphi, ht34, p1010_1]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [hlam, p1010_0]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [h1002, hlam, p1010_1]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [h3, hlam, p1010_0]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [h1000, h1005, hc12, hc23, hlam, hphi, p1010_1]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [h1000, h1005, h821, hc12, hc23, hlam, hphi, p1010_1]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [h1000, h1005, h823, hc12, hc23, hlam, hphi, p1010_1]
                              · have p1010_0 := h1010c.1
                                have p1010_1 := h1010c.2.1
                                have p1010_2 := h1010c.2.2.1
                                have p1010_3 := h1010c.2.2.2
                                linarith only [hlam, p1010_0]
                        · linarith only [h1005, h4, h739, h821, h827, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h1004, h4, h739, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1062 | h1062
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1063 | h1063
          · linarith only [h0, h1063, h4, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1065 | h1065
            · linarith only [h1062, h1065, h656, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1067 | h1067
              · linarith only [h0, h1067, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1069 | h1069
                · linarith only [h1, h1069, h739, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1071 | h1071
                  · linarith only [h1, h1071, h739, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1073 | h1073
                    · linarith only [h1073, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1075 | h1075
                      · linarith only [h1062, h1073, h1075, h739, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1077 | h1077
                        · linarith only [h1071, h1075, h1077, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1079 | h1079
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1080 | h1080
                            · rcases h1bigk with h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c
                              · have p1081_0 := h1081c.1
                                have p1081_1 := h1081c.2.1
                                have p1081_2 := h1081c.2.2.1
                                have p1081_3 := h1081c.2.2.2
                                linarith only [hlam, p1081_0]
                              · have p1081_0 := h1081c.1
                                have p1081_1 := h1081c.2.1
                                have p1081_2 := h1081c.2.2.1
                                have p1081_3 := h1081c.2.2.2
                                rcases p1081_3 (m.d 0 1) (by simp) with h1083 | h1083
                                · rcases p1081_3 (m.d 1 2) (by simp) with h1084 | h1084
                                  · linarith only [h1084, hlam, p1081_0]
                                  · rcases p1081_3 (m.d 1 3) (by simp) with h1086 | h1086
                                    · linarith only [h1, h1086, hlam]
                                    · linarith only [h1063, h1086, hlam]
                                · linarith only [h1083, hlam, p1081_0]
                              · have p1081_0 := h1081c.1
                                have p1081_1 := h1081c.2.1
                                have p1081_2 := h1081c.2.2.1
                                have p1081_3 := h1081c.2.2.2
                                rcases p1081_3 (m.d 0 1) (by simp) with h1090 | h1090
                                · rcases p1081_3 (m.d 1 2) (by simp) with h1091 | h1091
                                  · linarith only [h0, h1091, hlam]
                                  · rcases p1081_3 (m.d 1 3) (by simp) with h1093 | h1093
                                    · linarith only [h1093, hlam, p1081_0]
                                    · rcases p1081_3 (m.d 1 4) (by simp) with h1095 | h1095
                                      · linarith only [h1095, h2, hlam]
                                      · linarith only [h1069, h1095, hlam]
                                · linarith only [h1090, hlam, p1081_0]
                              · have p1081_0 := h1081c.1
                                have p1081_1 := h1081c.2.1
                                have p1081_2 := h1081c.2.2.1
                                have p1081_3 := h1081c.2.2.2
                                rcases p1081_3 (m.d 0 1) (by simp) with h1099 | h1099
                                · rcases p1081_3 (m.d 1 2) (by simp) with h1100 | h1100
                                  · linarith only [h0, h1100, hlam]
                                  · rcases p1081_3 (m.d 1 3) (by simp) with h1102 | h1102
                                    · linarith only [h1, h1102, hlam]
                                    · rcases p1081_3 (m.d 1 4) (by simp) with h1104 | h1104
                                      · linarith only [h1104, hlam, p1081_0]
                                      · rcases p1081_3 (m.d 1 5) (by simp) with h1106 | h1106
                                        · linarith only [h1106, h3, hlam]
                                        · linarith only [h1073, h1106, hlam]
                                · linarith only [h1099, hlam, p1081_0]
                              · have p1081_0 := h1081c.1
                                have p1081_1 := h1081c.2.1
                                have p1081_2 := h1081c.2.2.1
                                have p1081_3 := h1081c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht5b, p1081_1, u5ehi1]
                              · have p1081_0 := h1081c.1
                                have p1081_1 := h1081c.2.1
                                have p1081_2 := h1081c.2.2.1
                                have p1081_3 := h1081c.2.2.2
                                linarith only [h0, hlam, p1081_0]
                              · have p1081_0 := h1081c.1
                                have p1081_1 := h1081c.2.1
                                have p1081_2 := h1081c.2.2.1
                                have p1081_3 := h1081c.2.2.2
                                linarith only [hlam, p1081_0]
                              · have p1081_0 := h1081c.1
                                have p1081_1 := h1081c.2.1
                                have p1081_2 := h1081c.2.2.1
                                have p1081_3 := h1081c.2.2.2
                                linarith only [h1063, hlam, p1081_1]
                              · have p1081_0 := h1081c.1
                                have p1081_1 := h1081c.2.1
                                have p1081_2 := h1081c.2.2.1
                                have p1081_3 := h1081c.2.2.2
                                linarith only [h1065, hlam, p1081_1]
                              · have p1081_0 := h1081c.1
                                have p1081_1 := h1081c.2.1
                                have p1081_2 := h1081c.2.2.1
                                have p1081_3 := h1081c.2.2.2
                                linarith only [h1067, hlam, p1081_1]
                              · have p1081_0 := h1081c.1
                                have p1081_1 := h1081c.2.1
                                have p1081_2 := h1081c.2.2.1
                                have p1081_3 := h1081c.2.2.2
                                linarith only [h1, hlam, p1081_0]
                              · have p1081_0 := h1081c.1
                                have p1081_1 := h1081c.2.1
                                have p1081_2 := h1081c.2.2.1
                                have p1081_3 := h1081c.2.2.2
                                linarith only [h1062, h1069, h1073, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1081_1]
                              · have p1081_0 := h1081c.1
                                have p1081_1 := h1081c.2.1
                                have p1081_2 := h1081c.2.2.1
                                have p1081_3 := h1081c.2.2.2
                                linarith only [hlam, p1081_0]
                              · have p1081_0 := h1081c.1
                                have p1081_1 := h1081c.2.1
                                have p1081_2 := h1081c.2.2.1
                                have p1081_3 := h1081c.2.2.2
                                linarith only [h1069, hlam, p1081_0]
                              · have p1081_0 := h1081c.1
                                have p1081_1 := h1081c.2.1
                                have p1081_2 := h1081c.2.2.1
                                have p1081_3 := h1081c.2.2.2
                                linarith only [h1071, hlam, p1081_1]
                              · have p1081_0 := h1081c.1
                                have p1081_1 := h1081c.2.1
                                have p1081_2 := h1081c.2.2.1
                                have p1081_3 := h1081c.2.2.2
                                linarith only [h2, hlam, p1081_0]
                              · have p1081_0 := h1081c.1
                                have p1081_1 := h1081c.2.1
                                have p1081_2 := h1081c.2.2.1
                                have p1081_3 := h1081c.2.2.2
                                linarith only [h1062, h1073, h739, hc12, hc34, hlam, hphi, ht23, p1081_1]
                              · have p1081_0 := h1081c.1
                                have p1081_1 := h1081c.2.1
                                have p1081_2 := h1081c.2.2.1
                                have p1081_3 := h1081c.2.2.2
                                linarith only [h1062, h1073, h739, hc13, hc34, hlam, hphi, p1081_1]
                              · have p1081_0 := h1081c.1
                                have p1081_1 := h1081c.2.1
                                have p1081_2 := h1081c.2.2.1
                                have p1081_3 := h1081c.2.2.2
                                linarith only [hlam, p1081_0]
                              · have p1081_0 := h1081c.1
                                have p1081_1 := h1081c.2.1
                                have p1081_2 := h1081c.2.2.1
                                have p1081_3 := h1081c.2.2.2
                                linarith only [h1073, hlam, p1081_1]
                              · have p1081_0 := h1081c.1
                                have p1081_1 := h1081c.2.1
                                have p1081_2 := h1081c.2.2.1
                                have p1081_3 := h1081c.2.2.2
                                linarith only [h3, hlam, p1081_0]
                              · have p1081_0 := h1081c.1
                                have p1081_1 := h1081c.2.1
                                have p1081_2 := h1081c.2.2.1
                                have p1081_3 := h1081c.2.2.2
                                linarith only [h1062, h1073, h739, hc12, hc34, hlam, hphi, ht23, p1081_1]
                              · have p1081_0 := h1081c.1
                                have p1081_1 := h1081c.2.1
                                have p1081_2 := h1081c.2.2.1
                                have p1081_3 := h1081c.2.2.2
                                linarith only [h1062, h1063, h1073, h739, hc12, hc34, hlam, hphi, ht23, p1081_1]
                              · have p1081_0 := h1081c.1
                                have p1081_1 := h1081c.2.1
                                have p1081_2 := h1081c.2.2.1
                                have p1081_3 := h1081c.2.2.2
                                linarith only [h1062, h1065, h1073, h739, hc12, hc34, hlam, hphi, ht23, p1081_1]
                              · have p1081_0 := h1081c.1
                                have p1081_1 := h1081c.2.1
                                have p1081_2 := h1081c.2.2.1
                                have p1081_3 := h1081c.2.2.2
                                linarith only [hlam, p1081_0]
                            · linarith only [h1062, h1075, h1080, h656, hlam]
                          · linarith only [h1062, h1079, h656, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1133 | h1133
          · linarith only [h0, h1133, h4, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1135 | h1135
            · linarith only [h0, h1135, h656, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1137 | h1137
              · linarith only [h0, h1137, h737, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1139 | h1139
                · linarith only [h1, h1139, h739, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1141 | h1141
                  · linarith only [h1, h1141, h739, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1143 | h1143
                    · linarith only [h1143, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1145 | h1145
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1146 | h1146
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1147 | h1147
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1148 | h1148
                            · linarith only [h1145, h1148, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · linarith only [h0, h1145, h1147, h1148, h4, h739, hc12, hc23, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1151 | h1151
                            · linarith only [h0, h1147, h1151, h656, hc12, hc34, hlam, hphi, ht23]
                            · rcases h1bigk with h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c
                              · have p1153_0 := h1153c.1
                                have p1153_1 := h1153c.2.1
                                have p1153_2 := h1153c.2.2.1
                                have p1153_3 := h1153c.2.2.2
                                linarith only [hlam, p1153_0]
                              · have p1153_0 := h1153c.1
                                have p1153_1 := h1153c.2.1
                                have p1153_2 := h1153c.2.2.1
                                have p1153_3 := h1153c.2.2.2
                                rcases p1153_3 (m.d 0 1) (by simp) with h1155 | h1155
                                · rcases p1153_3 (m.d 1 2) (by simp) with h1156 | h1156
                                  · linarith only [h1156, hlam, p1153_0]
                                  · rcases p1153_3 (m.d 1 3) (by simp) with h1158 | h1158
                                    · linarith only [h1, h1158, hlam]
                                    · linarith only [h1133, h1158, hlam]
                                · linarith only [h1155, hlam, p1153_0]
                              · have p1153_0 := h1153c.1
                                have p1153_1 := h1153c.2.1
                                have p1153_2 := h1153c.2.2.1
                                have p1153_3 := h1153c.2.2.2
                                rcases p1153_3 (m.d 0 1) (by simp) with h1162 | h1162
                                · rcases p1153_3 (m.d 1 2) (by simp) with h1163 | h1163
                                  · linarith only [h0, h1163, hlam]
                                  · rcases p1153_3 (m.d 1 3) (by simp) with h1165 | h1165
                                    · linarith only [h1165, hlam, p1153_0]
                                    · rcases p1153_3 (m.d 1 4) (by simp) with h1167 | h1167
                                      · linarith only [h1167, h2, hlam]
                                      · linarith only [h1139, h1167, hlam]
                                · linarith only [h1162, hlam, p1153_0]
                              · have p1153_0 := h1153c.1
                                have p1153_1 := h1153c.2.1
                                have p1153_2 := h1153c.2.2.1
                                have p1153_3 := h1153c.2.2.2
                                rcases p1153_3 (m.d 0 1) (by simp) with h1171 | h1171
                                · rcases p1153_3 (m.d 1 2) (by simp) with h1172 | h1172
                                  · linarith only [h0, h1172, hlam]
                                  · rcases p1153_3 (m.d 1 3) (by simp) with h1174 | h1174
                                    · linarith only [h1, h1174, hlam]
                                    · rcases p1153_3 (m.d 1 4) (by simp) with h1176 | h1176
                                      · linarith only [h1176, hlam, p1153_0]
                                      · rcases p1153_3 (m.d 1 5) (by simp) with h1178 | h1178
                                        · linarith only [h1178, h3, hlam]
                                        · linarith only [h1143, h1178, hlam]
                                · linarith only [h1171, hlam, p1153_0]
                              · have p1153_0 := h1153c.1
                                have p1153_1 := h1153c.2.1
                                have p1153_2 := h1153c.2.2.1
                                have p1153_3 := h1153c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht5b, p1153_1, u5ehi1]
                              · have p1153_0 := h1153c.1
                                have p1153_1 := h1153c.2.1
                                have p1153_2 := h1153c.2.2.1
                                have p1153_3 := h1153c.2.2.2
                                linarith only [h0, hlam, p1153_0]
                              · have p1153_0 := h1153c.1
                                have p1153_1 := h1153c.2.1
                                have p1153_2 := h1153c.2.2.1
                                have p1153_3 := h1153c.2.2.2
                                linarith only [hlam, p1153_0]
                              · have p1153_0 := h1153c.1
                                have p1153_1 := h1153c.2.1
                                have p1153_2 := h1153c.2.2.1
                                have p1153_3 := h1153c.2.2.2
                                linarith only [h1133, hlam, p1153_1]
                              · have p1153_0 := h1153c.1
                                have p1153_1 := h1153c.2.1
                                have p1153_2 := h1153c.2.2.1
                                have p1153_3 := h1153c.2.2.2
                                linarith only [h1135, hlam, p1153_1]
                              · have p1153_0 := h1153c.1
                                have p1153_1 := h1153c.2.1
                                have p1153_2 := h1153c.2.2.1
                                have p1153_3 := h1153c.2.2.2
                                linarith only [h1137, hlam, p1153_1]
                              · have p1153_0 := h1153c.1
                                have p1153_1 := h1153c.2.1
                                have p1153_2 := h1153c.2.2.1
                                have p1153_3 := h1153c.2.2.2
                                linarith only [h1, hlam, p1153_0]
                              · have p1153_0 := h1153c.1
                                have p1153_1 := h1153c.2.1
                                have p1153_2 := h1153c.2.2.1
                                have p1153_3 := h1153c.2.2.2
                                linarith only [h1, h1145, h739, hc12, hc24, hlam, hphi, p1153_1]
                              · have p1153_0 := h1153c.1
                                have p1153_1 := h1153c.2.1
                                have p1153_2 := h1153c.2.2.1
                                have p1153_3 := h1153c.2.2.2
                                linarith only [hlam, p1153_0]
                              · have p1153_0 := h1153c.1
                                have p1153_1 := h1153c.2.1
                                have p1153_2 := h1153c.2.2.1
                                have p1153_3 := h1153c.2.2.2
                                linarith only [h1139, hlam, p1153_0]
                              · have p1153_0 := h1153c.1
                                have p1153_1 := h1153c.2.1
                                have p1153_2 := h1153c.2.2.1
                                have p1153_3 := h1153c.2.2.2
                                linarith only [h1141, hlam, p1153_1]
                              · have p1153_0 := h1153c.1
                                have p1153_1 := h1153c.2.1
                                have p1153_2 := h1153c.2.2.1
                                have p1153_3 := h1153c.2.2.2
                                linarith only [h2, hlam, p1153_0]
                              · have p1153_0 := h1153c.1
                                have p1153_1 := h1153c.2.1
                                have p1153_2 := h1153c.2.2.1
                                have p1153_3 := h1153c.2.2.2
                                linarith only [h1147, h2, h656, hc12, hc45, hlam, hphi, ht23, ht34, p1153_1]
                              · have p1153_0 := h1153c.1
                                have p1153_1 := h1153c.2.1
                                have p1153_2 := h1153c.2.2.1
                                have p1153_3 := h1153c.2.2.2
                                linarith only [h1145, h1147, h2, h739, hc13, hc45, hlam, hphi, ht34, p1153_1]
                              · have p1153_0 := h1153c.1
                                have p1153_1 := h1153c.2.1
                                have p1153_2 := h1153c.2.2.1
                                have p1153_3 := h1153c.2.2.2
                                linarith only [hlam, p1153_0]
                              · have p1153_0 := h1153c.1
                                have p1153_1 := h1153c.2.1
                                have p1153_2 := h1153c.2.2.1
                                have p1153_3 := h1153c.2.2.2
                                linarith only [h1143, hlam, p1153_1]
                              · have p1153_0 := h1153c.1
                                have p1153_1 := h1153c.2.1
                                have p1153_2 := h1153c.2.2.1
                                have p1153_3 := h1153c.2.2.2
                                linarith only [h3, hlam, p1153_0]
                              · have p1153_0 := h1153c.1
                                have p1153_1 := h1153c.2.1
                                have p1153_2 := h1153c.2.2.1
                                have p1153_3 := h1153c.2.2.2
                                linarith only [h1141, h1146, hc12, hc23, hlam, hphi, p1153_1]
                              · have p1153_0 := h1153c.1
                                have p1153_1 := h1153c.2.1
                                have p1153_2 := h1153c.2.2.1
                                have p1153_3 := h1153c.2.2.2
                                linarith only [h1133, h1141, h1146, hc12, hc23, hlam, hphi, p1153_1]
                              · have p1153_0 := h1153c.1
                                have p1153_1 := h1153c.2.1
                                have p1153_2 := h1153c.2.2.1
                                have p1153_3 := h1153c.2.2.2
                                linarith only [h1133, h1139, h1141, h1146, hc12, hc23, hlam, hphi, p1153_1]
                              · have p1153_0 := h1153c.1
                                have p1153_1 := h1153c.2.1
                                have p1153_2 := h1153c.2.2.1
                                have p1153_3 := h1153c.2.2.2
                                linarith only [hlam, p1153_0]
                        · linarith only [h1145, h1146, h739, hc03, hc35, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1204 | h1204
                        · linarith only [h1145, h1204, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1206 | h1206
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1207 | h1207
                            · rcases h1bigk with h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c
                              · have p1208_0 := h1208c.1
                                have p1208_1 := h1208c.2.1
                                have p1208_2 := h1208c.2.2.1
                                have p1208_3 := h1208c.2.2.2
                                linarith only [hlam, p1208_0]
                              · have p1208_0 := h1208c.1
                                have p1208_1 := h1208c.2.1
                                have p1208_2 := h1208c.2.2.1
                                have p1208_3 := h1208c.2.2.2
                                rcases p1208_3 (m.d 0 1) (by simp) with h1210 | h1210
                                · rcases p1208_3 (m.d 1 2) (by simp) with h1211 | h1211
                                  · linarith only [h1211, hlam, p1208_0]
                                  · rcases p1208_3 (m.d 1 3) (by simp) with h1213 | h1213
                                    · linarith only [h1, h1213, hlam]
                                    · linarith only [h1133, h1213, hlam]
                                · linarith only [h1210, hlam, p1208_0]
                              · have p1208_0 := h1208c.1
                                have p1208_1 := h1208c.2.1
                                have p1208_2 := h1208c.2.2.1
                                have p1208_3 := h1208c.2.2.2
                                rcases p1208_3 (m.d 0 1) (by simp) with h1217 | h1217
                                · rcases p1208_3 (m.d 1 2) (by simp) with h1218 | h1218
                                  · linarith only [h0, h1218, hlam]
                                  · rcases p1208_3 (m.d 1 3) (by simp) with h1220 | h1220
                                    · linarith only [h1220, hlam, p1208_0]
                                    · rcases p1208_3 (m.d 1 4) (by simp) with h1222 | h1222
                                      · linarith only [h1222, h2, hlam]
                                      · linarith only [h1139, h1222, hlam]
                                · linarith only [h1217, hlam, p1208_0]
                              · have p1208_0 := h1208c.1
                                have p1208_1 := h1208c.2.1
                                have p1208_2 := h1208c.2.2.1
                                have p1208_3 := h1208c.2.2.2
                                rcases p1208_3 (m.d 0 1) (by simp) with h1226 | h1226
                                · rcases p1208_3 (m.d 1 2) (by simp) with h1227 | h1227
                                  · linarith only [h0, h1227, hlam]
                                  · rcases p1208_3 (m.d 1 3) (by simp) with h1229 | h1229
                                    · linarith only [h1, h1229, hlam]
                                    · rcases p1208_3 (m.d 1 4) (by simp) with h1231 | h1231
                                      · linarith only [h1231, hlam, p1208_0]
                                      · rcases p1208_3 (m.d 1 5) (by simp) with h1233 | h1233
                                        · linarith only [h1233, h3, hlam]
                                        · linarith only [h1143, h1233, hlam]
                                · linarith only [h1226, hlam, p1208_0]
                              · have p1208_0 := h1208c.1
                                have p1208_1 := h1208c.2.1
                                have p1208_2 := h1208c.2.2.1
                                have p1208_3 := h1208c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht5b, p1208_1, u5ehi1]
                              · have p1208_0 := h1208c.1
                                have p1208_1 := h1208c.2.1
                                have p1208_2 := h1208c.2.2.1
                                have p1208_3 := h1208c.2.2.2
                                linarith only [h0, hlam, p1208_0]
                              · have p1208_0 := h1208c.1
                                have p1208_1 := h1208c.2.1
                                have p1208_2 := h1208c.2.2.1
                                have p1208_3 := h1208c.2.2.2
                                linarith only [hlam, p1208_0]
                              · have p1208_0 := h1208c.1
                                have p1208_1 := h1208c.2.1
                                have p1208_2 := h1208c.2.2.1
                                have p1208_3 := h1208c.2.2.2
                                linarith only [h1133, hlam, p1208_1]
                              · have p1208_0 := h1208c.1
                                have p1208_1 := h1208c.2.1
                                have p1208_2 := h1208c.2.2.1
                                have p1208_3 := h1208c.2.2.2
                                linarith only [h1135, hlam, p1208_1]
                              · have p1208_0 := h1208c.1
                                have p1208_1 := h1208c.2.1
                                have p1208_2 := h1208c.2.2.1
                                have p1208_3 := h1208c.2.2.2
                                linarith only [h1137, hlam, p1208_1]
                              · have p1208_0 := h1208c.1
                                have p1208_1 := h1208c.2.1
                                have p1208_2 := h1208c.2.2.1
                                have p1208_3 := h1208c.2.2.2
                                linarith only [h1, hlam, p1208_0]
                              · have p1208_0 := h1208c.1
                                have p1208_1 := h1208c.2.1
                                have p1208_2 := h1208c.2.2.1
                                have p1208_3 := h1208c.2.2.2
                                linarith only [h1062, h1139, h2, hc12, hc45, hlam, hphi, ht23, ht34, p1208_1]
                              · have p1208_0 := h1208c.1
                                have p1208_1 := h1208c.2.1
                                have p1208_2 := h1208c.2.2.1
                                have p1208_3 := h1208c.2.2.2
                                linarith only [hlam, p1208_0]
                              · have p1208_0 := h1208c.1
                                have p1208_1 := h1208c.2.1
                                have p1208_2 := h1208c.2.2.1
                                have p1208_3 := h1208c.2.2.2
                                linarith only [h1139, hlam, p1208_0]
                              · have p1208_0 := h1208c.1
                                have p1208_1 := h1208c.2.1
                                have p1208_2 := h1208c.2.2.1
                                have p1208_3 := h1208c.2.2.2
                                linarith only [h1141, hlam, p1208_1]
                              · have p1208_0 := h1208c.1
                                have p1208_1 := h1208c.2.1
                                have p1208_2 := h1208c.2.2.1
                                have p1208_3 := h1208c.2.2.2
                                linarith only [h2, hlam, p1208_0]
                              · have p1208_0 := h1208c.1
                                have p1208_1 := h1208c.2.1
                                have p1208_2 := h1208c.2.2.1
                                have p1208_3 := h1208c.2.2.2
                                linarith only [h1062, h2, hc12, hc45, hlam, hphi, ht23, ht34, p1208_1]
                              · have p1208_0 := h1208c.1
                                have p1208_1 := h1208c.2.1
                                have p1208_2 := h1208c.2.2.1
                                have p1208_3 := h1208c.2.2.2
                                linarith only [h1062, h2, hc13, hc45, hlam, hphi, ht34, p1208_1]
                              · have p1208_0 := h1208c.1
                                have p1208_1 := h1208c.2.1
                                have p1208_2 := h1208c.2.2.1
                                have p1208_3 := h1208c.2.2.2
                                linarith only [hlam, p1208_0]
                              · have p1208_0 := h1208c.1
                                have p1208_1 := h1208c.2.1
                                have p1208_2 := h1208c.2.2.1
                                have p1208_3 := h1208c.2.2.2
                                linarith only [h1143, hlam, p1208_1]
                              · have p1208_0 := h1208c.1
                                have p1208_1 := h1208c.2.1
                                have p1208_2 := h1208c.2.2.1
                                have p1208_3 := h1208c.2.2.2
                                linarith only [h3, hlam, p1208_0]
                              · have p1208_0 := h1208c.1
                                have p1208_1 := h1208c.2.1
                                have p1208_2 := h1208c.2.2.1
                                have p1208_3 := h1208c.2.2.2
                                linarith only [h1062, h1145, h1206, h3, hc12, hc34, hlam, hphi, ht23, p1208_1]
                              · have p1208_0 := h1208c.1
                                have p1208_1 := h1208c.2.1
                                have p1208_2 := h1208c.2.2.1
                                have p1208_3 := h1208c.2.2.2
                                linarith only [h1062, h1133, h1145, h1206, h3, hc12, hc34, hlam, hphi, ht23, p1208_1]
                              · have p1208_0 := h1208c.1
                                have p1208_1 := h1208c.2.1
                                have p1208_2 := h1208c.2.2.1
                                have p1208_3 := h1208c.2.2.2
                                linarith only [h1062, h1135, h1145, h1206, h3, hc12, hc34, hlam, hphi, ht23, p1208_1]
                              · have p1208_0 := h1208c.1
                                have p1208_1 := h1208c.2.1
                                have p1208_2 := h1208c.2.2.1
                                have p1208_3 := h1208c.2.2.2
                                linarith only [hlam, p1208_0]
                            · linarith only [h1145, h1206, h1207, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1259 | h1259
                            · linarith only [h0, h1145, h1206, h1259, h4, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h0, h1145, h1259, h4, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 7470000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4

set_option maxHeartbeats 7470000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1262 | h1262
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1263 | h1263
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1264 | h1264
      · linarith only [h0, h1264, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1266 | h1266
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1267 | h1267
          · linarith only [h1, h1266, h1267, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1269 | h1269
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1270 | h1270
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1271 | h1271
                · linarith only [h0, h1264, h1271, h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1273 | h1273
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1274 | h1274
                    · linarith only [h1, h1271, h1274, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · linarith only [h0, h1269, h1274, h3, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1277 | h1277
                    · linarith only [h0, h1262, h1266, h1271, h1273, h1277, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · linarith only [h0, h1262, h1266, h1269, h1273, h1277, h3, hc23, hc35, hlam, hphi]
              · linarith only [h1263, h1264, h1270, hc12, hc25, hlam, hphi]
            · linarith only [h1262, h1264, h1269, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1282 | h1282
          · linarith only [h1263, h1264, h1282, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1284 | h1284
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1285 | h1285
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1286 | h1286
                · linarith only [h0, h1286, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1288 | h1288
                  · linarith only [h1, h1266, h1286, h1288, h3, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1290 | h1290
                    · linarith only [h1, h1286, h1290, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · linarith only [h0, h1284, h1290, h3, hc23, hc35, hlam, hphi]
              · linarith only [h0, h1263, h1284, h1285, h3, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · linarith only [h1262, h1264, h1284, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1295 | h1295
      · linarith only [h1263, h1295, h2, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1297 | h1297
        · linarith only [h1262, h1263, h1297, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1299 | h1299
          · linarith only [h1299, h2, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1301 | h1301
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1302 | h1302
              · linarith only [h0, h1263, h1302, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1304 | h1304
                · linarith only [h0, h1263, h1295, h1304, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1306 | h1306
                  · linarith only [h1, h1263, h1297, h1304, h1306, h3, hc02, hc25, hlam, hphi]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1308 | h1308
                    · linarith only [h1, h1297, h1301, h1302, h1304, h1308, h2, h3, hc23, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · linarith only [h1301, h1302, h1308, h2, h3, hc23, hc35, hlam, hphi]
            · linarith only [h1262, h1263, h1299, h1301, hc12, hc45, hlam, hphi, ht23, ht34]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1312 | h1312
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1313 | h1313
      · linarith only [h1, h1262, h1313, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1315 | h1315
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1316 | h1316
          · linarith only [h1, h1262, h1312, h1316, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1318 | h1318
            · linarith only [h0, h1262, h1318, h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1320 | h1320
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1321 | h1321
                · linarith only [h0, h1313, h1321, h3, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1323 | h1323
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1324 | h1324
                    · linarith only [h1, h1321, h1324, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1326 | h1326
                      · linarith only [h1, h1316, h1318, h1320, h1324, h1326, h3, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h1, h1318, h1320, h1326, h3, hc24, hc45, hlam, hphi]
                  · linarith only [h1, h1315, h1318, h1320, h1321, h1323, h3, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · linarith only [h1262, h1312, h1320, hc12, hc23, hlam, hphi]
        · linarith only [h1262, h1312, h1315, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1332 | h1332
      · linarith only [h1262, h1332, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1334 | h1334
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1335 | h1335
          · linarith only [h1, h1334, h1335, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1337 | h1337
            · linarith only [h0, h1262, h1337, h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1339 | h1339
              · linarith only [h0, h1312, h1339, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1341 | h1341
                · linarith only [h0, h1312, h1332, h1341, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1343 | h1343
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1344 | h1344
                    · linarith only [h1, h1344, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1346 | h1346
                      · linarith only [h1, h1343, h1344, h1346, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · linarith only [h1, h1343, h1346, h3, hc34, hc45, hlam, hphi]
                  · linarith only [h1, h1334, h1337, h1341, h1343, h3, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1350 | h1350
          · linarith only [h1350, h2, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1352 | h1352
            · linarith only [h0, h1262, h1352, h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1354 | h1354
              · linarith only [h0, h1312, h1354, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1356 | h1356
                · linarith only [h0, h1262, h1356, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1358 | h1358
                  · linarith only [h1, h1262, h1334, h1356, h1358, h3, hc02, hc25, hlam, hphi]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1360 | h1360
                    · linarith only [h1, h1356, h1360, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1362 | h1362
                      · linarith only [h1360, h1362, h2, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1364 | h1364
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1365 | h1365
                          · linarith only [h0, h1360, h1365, h3, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1262, h1334, h1364, h1365, hc12, hc35, hlam, hphi, ht23]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1368 | h1368
                          · linarith only [h1360, h1364, h1368, h3, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1370 | h1370
                            · linarith only [h1352, h1358, h1362, h1364, h1370, h2, h3, hc12, hc34, hlam, hphi, ht23]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1372 | h1372
                              · linarith only [h0, h1262, h1364, h1370, h1372, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h0, h1262, h1364, h1372, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 7470000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 h0 h1 h2 h3
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 h0 h1 h2 h3

set_option maxHeartbeats 7470000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1375 | h1375
  · linarith only [h1375, h2, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1377 | h1377
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1378 | h1378
      · linarith only [h0, h1378, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1380 | h1380
        · linarith only [h0, h1380, h2, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1382 | h1382
          · linarith only [h1, h1382, h2, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1384 | h1384
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1385 | h1385
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1386 | h1386
                · linarith only [h0, h1378, h1386, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1388 | h1388
                  · linarith only [h0, h1375, h1380, h1388, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1390 | h1390
                    · linarith only [h1, h1377, h1382, h1384, h1390, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · linarith only [h0, h1385, h1390, h2, hc23, hc34, hlam, hphi]
              · linarith only [h1377, h1378, h1385, hc12, hc24, hlam, hphi]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1394 | h1394
              · linarith only [h0, h1384, h1394, h2, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h0, h1377, h1384, h1394, h2, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1397 | h1397
      · linarith only [h1, h1377, h1397, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1399 | h1399
        · linarith only [h1, h1377, h1399, h2, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1401 | h1401
          · linarith only [h1, h1401, h2, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1403 | h1403
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1404 | h1404
              · linarith only [h0, h1377, h1404, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1406 | h1406
                · linarith only [h0, h1397, h1406, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1408 | h1408
                  · linarith only [h0, h1375, h1399, h1408, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1410 | h1410
                    · linarith only [h1, h1401, h1406, h1410, h2, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1412 | h1412
                      · linarith only [h1, h1410, h1412, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1414 | h1414
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1415 | h1415
                          · linarith only [h0, h1375, h1410, h1414, h1415, hc12, hc23, hlam, hphi]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1417 | h1417
                            · linarith only [h1, h1375, h1404, h1412, h1415, h1417, hc12, hc34, hlam, hphi, ht23]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1419 | h1419
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1420 | h1420
                                · rcases h1bigk with h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c
                                  · have p1421_0 := h1421c.1
                                    have p1421_1 := h1421c.2.1
                                    have p1421_2 := h1421c.2.2.1
                                    have p1421_3 := h1421c.2.2.2
                                    linarith only [hlam, p1421_0]
                                  · have p1421_0 := h1421c.1
                                    have p1421_1 := h1421c.2.1
                                    have p1421_2 := h1421c.2.2.1
                                    have p1421_3 := h1421c.2.2.2
                                    linarith only [h1375, h1408, hc12, hc25, hlam, hphi, p1421_1]
                                  · have p1421_0 := h1421c.1
                                    have p1421_1 := h1421c.2.1
                                    have p1421_2 := h1421c.2.2.1
                                    have p1421_3 := h1421c.2.2.2
                                    linarith only [h1375, h1404, h1408, hc12, hc25, hlam, hphi, p1421_1]
                                  · have p1421_0 := h1421c.1
                                    have p1421_1 := h1421c.2.1
                                    have p1421_2 := h1421c.2.2.1
                                    have p1421_3 := h1421c.2.2.2
                                    linarith only [h2, hlam, p1421_0]
                                  · have p1421_0 := h1421c.1
                                    have p1421_1 := h1421c.2.1
                                    have p1421_2 := h1421c.2.2.1
                                    have p1421_3 := h1421c.2.2.2
                                    linarith only [h1375, hlam, p1421_0]
                                  · have p1421_0 := h1421c.1
                                    have p1421_1 := h1421c.2.1
                                    have p1421_2 := h1421c.2.2.1
                                    have p1421_3 := h1421c.2.2.2
                                    linarith only [h0, hlam, p1421_0]
                                  · have p1421_0 := h1421c.1
                                    have p1421_1 := h1421c.2.1
                                    have p1421_2 := h1421c.2.2.1
                                    have p1421_3 := h1421c.2.2.2
                                    linarith only [hlam, p1421_0]
                                  · have p1421_0 := h1421c.1
                                    have p1421_1 := h1421c.2.1
                                    have p1421_2 := h1421c.2.2.1
                                    have p1421_3 := h1421c.2.2.2
                                    linarith only [h1404, hlam, p1421_1]
                                  · have p1421_0 := h1421c.1
                                    have p1421_1 := h1421c.2.1
                                    have p1421_2 := h1421c.2.2.1
                                    have p1421_3 := h1421c.2.2.2
                                    linarith only [h1406, hlam, p1421_1]
                                  · have p1421_0 := h1421c.1
                                    have p1421_1 := h1421c.2.1
                                    have p1421_2 := h1421c.2.2.1
                                    have p1421_3 := h1421c.2.2.2
                                    linarith only [h1408, hlam, p1421_1]
                                  · have p1421_0 := h1421c.1
                                    have p1421_1 := h1421c.2.1
                                    have p1421_2 := h1421c.2.2.1
                                    have p1421_3 := h1421c.2.2.2
                                    linarith only [h1, hlam, p1421_0]
                                  · have p1421_0 := h1421c.1
                                    have p1421_1 := h1421c.2.1
                                    have p1421_2 := h1421c.2.2.1
                                    have p1421_3 := h1421c.2.2.2
                                    linarith only [h1, h1375, h1408, hc12, hc25, hlam, hphi, p1421_1]
                                  · have p1421_0 := h1421c.1
                                    have p1421_1 := h1421c.2.1
                                    have p1421_2 := h1421c.2.2.1
                                    have p1421_3 := h1421c.2.2.2
                                    linarith only [hlam, p1421_0]
                                  · have p1421_0 := h1421c.1
                                    have p1421_1 := h1421c.2.1
                                    have p1421_2 := h1421c.2.2.1
                                    have p1421_3 := h1421c.2.2.2
                                    linarith only [h1410, hlam, p1421_0]
                                  · have p1421_0 := h1421c.1
                                    have p1421_1 := h1421c.2.1
                                    have p1421_2 := h1421c.2.2.1
                                    have p1421_3 := h1421c.2.2.2
                                    linarith only [h1412, hlam, p1421_1]
                                  · have p1421_0 := h1421c.1
                                    have p1421_1 := h1421c.2.1
                                    have p1421_2 := h1421c.2.2.1
                                    have p1421_3 := h1421c.2.2.2
                                    linarith only [h0, h1406, hc12, hc24, hlam, hphi, p1421_1]
                                  · have p1421_0 := h1421c.1
                                    have p1421_1 := h1421c.2.1
                                    have p1421_2 := h1421c.2.2.1
                                    have p1421_3 := h1421c.2.2.2
                                    rcases p1421_3 (m.d 0 1) (by simp) with h1438 | h1438
                                    · linarith only [h1438, h2, hlam]
                                    · linarith only [h0, h1438, hlam]
                                  · have p1421_0 := h1421c.1
                                    have p1421_1 := h1421c.2.1
                                    have p1421_2 := h1421c.2.2.1
                                    have p1421_3 := h1421c.2.2.2
                                    rcases p1421_3 (m.d 0 1) (by simp) with h1441 | h1441
                                    · linarith only [h1441, h2, hlam]
                                    · linarith only [h1, h1441, hlam]
                                  · have p1421_0 := h1421c.1
                                    have p1421_1 := h1421c.2.1
                                    have p1421_2 := h1421c.2.2.1
                                    have p1421_3 := h1421c.2.2.2
                                    linarith only [hlam, p1421_0]
                                  · have p1421_0 := h1421c.1
                                    have p1421_1 := h1421c.2.1
                                    have p1421_2 := h1421c.2.2.1
                                    have p1421_3 := h1421c.2.2.2
                                    linarith only [h1, h1375, h1404, h1406, h1415, hc12, hc34, hlam, hphi, ht23, p1421_1]
                                  · have p1421_0 := h1421c.1
                                    have p1421_1 := h1421c.2.1
                                    have p1421_2 := h1421c.2.2.1
                                    have p1421_3 := h1421c.2.2.2
                                    linarith only [h1, h1404, h1408, hc12, hc25, hlam, hphi, p1421_1]
                                  · have p1421_0 := h1421c.1
                                    have p1421_1 := h1421c.2.1
                                    have p1421_2 := h1421c.2.2.1
                                    have p1421_3 := h1421c.2.2.2
                                    rcases p1421_3 (m.d 0 1) (by simp) with h1447 | h1447
                                    · linarith only [h1375, h1447, hlam]
                                    · linarith only [h0, h1447, hlam]
                                  · have p1421_0 := h1421c.1
                                    have p1421_1 := h1421c.2.1
                                    have p1421_2 := h1421c.2.2.1
                                    have p1421_3 := h1421c.2.2.2
                                    rcases p1421_3 (m.d 0 1) (by simp) with h1450 | h1450
                                    · linarith only [h1375, h1450, hlam]
                                    · linarith only [h1, h1450, hlam]
                                  · have p1421_0 := h1421c.1
                                    have p1421_1 := h1421c.2.1
                                    have p1421_2 := h1421c.2.2.1
                                    have p1421_3 := h1421c.2.2.2
                                    linarith only [h1414, hlam, p1421_0]
                                  · have p1421_0 := h1421c.1
                                    have p1421_1 := h1421c.2.1
                                    have p1421_2 := h1421c.2.2.1
                                    have p1421_3 := h1421c.2.2.2
                                    linarith only [hlam, p1421_0]
                                · linarith only [h1403, h1406, h1414, h1415, h1420, hc04, hlam, hphi, ht0b, ht5b, u5ehi1]
                              · linarith only [h1403, h1406, h1419, h2, hlam]
                        · linarith only [h1403, h1414, h2, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1458 | h1458
              · linarith only [h0, h1375, h1377, h1458, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1460 | h1460
                · linarith only [h0, h1403, h1460, h2, hc24, hc45, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1462 | h1462
                  · linarith only [h1, h1399, h1403, h1458, h1462, h2, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1464 | h1464
                    · linarith only [h1, h1401, h1403, h1464, h2, hc03, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1466 | h1466
                      · linarith only [h1, h1403, h1466, h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1468 | h1468
                        · linarith only [h1, h1403, h1458, h1460, h1468, h2, hc12, hc24, hlam, hphi]
                        · linarith only [h1, h1458, h1468, h2, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 7470000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x0_x0_x0 m hb1 hb2 hb4 hb5 h0 h1 h2
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x0_x0_x1 m hb1 hb2 hb4 hb5 h0 h1 h2

end R2N4
