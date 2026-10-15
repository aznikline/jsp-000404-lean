import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3710000 in
set_option maxHeartbeats 3710000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_0_L_I_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h659 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0elo := hb0.1
  have h1bigk := hb1.1
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h660 | h660
  · rcases m.htr 0 1 5 (by decide) (by decide) with h661 | h661
    · rcases m.htr 0 2 4 (by decide) (by decide) with h662 | h662
      · rcases m.htr 0 3 4 (by decide) (by decide) with h663 | h663
        · rcases m.htr 0 3 5 (by decide) (by decide) with h664 | h664
          · rcases m.htr 1 2 3 (by decide) (by decide) with h665 | h665
            · rcases m.htr 1 2 4 (by decide) (by decide) with h666 | h666
              · rcases m.htr 1 2 5 (by decide) (by decide) with h667 | h667
                · rcases m.htr 1 3 4 (by decide) (by decide) with h668 | h668
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h669 | h669
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h670 | h670
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h671 | h671
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h672 | h672
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h673 | h673
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h674 | h674
                              · linarith only [h659, h665, h671, h674, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                              · linarith only [h0, h659, h668, h670, h674, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · linarith only [h0, h659, h668, h670, h673, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · linarith only [h664, h672, hc23, hlam, hphi, u3elo0]
                        · linarith only [h663, h671, hc23, hlam, hphi, u3elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h680 | h680
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h681 | h681
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h682 | h682
                            · linarith only [h662, h670, h682, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h684 | h684
                              · linarith only [h0, h659, h667, h668, h670, h684, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                              · rcases h1bigk with h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c
                                · have p686_0 := h686c.1
                                  have p686_1 := h686c.2.1
                                  have p686_2 := h686c.2.2.1
                                  have p686_3 := h686c.2.2.2
                                  linarith only [hlam, p686_0]
                                · have p686_0 := h686c.1
                                  have p686_1 := h686c.2.1
                                  have p686_2 := h686c.2.2.1
                                  have p686_3 := h686c.2.2.2
                                  linarith only [h0, hlam, p686_0]
                                · have p686_0 := h686c.1
                                  have p686_1 := h686c.2.1
                                  have p686_2 := h686c.2.2.1
                                  have p686_3 := h686c.2.2.2
                                  linarith only [h0, h665, h681, h684, hc34, hlam, hphi, ht0b, ht45, ht5b, p686_1, u0elo1]
                                · have p686_0 := h686c.1
                                  have p686_1 := h686c.2.1
                                  have p686_2 := h686c.2.2.1
                                  have p686_3 := h686c.2.2.2
                                  rcases p686_3 (m.d 0 1) (by simp) with h690 | h690
                                  · rcases p686_3 (m.d 1 2) (by simp) with h691 | h691
                                    · rcases p686_3 (m.d 1 3) (by simp) with h692 | h692
                                      · linarith only [h659, h692, hlam]
                                      · linarith only [h668, h692, hlam]
                                    · linarith only [h666, h691, hlam]
                                  · linarith only [h690, hlam, p686_0]
                                · have p686_0 := h686c.1
                                  have p686_1 := h686c.2.1
                                  have p686_2 := h686c.2.2.1
                                  have p686_3 := h686c.2.2.2
                                  rcases p686_3 (m.d 0 1) (by simp) with h697 | h697
                                  · rcases p686_3 (m.d 1 2) (by simp) with h698 | h698
                                    · rcases p686_3 (m.d 1 3) (by simp) with h699 | h699
                                      · linarith only [h659, h699, hlam]
                                      · linarith only [h669, h699, hlam]
                                    · linarith only [h667, h698, hlam]
                                  · linarith only [h697, hlam, p686_0]
                                · have p686_0 := h686c.1
                                  have p686_1 := h686c.2.1
                                  have p686_2 := h686c.2.2.1
                                  have p686_3 := h686c.2.2.2
                                  linarith only [h659, h665, h681, h684, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p686_1]
                                · have p686_0 := h686c.1
                                  have p686_1 := h686c.2.1
                                  have p686_2 := h686c.2.2.1
                                  have p686_3 := h686c.2.2.2
                                  linarith only [hlam, p686_0]
                                · have p686_0 := h686c.1
                                  have p686_1 := h686c.2.1
                                  have p686_2 := h686c.2.2.1
                                  have p686_3 := h686c.2.2.2
                                  rcases p686_3 (m.d 0 1) (by simp) with h706 | h706
                                  · linarith only [h0, h706, hlam]
                                  · linarith only [h659, h706, hlam]
                                · have p686_0 := h686c.1
                                  have p686_1 := h686c.2.1
                                  have p686_2 := h686c.2.2.1
                                  have p686_3 := h686c.2.2.2
                                  rcases p686_3 (m.d 0 1) (by simp) with h709 | h709
                                  · linarith only [h0, h709, hlam]
                                  · linarith only [h660, h709, hlam]
                                · have p686_0 := h686c.1
                                  have p686_1 := h686c.2.1
                                  have p686_2 := h686c.2.2.1
                                  have p686_3 := h686c.2.2.2
                                  rcases p686_3 (m.d 0 1) (by simp) with h712 | h712
                                  · linarith only [h0, h712, hlam]
                                  · linarith only [h661, h712, hlam]
                                · have p686_0 := h686c.1
                                  have p686_1 := h686c.2.1
                                  have p686_2 := h686c.2.2.1
                                  have p686_3 := h686c.2.2.2
                                  linarith only [h659, hlam, p686_0]
                                · have p686_0 := h686c.1
                                  have p686_1 := h686c.2.1
                                  have p686_2 := h686c.2.2.1
                                  have p686_3 := h686c.2.2.2
                                  linarith only [h665, hlam, p686_1]
                                · have p686_0 := h686c.1
                                  have p686_1 := h686c.2.1
                                  have p686_2 := h686c.2.2.1
                                  have p686_3 := h686c.2.2.2
                                  linarith only [hlam, p686_0]
                                · have p686_0 := h686c.1
                                  have p686_1 := h686c.2.1
                                  have p686_2 := h686c.2.2.1
                                  have p686_3 := h686c.2.2.2
                                  linarith only [h659, hc14, hlam, hphi, ht0b, ht45, ht5b, p686_1, u0elo0]
                                · have p686_0 := h686c.1
                                  have p686_1 := h686c.2.1
                                  have p686_2 := h686c.2.2.1
                                  have p686_3 := h686c.2.2.2
                                  linarith only [h0, h659, h670, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p686_1]
                                · have p686_0 := h686c.1
                                  have p686_1 := h686c.2.1
                                  have p686_2 := h686c.2.2.1
                                  have p686_3 := h686c.2.2.2
                                  linarith only [h660, hlam, p686_0]
                                · have p686_0 := h686c.1
                                  have p686_1 := h686c.2.1
                                  have p686_2 := h686c.2.2.1
                                  have p686_3 := h686c.2.2.2
                                  linarith only [h666, hlam, p686_1]
                                · have p686_0 := h686c.1
                                  have p686_1 := h686c.2.1
                                  have p686_2 := h686c.2.2.1
                                  have p686_3 := h686c.2.2.2
                                  linarith only [h668, hlam, p686_0]
                                · have p686_0 := h686c.1
                                  have p686_1 := h686c.2.1
                                  have p686_2 := h686c.2.2.1
                                  have p686_3 := h686c.2.2.2
                                  linarith only [hlam, p686_0]
                                · have p686_0 := h686c.1
                                  have p686_1 := h686c.2.1
                                  have p686_2 := h686c.2.2.1
                                  have p686_3 := h686c.2.2.2
                                  linarith only [h670, hlam, p686_1]
                                · have p686_0 := h686c.1
                                  have p686_1 := h686c.2.1
                                  have p686_2 := h686c.2.2.1
                                  have p686_3 := h686c.2.2.2
                                  linarith only [h661, hlam, p686_0]
                                · have p686_0 := h686c.1
                                  have p686_1 := h686c.2.1
                                  have p686_2 := h686c.2.2.1
                                  have p686_3 := h686c.2.2.2
                                  linarith only [h667, hlam, p686_1]
                                · have p686_0 := h686c.1
                                  have p686_1 := h686c.2.1
                                  have p686_2 := h686c.2.2.1
                                  have p686_3 := h686c.2.2.2
                                  linarith only [h669, hlam, p686_0]
                                · have p686_0 := h686c.1
                                  have p686_1 := h686c.2.1
                                  have p686_2 := h686c.2.2.1
                                  have p686_3 := h686c.2.2.2
                                  linarith only [h0, h661, h666, h680, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p686_1]
                                · have p686_0 := h686c.1
                                  have p686_1 := h686c.2.1
                                  have p686_2 := h686c.2.2.1
                                  have p686_3 := h686c.2.2.2
                                  linarith only [hlam, p686_0]
                          · linarith only [h664, h681, hc23, hlam, hphi, u3elo0]
                        · linarith only [h663, h680, hc23, hlam, hphi, u3elo0]
                    · linarith only [h664, h669, hc13, hlam, hphi, u3elo0]
                  · linarith only [h663, h665, h668, hc23, hlam, hphi, u3elo0]
                · linarith only [h0, h661, h667, hlam]
              · linarith only [h0, h662, h666, hlam]
            · linarith only [h0, h665, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h737 | h737
            · rcases m.htr 1 2 4 (by decide) (by decide) with h738 | h738
              · rcases m.htr 1 2 5 (by decide) (by decide) with h739 | h739
                · rcases m.htr 1 3 4 (by decide) (by decide) with h740 | h740
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h741 | h741
                    · linarith only [h659, h664, h741, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h743 | h743
                      · linarith only [h740, h741, h743, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h745 | h745
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h746 | h746
                          · linarith only [h664, h746, hc03, hlam, hphi, u3elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h748 | h748
                            · linarith only [h662, h743, h748, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h750 | h750
                              · linarith only [h737, h741, h743, h745, h750, hlam]
                              · rcases h1bigk with h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c
                                · have p752_0 := h752c.1
                                  have p752_1 := h752c.2.1
                                  have p752_2 := h752c.2.2.1
                                  have p752_3 := h752c.2.2.2
                                  linarith only [hlam, p752_0]
                                · have p752_0 := h752c.1
                                  have p752_1 := h752c.2.1
                                  have p752_2 := h752c.2.2.1
                                  have p752_3 := h752c.2.2.2
                                  linarith only [h0, hlam, p752_0]
                                · have p752_0 := h752c.1
                                  have p752_1 := h752c.2.1
                                  have p752_2 := h752c.2.2.1
                                  have p752_3 := h752c.2.2.2
                                  linarith only [h737, h745, hc34, hlam, hphi, ht0b, ht45, ht5b, p752_1, u0elo0]
                                · have p752_0 := h752c.1
                                  have p752_1 := h752c.2.1
                                  have p752_2 := h752c.2.2.1
                                  have p752_3 := h752c.2.2.2
                                  rcases p752_3 (m.d 0 1) (by simp) with h756 | h756
                                  · rcases p752_3 (m.d 1 2) (by simp) with h757 | h757
                                    · rcases p752_3 (m.d 1 3) (by simp) with h758 | h758
                                      · linarith only [h659, h758, hlam]
                                      · linarith only [h740, h758, hlam]
                                    · linarith only [h738, h757, hlam]
                                  · linarith only [h756, hlam, p752_0]
                                · have p752_0 := h752c.1
                                  have p752_1 := h752c.2.1
                                  have p752_2 := h752c.2.2.1
                                  have p752_3 := h752c.2.2.2
                                  linarith only [h0, h737, h741, h745, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p752_1]
                                · have p752_0 := h752c.1
                                  have p752_1 := h752c.2.1
                                  have p752_2 := h752c.2.2.1
                                  have p752_3 := h752c.2.2.2
                                  linarith only [h659, h737, h745, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p752_1]
                                · have p752_0 := h752c.1
                                  have p752_1 := h752c.2.1
                                  have p752_2 := h752c.2.2.1
                                  have p752_3 := h752c.2.2.2
                                  linarith only [hlam, p752_0]
                                · have p752_0 := h752c.1
                                  have p752_1 := h752c.2.1
                                  have p752_2 := h752c.2.2.1
                                  have p752_3 := h752c.2.2.2
                                  rcases p752_3 (m.d 0 1) (by simp) with h766 | h766
                                  · linarith only [h0, h766, hlam]
                                  · linarith only [h659, h766, hlam]
                                · have p752_0 := h752c.1
                                  have p752_1 := h752c.2.1
                                  have p752_2 := h752c.2.2.1
                                  have p752_3 := h752c.2.2.2
                                  rcases p752_3 (m.d 0 1) (by simp) with h769 | h769
                                  · linarith only [h0, h769, hlam]
                                  · linarith only [h660, h769, hlam]
                                · have p752_0 := h752c.1
                                  have p752_1 := h752c.2.1
                                  have p752_2 := h752c.2.2.1
                                  have p752_3 := h752c.2.2.2
                                  rcases p752_3 (m.d 0 1) (by simp) with h772 | h772
                                  · linarith only [h0, h772, hlam]
                                  · linarith only [h661, h772, hlam]
                                · have p752_0 := h752c.1
                                  have p752_1 := h752c.2.1
                                  have p752_2 := h752c.2.2.1
                                  have p752_3 := h752c.2.2.2
                                  linarith only [h659, hlam, p752_0]
                                · have p752_0 := h752c.1
                                  have p752_1 := h752c.2.1
                                  have p752_2 := h752c.2.2.1
                                  have p752_3 := h752c.2.2.2
                                  linarith only [h737, hlam, p752_1]
                                · have p752_0 := h752c.1
                                  have p752_1 := h752c.2.1
                                  have p752_2 := h752c.2.2.1
                                  have p752_3 := h752c.2.2.2
                                  linarith only [hlam, p752_0]
                                · have p752_0 := h752c.1
                                  have p752_1 := h752c.2.1
                                  have p752_2 := h752c.2.2.1
                                  have p752_3 := h752c.2.2.2
                                  linarith only [h661, h741, hc14, hlam, hphi, ht0b, ht45, ht5b, p752_1, u0elo0]
                                · have p752_0 := h752c.1
                                  have p752_1 := h752c.2.1
                                  have p752_2 := h752c.2.2.1
                                  have p752_3 := h752c.2.2.2
                                  linarith only [h741, hlam, p752_1]
                                · have p752_0 := h752c.1
                                  have p752_1 := h752c.2.1
                                  have p752_2 := h752c.2.2.1
                                  have p752_3 := h752c.2.2.2
                                  linarith only [h660, hlam, p752_0]
                                · have p752_0 := h752c.1
                                  have p752_1 := h752c.2.1
                                  have p752_2 := h752c.2.2.1
                                  have p752_3 := h752c.2.2.2
                                  linarith only [h738, hlam, p752_1]
                                · have p752_0 := h752c.1
                                  have p752_1 := h752c.2.1
                                  have p752_2 := h752c.2.2.1
                                  have p752_3 := h752c.2.2.2
                                  linarith only [h740, hlam, p752_0]
                                · have p752_0 := h752c.1
                                  have p752_1 := h752c.2.1
                                  have p752_2 := h752c.2.2.1
                                  have p752_3 := h752c.2.2.2
                                  linarith only [hlam, p752_0]
                                · have p752_0 := h752c.1
                                  have p752_1 := h752c.2.1
                                  have p752_2 := h752c.2.2.1
                                  have p752_3 := h752c.2.2.2
                                  linarith only [h743, hlam, p752_1]
                                · have p752_0 := h752c.1
                                  have p752_1 := h752c.2.1
                                  have p752_2 := h752c.2.2.1
                                  have p752_3 := h752c.2.2.2
                                  linarith only [h661, hlam, p752_0]
                                · have p752_0 := h752c.1
                                  have p752_1 := h752c.2.1
                                  have p752_2 := h752c.2.2.1
                                  have p752_3 := h752c.2.2.2
                                  linarith only [h739, hlam, p752_1]
                                · have p752_0 := h752c.1
                                  have p752_1 := h752c.2.1
                                  have p752_2 := h752c.2.2.1
                                  have p752_3 := h752c.2.2.2
                                  linarith only [h0, h661, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p752_1]
                                · have p752_0 := h752c.1
                                  have p752_1 := h752c.2.1
                                  have p752_2 := h752c.2.2.1
                                  have p752_3 := h752c.2.2.2
                                  linarith only [h0, h661, h738, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p752_1]
                                · have p752_0 := h752c.1
                                  have p752_1 := h752c.2.1
                                  have p752_2 := h752c.2.2.1
                                  have p752_3 := h752c.2.2.2
                                  linarith only [hlam, p752_0]
                        · linarith only [h663, h664, h745, hc23, hlam, hphi, u3elo4]
                  · linarith only [h663, h664, h740, hc13, hlam, hphi, u3elo4]
                · linarith only [h0, h661, h739, hlam]
              · linarith only [h0, h662, h738, hlam]
            · linarith only [h0, h737, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h795 | h795
          · rcases m.htr 1 2 3 (by decide) (by decide) with h796 | h796
            · rcases m.htr 1 2 4 (by decide) (by decide) with h797 | h797
              · rcases m.htr 1 2 5 (by decide) (by decide) with h798 | h798
                · rcases m.htr 1 3 4 (by decide) (by decide) with h799 | h799
                  · linarith only [h659, h663, h799, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h801 | h801
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h802 | h802
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h803 | h803
                        · linarith only [h659, h663, h801, h803, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h805 | h805
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h806 | h806
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h807 | h807
                              · rcases h1bigk with h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c
                                · have p808_0 := h808c.1
                                  have p808_1 := h808c.2.1
                                  have p808_2 := h808c.2.2.1
                                  have p808_3 := h808c.2.2.2
                                  linarith only [hlam, p808_0]
                                · have p808_0 := h808c.1
                                  have p808_1 := h808c.2.1
                                  have p808_2 := h808c.2.2.1
                                  have p808_3 := h808c.2.2.2
                                  linarith only [h0, hlam, p808_0]
                                · have p808_0 := h808c.1
                                  have p808_1 := h808c.2.1
                                  have p808_2 := h808c.2.2.1
                                  have p808_3 := h808c.2.2.2
                                  linarith only [h796, h805, h807, hc45, hlam, hphi, ht0b, ht5b, p808_1, u0elo0]
                                · have p808_0 := h808c.1
                                  have p808_1 := h808c.2.1
                                  have p808_2 := h808c.2.2.1
                                  have p808_3 := h808c.2.2.2
                                  linarith only [h0, h796, h799, h805, h807, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p808_1]
                                · have p808_0 := h808c.1
                                  have p808_1 := h808c.2.1
                                  have p808_2 := h808c.2.2.1
                                  have p808_3 := h808c.2.2.2
                                  rcases p808_3 (m.d 0 1) (by simp) with h813 | h813
                                  · rcases p808_3 (m.d 1 2) (by simp) with h814 | h814
                                    · rcases p808_3 (m.d 1 3) (by simp) with h815 | h815
                                      · linarith only [h659, h815, hlam]
                                      · linarith only [h801, h815, hlam]
                                    · linarith only [h798, h814, hlam]
                                  · linarith only [h813, hlam, p808_0]
                                · have p808_0 := h808c.1
                                  have p808_1 := h808c.2.1
                                  have p808_2 := h808c.2.2.1
                                  have p808_3 := h808c.2.2.2
                                  linarith only [h659, h796, h805, h807, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p808_1]
                                · have p808_0 := h808c.1
                                  have p808_1 := h808c.2.1
                                  have p808_2 := h808c.2.2.1
                                  have p808_3 := h808c.2.2.2
                                  linarith only [hlam, p808_0]
                                · have p808_0 := h808c.1
                                  have p808_1 := h808c.2.1
                                  have p808_2 := h808c.2.2.1
                                  have p808_3 := h808c.2.2.2
                                  rcases p808_3 (m.d 0 1) (by simp) with h822 | h822
                                  · linarith only [h0, h822, hlam]
                                  · linarith only [h659, h822, hlam]
                                · have p808_0 := h808c.1
                                  have p808_1 := h808c.2.1
                                  have p808_2 := h808c.2.2.1
                                  have p808_3 := h808c.2.2.2
                                  rcases p808_3 (m.d 0 1) (by simp) with h825 | h825
                                  · linarith only [h0, h825, hlam]
                                  · linarith only [h660, h825, hlam]
                                · have p808_0 := h808c.1
                                  have p808_1 := h808c.2.1
                                  have p808_2 := h808c.2.2.1
                                  have p808_3 := h808c.2.2.2
                                  rcases p808_3 (m.d 0 1) (by simp) with h828 | h828
                                  · linarith only [h0, h828, hlam]
                                  · linarith only [h661, h828, hlam]
                                · have p808_0 := h808c.1
                                  have p808_1 := h808c.2.1
                                  have p808_2 := h808c.2.2.1
                                  have p808_3 := h808c.2.2.2
                                  linarith only [h659, hlam, p808_0]
                                · have p808_0 := h808c.1
                                  have p808_1 := h808c.2.1
                                  have p808_2 := h808c.2.2.1
                                  have p808_3 := h808c.2.2.2
                                  linarith only [h796, hlam, p808_1]
                                · have p808_0 := h808c.1
                                  have p808_1 := h808c.2.1
                                  have p808_2 := h808c.2.2.1
                                  have p808_3 := h808c.2.2.2
                                  linarith only [hlam, p808_0]
                                · have p808_0 := h808c.1
                                  have p808_1 := h808c.2.1
                                  have p808_2 := h808c.2.2.1
                                  have p808_3 := h808c.2.2.2
                                  linarith only [h799, hlam, p808_1]
                                · have p808_0 := h808c.1
                                  have p808_1 := h808c.2.1
                                  have p808_2 := h808c.2.2.1
                                  have p808_3 := h808c.2.2.2
                                  linarith only [h660, h799, hc15, hlam, hphi, ht0b, ht5b, p808_1, u0elo0]
                                · have p808_0 := h808c.1
                                  have p808_1 := h808c.2.1
                                  have p808_2 := h808c.2.2.1
                                  have p808_3 := h808c.2.2.2
                                  linarith only [h660, hlam, p808_0]
                                · have p808_0 := h808c.1
                                  have p808_1 := h808c.2.1
                                  have p808_2 := h808c.2.2.1
                                  have p808_3 := h808c.2.2.2
                                  linarith only [h797, hlam, p808_1]
                                · have p808_0 := h808c.1
                                  have p808_1 := h808c.2.1
                                  have p808_2 := h808c.2.2.1
                                  have p808_3 := h808c.2.2.2
                                  linarith only [h0, h660, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p808_1]
                                · have p808_0 := h808c.1
                                  have p808_1 := h808c.2.1
                                  have p808_2 := h808c.2.2.1
                                  have p808_3 := h808c.2.2.2
                                  linarith only [hlam, p808_0]
                                · have p808_0 := h808c.1
                                  have p808_1 := h808c.2.1
                                  have p808_2 := h808c.2.2.1
                                  have p808_3 := h808c.2.2.2
                                  linarith only [h0, h660, h801, h807, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p808_1]
                                · have p808_0 := h808c.1
                                  have p808_1 := h808c.2.1
                                  have p808_2 := h808c.2.2.1
                                  have p808_3 := h808c.2.2.2
                                  linarith only [h661, hlam, p808_0]
                                · have p808_0 := h808c.1
                                  have p808_1 := h808c.2.1
                                  have p808_2 := h808c.2.2.1
                                  have p808_3 := h808c.2.2.2
                                  linarith only [h798, hlam, p808_1]
                                · have p808_0 := h808c.1
                                  have p808_1 := h808c.2.1
                                  have p808_2 := h808c.2.2.1
                                  have p808_3 := h808c.2.2.2
                                  linarith only [h801, hlam, p808_0]
                                · have p808_0 := h808c.1
                                  have p808_1 := h808c.2.1
                                  have p808_2 := h808c.2.2.1
                                  have p808_3 := h808c.2.2.2
                                  linarith only [h802, hlam, p808_0]
                                · have p808_0 := h808c.1
                                  have p808_1 := h808c.2.1
                                  have p808_2 := h808c.2.2.1
                                  have p808_3 := h808c.2.2.2
                                  linarith only [hlam, p808_0]
                              · linarith only [h0, h660, h663, h802, h807, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · linarith only [h0, h660, h802, h806, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h659, h663, h801, h805, hc23, hlam, hphi, u3elo3]
                      · linarith only [h799, h801, h802, hlam]
                    · linarith only [h663, h795, h801, hc13, hlam, hphi, u3elo3]
                · linarith only [h0, h661, h798, hlam]
              · linarith only [h0, h662, h797, hlam]
            · linarith only [h0, h796, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h854 | h854
            · rcases m.htr 1 2 4 (by decide) (by decide) with h855 | h855
              · rcases m.htr 1 2 5 (by decide) (by decide) with h856 | h856
                · rcases m.htr 1 3 4 (by decide) (by decide) with h857 | h857
                  · linarith only [h659, h663, h857, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h859 | h859
                    · linarith only [h659, h795, h859, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h861 | h861
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h862 | h862
                        · linarith only [h663, h862, hc03, hlam, hphi, u3elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h864 | h864
                          · linarith only [h659, h795, h854, h864, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h866 | h866
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h867 | h867
                              · rcases h1bigk with h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c
                                · have p868_0 := h868c.1
                                  have p868_1 := h868c.2.1
                                  have p868_2 := h868c.2.2.1
                                  have p868_3 := h868c.2.2.2
                                  linarith only [hlam, p868_0]
                                · have p868_0 := h868c.1
                                  have p868_1 := h868c.2.1
                                  have p868_2 := h868c.2.2.1
                                  have p868_3 := h868c.2.2.2
                                  linarith only [h0, hlam, p868_0]
                                · have p868_0 := h868c.1
                                  have p868_1 := h868c.2.1
                                  have p868_2 := h868c.2.2.1
                                  have p868_3 := h868c.2.2.2
                                  rcases p868_3 (m.d 0 1) (by simp) with h871 | h871
                                  · rcases p868_3 (m.d 1 2) (by simp) with h872 | h872
                                    · rcases p868_3 (m.d 1 3) (by simp) with h873 | h873
                                      · linarith only [h873, hlam, p868_0]
                                      · rcases p868_3 (m.d 1 4) (by simp) with h875 | h875
                                        · linarith only [h660, h875, hlam]
                                        · linarith only [h857, h875, hlam]
                                    · linarith only [h854, h872, hlam]
                                  · linarith only [h871, hlam, p868_0]
                                · have p868_0 := h868c.1
                                  have p868_1 := h868c.2.1
                                  have p868_2 := h868c.2.2.1
                                  have p868_3 := h868c.2.2.2
                                  linarith only [h0, h855, h866, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p868_1]
                                · have p868_0 := h868c.1
                                  have p868_1 := h868c.2.1
                                  have p868_2 := h868c.2.2.1
                                  have p868_3 := h868c.2.2.2
                                  rcases p868_3 (m.d 0 1) (by simp) with h881 | h881
                                  · rcases p868_3 (m.d 1 2) (by simp) with h882 | h882
                                    · rcases p868_3 (m.d 1 3) (by simp) with h883 | h883
                                      · linarith only [h659, h883, hlam]
                                      · rcases p868_3 (m.d 1 4) (by simp) with h885 | h885
                                        · linarith only [h660, h885, hlam]
                                        · linarith only [h861, h885, hlam]
                                    · linarith only [h856, h882, hlam]
                                  · linarith only [h881, hlam, p868_0]
                                · have p868_0 := h868c.1
                                  have p868_1 := h868c.2.1
                                  have p868_2 := h868c.2.2.1
                                  have p868_3 := h868c.2.2.2
                                  linarith only [h660, h855, h866, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p868_1]
                                · have p868_0 := h868c.1
                                  have p868_1 := h868c.2.1
                                  have p868_2 := h868c.2.2.1
                                  have p868_3 := h868c.2.2.2
                                  linarith only [hlam, p868_0]
                                · have p868_0 := h868c.1
                                  have p868_1 := h868c.2.1
                                  have p868_2 := h868c.2.2.1
                                  have p868_3 := h868c.2.2.2
                                  rcases p868_3 (m.d 0 1) (by simp) with h892 | h892
                                  · linarith only [h0, h892, hlam]
                                  · linarith only [h659, h892, hlam]
                                · have p868_0 := h868c.1
                                  have p868_1 := h868c.2.1
                                  have p868_2 := h868c.2.2.1
                                  have p868_3 := h868c.2.2.2
                                  rcases p868_3 (m.d 0 1) (by simp) with h895 | h895
                                  · linarith only [h0, h895, hlam]
                                  · linarith only [h660, h895, hlam]
                                · have p868_0 := h868c.1
                                  have p868_1 := h868c.2.1
                                  have p868_2 := h868c.2.2.1
                                  have p868_3 := h868c.2.2.2
                                  rcases p868_3 (m.d 0 1) (by simp) with h898 | h898
                                  · linarith only [h0, h898, hlam]
                                  · linarith only [h661, h898, hlam]
                                · have p868_0 := h868c.1
                                  have p868_1 := h868c.2.1
                                  have p868_2 := h868c.2.2.1
                                  have p868_3 := h868c.2.2.2
                                  linarith only [h659, hlam, p868_0]
                                · have p868_0 := h868c.1
                                  have p868_1 := h868c.2.1
                                  have p868_2 := h868c.2.2.1
                                  have p868_3 := h868c.2.2.2
                                  linarith only [h854, hlam, p868_1]
                                · have p868_0 := h868c.1
                                  have p868_1 := h868c.2.1
                                  have p868_2 := h868c.2.2.1
                                  have p868_3 := h868c.2.2.2
                                  linarith only [hlam, p868_0]
                                · have p868_0 := h868c.1
                                  have p868_1 := h868c.2.1
                                  have p868_2 := h868c.2.2.1
                                  have p868_3 := h868c.2.2.2
                                  linarith only [h857, hlam, p868_1]
                                · have p868_0 := h868c.1
                                  have p868_1 := h868c.2.1
                                  have p868_2 := h868c.2.2.1
                                  have p868_3 := h868c.2.2.2
                                  linarith only [h859, hlam, p868_1]
                                · have p868_0 := h868c.1
                                  have p868_1 := h868c.2.1
                                  have p868_2 := h868c.2.2.1
                                  have p868_3 := h868c.2.2.2
                                  linarith only [h660, hlam, p868_0]
                                · have p868_0 := h868c.1
                                  have p868_1 := h868c.2.1
                                  have p868_2 := h868c.2.2.1
                                  have p868_3 := h868c.2.2.2
                                  linarith only [h855, hlam, p868_1]
                                · have p868_0 := h868c.1
                                  have p868_1 := h868c.2.1
                                  have p868_2 := h868c.2.2.1
                                  have p868_3 := h868c.2.2.2
                                  linarith only [h660, h854, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p868_1, u0elo0]
                                · have p868_0 := h868c.1
                                  have p868_1 := h868c.2.1
                                  have p868_2 := h868c.2.2.1
                                  have p868_3 := h868c.2.2.2
                                  linarith only [hlam, p868_0]
                                · have p868_0 := h868c.1
                                  have p868_1 := h868c.2.1
                                  have p868_2 := h868c.2.2.1
                                  have p868_3 := h868c.2.2.2
                                  linarith only [h660, h663, h854, h859, hc23, hlam, hphi, p868_1, u3elo3]
                                · have p868_0 := h868c.1
                                  have p868_1 := h868c.2.1
                                  have p868_2 := h868c.2.2.1
                                  have p868_3 := h868c.2.2.2
                                  linarith only [h661, hlam, p868_0]
                                · have p868_0 := h868c.1
                                  have p868_1 := h868c.2.1
                                  have p868_2 := h868c.2.2.1
                                  have p868_3 := h868c.2.2.2
                                  linarith only [h856, hlam, p868_1]
                                · have p868_0 := h868c.1
                                  have p868_1 := h868c.2.1
                                  have p868_2 := h868c.2.2.1
                                  have p868_3 := h868c.2.2.2
                                  linarith only [h0, h661, h854, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p868_1]
                                · have p868_0 := h868c.1
                                  have p868_1 := h868c.2.1
                                  have p868_2 := h868c.2.2.1
                                  have p868_3 := h868c.2.2.2
                                  linarith only [h861, hlam, p868_0]
                                · have p868_0 := h868c.1
                                  have p868_1 := h868c.2.1
                                  have p868_2 := h868c.2.2.1
                                  have p868_3 := h868c.2.2.2
                                  linarith only [hlam, p868_0]
                              · linarith only [h660, h662, h663, h866, h867, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · linarith only [h0, h660, h861, h866, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h918 | h918
                        · linarith only [h659, h663, h854, h918, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h920 | h920
                          · linarith only [h795, h920, hc03, hlam, hphi, u3elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h922 | h922
                            · linarith only [h855, h861, h922, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h924 | h924
                              · linarith only [h854, h857, h861, h924, hc23, hlam, hphi, u3elo3]
                              · rcases h1bigk with h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [hlam, p926_0]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [h0, hlam, p926_0]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  rcases p926_3 (m.d 0 1) (by simp) with h929 | h929
                                  · rcases p926_3 (m.d 1 2) (by simp) with h930 | h930
                                    · rcases p926_3 (m.d 1 3) (by simp) with h931 | h931
                                      · linarith only [h931, hlam, p926_0]
                                      · rcases p926_3 (m.d 1 4) (by simp) with h933 | h933
                                        · linarith only [h660, h933, hlam]
                                        · linarith only [h857, h933, hlam]
                                    · linarith only [h854, h930, hlam]
                                  · linarith only [h929, hlam, p926_0]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  rcases p926_3 (m.d 0 1) (by simp) with h938 | h938
                                  · rcases p926_3 (m.d 1 2) (by simp) with h939 | h939
                                    · rcases p926_3 (m.d 1 3) (by simp) with h940 | h940
                                      · linarith only [h659, h940, hlam]
                                      · rcases p926_3 (m.d 1 4) (by simp) with h942 | h942
                                        · linarith only [h942, hlam, p926_0]
                                        · rcases p926_3 (m.d 1 5) (by simp) with h944 | h944
                                          · linarith only [h661, h944, hlam]
                                          · linarith only [h861, h944, hlam]
                                    · linarith only [h855, h939, hlam]
                                  · linarith only [h938, hlam, p926_0]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  rcases p926_3 (m.d 0 1) (by simp) with h949 | h949
                                  · rcases p926_3 (m.d 1 2) (by simp) with h950 | h950
                                    · rcases p926_3 (m.d 1 3) (by simp) with h951 | h951
                                      · linarith only [h659, h951, hlam]
                                      · rcases p926_3 (m.d 1 4) (by simp) with h953 | h953
                                        · linarith only [h660, h953, hlam]
                                        · rcases p926_3 (m.d 1 5) (by simp) with h955 | h955
                                          · linarith only [h955, hlam, p926_0]
                                          · rcases h1emin with h957 | h957 | h957 | h957 | h957
                                            · linarith only [h0, h957, hc12, hlam]
                                            · rcases h4bigk with h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c
                                              · have p959_0 := h959c.1
                                                have p959_1 := h959c.2.1
                                                have p959_2 := h959c.2.2.1
                                                have p959_3 := h959c.2.2.2
                                                linarith only [hlam, p959_0]
                                              · have p959_0 := h959c.1
                                                have p959_1 := h959c.2.1
                                                have p959_2 := h959c.2.2.1
                                                have p959_3 := h959c.2.2.2
                                                linarith only [h663, h854, h857, hc23, hlam, hphi, p959_1, u3elo3]
                                              · have p959_0 := h959c.1
                                                have p959_1 := h959c.2.1
                                                have p959_2 := h959c.2.2.1
                                                have p959_3 := h959c.2.2.2
                                                linarith only [h663, h918, h924, hc23, hlam, hphi, p959_1, u3elo4]
                                              · have p959_0 := h959c.1
                                                have p959_1 := h959c.2.1
                                                have p959_2 := h959c.2.2.1
                                                have p959_3 := h959c.2.2.2
                                                linarith only [h663, hlam, p959_0]
                                              · have p959_0 := h959c.1
                                                have p959_1 := h959c.2.1
                                                have p959_2 := h959c.2.2.1
                                                have p959_3 := h959c.2.2.2
                                                linarith only [h663, h854, h857, h861, h924, hc23, hlam, hphi, p959_1, u3elo4]
                                              · have p959_0 := h959c.1
                                                have p959_1 := h959c.2.1
                                                have p959_2 := h959c.2.2.1
                                                have p959_3 := h959c.2.2.2
                                                linarith only [h660, hlam, p959_1]
                                              · have p959_0 := h959c.1
                                                have p959_1 := h959c.2.1
                                                have p959_2 := h959c.2.2.1
                                                have p959_3 := h959c.2.2.2
                                                linarith only [hlam, p959_0]
                                              · have p959_0 := h959c.1
                                                have p959_1 := h959c.2.1
                                                have p959_2 := h959c.2.2.1
                                                have p959_3 := h959c.2.2.2
                                                linarith only [h0, h861, h918, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p926_1, p959_1]
                                              · have p959_0 := h959c.1
                                                have p959_1 := h959c.2.1
                                                have p959_2 := h959c.2.2.1
                                                have p959_3 := h959c.2.2.2
                                                linarith only [h857, hlam, p959_1]
                                              · have p959_0 := h959c.1
                                                have p959_1 := h959c.2.1
                                                have p959_2 := h959c.2.2.1
                                                have p959_3 := h959c.2.2.2
                                                linarith only [h861, hlam, p959_0]
                                              · have p959_0 := h959c.1
                                                have p959_1 := h959c.2.1
                                                have p959_2 := h959c.2.2.1
                                                have p959_3 := h959c.2.2.2
                                                linarith only [h662, hlam, p959_1]
                                              · have p959_0 := h959c.1
                                                have p959_1 := h959c.2.1
                                                have p959_2 := h959c.2.2.1
                                                have p959_3 := h959c.2.2.2
                                                linarith only [h855, hlam, p959_1]
                                              · have p959_0 := h959c.1
                                                have p959_1 := h959c.2.1
                                                have p959_2 := h959c.2.2.1
                                                have p959_3 := h959c.2.2.2
                                                linarith only [hlam, p959_0]
                                              · have p959_0 := h959c.1
                                                have p959_1 := h959c.2.1
                                                have p959_2 := h959c.2.2.1
                                                have p959_3 := h959c.2.2.2
                                                linarith only [h918, hlam, p959_1]
                                              · have p959_0 := h959c.1
                                                have p959_1 := h959c.2.1
                                                have p959_2 := h959c.2.2.1
                                                have p959_3 := h959c.2.2.2
                                                linarith only [h922, hlam, p959_0]
                                              · have p959_0 := h959c.1
                                                have p959_1 := h959c.2.1
                                                have p959_2 := h959c.2.2.1
                                                have p959_3 := h959c.2.2.2
                                                linarith only [h662, h918, h924, hc23, hlam, hphi, p959_1, u3elo4]
                                              · have p959_0 := h959c.1
                                                have p959_1 := h959c.2.1
                                                have p959_2 := h959c.2.2.1
                                                have p959_3 := h959c.2.2.2
                                                linarith only [h855, h918, h924, hc23, hlam, hphi, p959_1, u3elo4]
                                              · have p959_0 := h959c.1
                                                have p959_1 := h959c.2.1
                                                have p959_2 := h959c.2.2.1
                                                have p959_3 := h959c.2.2.2
                                                linarith only [h918, h924, hc23, hlam, hphi, p959_1, u3elo4]
                                              · have p959_0 := h959c.1
                                                have p959_1 := h959c.2.1
                                                have p959_2 := h959c.2.2.1
                                                have p959_3 := h959c.2.2.2
                                                linarith only [hlam, p959_0]
                                              · have p959_0 := h959c.1
                                                have p959_1 := h959c.2.1
                                                have p959_2 := h959c.2.2.1
                                                have p959_3 := h959c.2.2.2
                                                linarith only [h924, hlam, p959_0]
                                              · have p959_0 := h959c.1
                                                have p959_1 := h959c.2.1
                                                have p959_2 := h959c.2.2.1
                                                have p959_3 := h959c.2.2.2
                                                rcases p959_3 (m.d 0 4) (by simp) with h980 | h980
                                                · linarith only [h980, hlam, p959_0]
                                                · rcases p959_3 (m.d 1 4) (by simp) with h982 | h982
                                                  · linarith only [h861, h982, hlam]
                                                  · rcases p959_3 (m.d 2 4) (by simp) with h984 | h984
                                                    · linarith only [h922, h984, hlam]
                                                    · rcases p959_3 (m.d 3 4) (by simp) with h986 | h986
                                                      · linarith only [h924, h986, hlam]
                                                      · linarith only [h663, h986, hlam]
                                              · have p959_0 := h959c.1
                                                have p959_1 := h959c.2.1
                                                have p959_2 := h959c.2.2.1
                                                have p959_3 := h959c.2.2.2
                                                rcases p959_3 (m.d 0 4) (by simp) with h989 | h989
                                                · linarith only [h663, h924, h989, hlam]
                                                · linarith only [h660, h989, hlam]
                                              · have p959_0 := h959c.1
                                                have p959_1 := h959c.2.1
                                                have p959_2 := h959c.2.2.1
                                                have p959_3 := h959c.2.2.2
                                                rcases p959_3 (m.d 0 4) (by simp) with h992 | h992
                                                · linarith only [h663, h924, h992, hlam]
                                                · linarith only [h662, h992, hlam]
                                              · have p959_0 := h959c.1
                                                have p959_1 := h959c.2.1
                                                have p959_2 := h959c.2.2.1
                                                have p959_3 := h959c.2.2.2
                                                linarith only [h659, h663, h854, hc23, hc45, hlam, hphi, ht34, p959_1]
                                              · have p959_0 := h959c.1
                                                have p959_1 := h959c.2.1
                                                have p959_2 := h959c.2.2.1
                                                have p959_3 := h959c.2.2.2
                                                linarith only [hlam, p959_0]
                                            · linarith only [h659, h957, hlam, ht12, ht23, u3elo0]
                                            · linarith only [h0, h660, h957, hc12, hlam]
                                            · linarith only [h0, h957, hc12, hlam, p926_1]
                                    · linarith only [h856, h950, hlam]
                                  · linarith only [h949, hlam, p926_0]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  rcases p926_3 (m.d 0 1) (by simp) with h1002 | h1002
                                  · linarith only [h1002, hlam, p926_0]
                                  · rcases p926_3 (m.d 1 2) (by simp) with h1004 | h1004
                                    · rcases p926_3 (m.d 1 3) (by simp) with h1005 | h1005
                                      · linarith only [h1005, h854, hlam]
                                      · rcases p926_3 (m.d 1 4) (by simp) with h1007 | h1007
                                        · linarith only [h1007, h855, hlam]
                                        · rcases p926_3 (m.d 1 5) (by simp) with h1009 | h1009
                                          · linarith only [h1009, h856, hlam]
                                          · rcases h1emin with h1011 | h1011 | h1011 | h1011 | h1011
                                            · linarith only [h1011, hc12, hlam, p926_1]
                                            · rcases h4bigk with h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c
                                              · have p1013_0 := h1013c.1
                                                have p1013_1 := h1013c.2.1
                                                have p1013_2 := h1013c.2.2.1
                                                have p1013_3 := h1013c.2.2.2
                                                linarith only [hlam, p1013_0]
                                              · have p1013_0 := h1013c.1
                                                have p1013_1 := h1013c.2.1
                                                have p1013_2 := h1013c.2.2.1
                                                have p1013_3 := h1013c.2.2.2
                                                linarith only [h663, h855, h918, hc23, hlam, hphi, p1013_1, u3elo3]
                                              · have p1013_0 := h1013c.1
                                                have p1013_1 := h1013c.2.1
                                                have p1013_2 := h1013c.2.2.1
                                                have p1013_3 := h1013c.2.2.2
                                                linarith only [h660, h918, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1013_1, p926_1]
                                              · have p1013_0 := h1013c.1
                                                have p1013_1 := h1013c.2.1
                                                have p1013_2 := h1013c.2.2.1
                                                have p1013_3 := h1013c.2.2.2
                                                linarith only [h663, hlam, p1013_0]
                                              · have p1013_0 := h1013c.1
                                                have p1013_1 := h1013c.2.1
                                                have p1013_2 := h1013c.2.2.1
                                                have p1013_3 := h1013c.2.2.2
                                                linarith only [h660, h924, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1013_1, p926_1]
                                              · have p1013_0 := h1013c.1
                                                have p1013_1 := h1013c.2.1
                                                have p1013_2 := h1013c.2.2.1
                                                have p1013_3 := h1013c.2.2.2
                                                linarith only [h660, hlam, p1013_1]
                                              · have p1013_0 := h1013c.1
                                                have p1013_1 := h1013c.2.1
                                                have p1013_2 := h1013c.2.2.1
                                                have p1013_3 := h1013c.2.2.2
                                                linarith only [hlam, p1013_0]
                                              · have p1013_0 := h1013c.1
                                                have p1013_1 := h1013c.2.1
                                                have p1013_2 := h1013c.2.2.1
                                                have p1013_3 := h1013c.2.2.2
                                                linarith only [h661, h861, h918, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1013_1, p926_1]
                                              · have p1013_0 := h1013c.1
                                                have p1013_1 := h1013c.2.1
                                                have p1013_2 := h1013c.2.2.1
                                                have p1013_3 := h1013c.2.2.2
                                                linarith only [h857, hlam, p1013_1]
                                              · have p1013_0 := h1013c.1
                                                have p1013_1 := h1013c.2.1
                                                have p1013_2 := h1013c.2.2.1
                                                have p1013_3 := h1013c.2.2.2
                                                linarith only [h861, hlam, p1013_0]
                                              · have p1013_0 := h1013c.1
                                                have p1013_1 := h1013c.2.1
                                                have p1013_2 := h1013c.2.2.1
                                                have p1013_3 := h1013c.2.2.2
                                                linarith only [h662, hlam, p1013_1]
                                              · have p1013_0 := h1013c.1
                                                have p1013_1 := h1013c.2.1
                                                have p1013_2 := h1013c.2.2.1
                                                have p1013_3 := h1013c.2.2.2
                                                linarith only [h855, hlam, p1013_1]
                                              · have p1013_0 := h1013c.1
                                                have p1013_1 := h1013c.2.1
                                                have p1013_2 := h1013c.2.2.1
                                                have p1013_3 := h1013c.2.2.2
                                                linarith only [hlam, p1013_0]
                                              · have p1013_0 := h1013c.1
                                                have p1013_1 := h1013c.2.1
                                                have p1013_2 := h1013c.2.2.1
                                                have p1013_3 := h1013c.2.2.2
                                                linarith only [h918, hlam, p1013_1]
                                              · have p1013_0 := h1013c.1
                                                have p1013_1 := h1013c.2.1
                                                have p1013_2 := h1013c.2.2.1
                                                have p1013_3 := h1013c.2.2.2
                                                linarith only [h922, hlam, p1013_0]
                                              · have p1013_0 := h1013c.1
                                                have p1013_1 := h1013c.2.1
                                                have p1013_2 := h1013c.2.2.1
                                                have p1013_3 := h1013c.2.2.2
                                                linarith only [h924, hc04, hc45, hlam, hphi, p1013_1]
                                              · have p1013_0 := h1013c.1
                                                have p1013_1 := h1013c.2.1
                                                have p1013_2 := h1013c.2.2.1
                                                have p1013_3 := h1013c.2.2.2
                                                linarith only [h924, hc14, hc45, hlam, hphi, p1013_1]
                                              · have p1013_0 := h1013c.1
                                                have p1013_1 := h1013c.2.1
                                                have p1013_2 := h1013c.2.2.1
                                                have p1013_3 := h1013c.2.2.2
                                                linarith only [h918, h924, hc23, hc45, hlam, hphi, ht34, p1013_1]
                                              · have p1013_0 := h1013c.1
                                                have p1013_1 := h1013c.2.1
                                                have p1013_2 := h1013c.2.2.1
                                                have p1013_3 := h1013c.2.2.2
                                                linarith only [hlam, p1013_0]
                                              · have p1013_0 := h1013c.1
                                                have p1013_1 := h1013c.2.1
                                                have p1013_2 := h1013c.2.2.1
                                                have p1013_3 := h1013c.2.2.2
                                                linarith only [h924, hlam, p1013_0]
                                              · have p1013_0 := h1013c.1
                                                have p1013_1 := h1013c.2.1
                                                have p1013_2 := h1013c.2.2.1
                                                have p1013_3 := h1013c.2.2.2
                                                rcases p1013_3 (m.d 0 4) (by simp) with h1034 | h1034
                                                · linarith only [h1034, hlam, p1013_0]
                                                · rcases p1013_3 (m.d 1 4) (by simp) with h1036 | h1036
                                                  · linarith only [h1036, h861, hlam]
                                                  · rcases p1013_3 (m.d 2 4) (by simp) with h1038 | h1038
                                                    · linarith only [h1038, h922, hlam]
                                                    · rcases p1013_3 (m.d 3 4) (by simp) with h1040 | h1040
                                                      · linarith only [h1040, h924, hlam]
                                                      · linarith only [h1040, h663, hlam]
                                              · have p1013_0 := h1013c.1
                                                have p1013_1 := h1013c.2.1
                                                have p1013_2 := h1013c.2.2.1
                                                have p1013_3 := h1013c.2.2.2
                                                rcases p1013_3 (m.d 0 4) (by simp) with h1043 | h1043
                                                · linarith only [h1043, h659, h660, h663, h854, h924, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p926_1]
                                                · linarith only [h1043, h660, hlam]
                                              · have p1013_0 := h1013c.1
                                                have p1013_1 := h1013c.2.1
                                                have p1013_2 := h1013c.2.2.1
                                                have p1013_3 := h1013c.2.2.2
                                                rcases p1013_3 (m.d 0 4) (by simp) with h1046 | h1046
                                                · linarith only [h1046, h663, h924, hlam]
                                                · linarith only [h1046, h662, hlam]
                                              · have p1013_0 := h1013c.1
                                                have p1013_1 := h1013c.2.1
                                                have p1013_2 := h1013c.2.2.1
                                                have p1013_3 := h1013c.2.2.2
                                                linarith only [h659, h663, h854, hc23, hc45, hlam, hphi, ht34, p1013_1]
                                              · have p1013_0 := h1013c.1
                                                have p1013_1 := h1013c.2.1
                                                have p1013_2 := h1013c.2.2.1
                                                have p1013_3 := h1013c.2.2.2
                                                linarith only [hlam, p1013_0]
                                            · linarith only [h1011, h659, h663, hlam, ht12, ht23, u3elo3]
                                            · linarith only [h1011, h660, hc12, hlam, p926_1]
                                            · linarith only [h1011, h661, hc12, hlam, p926_1]
                                    · linarith only [h1004, hlam, p926_0]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [hlam, p926_0]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  rcases p926_3 (m.d 0 1) (by simp) with h1056 | h1056
                                  · linarith only [h0, h1056, hlam]
                                  · linarith only [h1056, h659, hlam]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  rcases p926_3 (m.d 0 1) (by simp) with h1059 | h1059
                                  · linarith only [h0, h1059, hlam]
                                  · linarith only [h1059, h660, hlam]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  rcases p926_3 (m.d 0 1) (by simp) with h1062 | h1062
                                  · linarith only [h0, h1062, hlam]
                                  · linarith only [h1062, h661, hlam]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [h659, hlam, p926_0]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [h854, hlam, p926_1]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [hlam, p926_0]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [h857, hlam, p926_1]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [h859, hlam, p926_1]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [h660, hlam, p926_0]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [h855, hlam, p926_1]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [h660, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p926_1, u0elo0]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [hlam, p926_0]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [h861, hlam, p926_1]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [h661, hlam, p926_0]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [h856, hlam, p926_1]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [h0, h661, h854, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p926_1]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [h0, h661, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p926_1]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [hlam, p926_0]
                · linarith only [h0, h661, h856, hlam]
              · linarith only [h0, h662, h855, hlam]
            · linarith only [h0, h854, hc01, hlam, hphi, ht12, ht23, u3elo2]
      · linarith only [h0, h660, h662, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1084 | h1084
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1085 | h1085
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1086 | h1086
          · linarith only [h1086, h659, h661, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1088 | h1088
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1089 | h1089
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1090 | h1090
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1091 | h1091
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1092 | h1092
                    · linarith only [h1086, h1092, h659, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h1092, h659, h661, hc13, hlam, hphi, u3elo4]
                  · linarith only [h1085, h1086, h1088, h1091, hc23, hlam, hphi, u3elo4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1096 | h1096
                  · linarith only [h0, h1090, h1096, h659, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h1085, h1086, h1096, hc13, hlam, hphi, u3elo4]
              · linarith only [h0, h1084, h1089, hlam]
            · linarith only [h0, h1088, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1101 | h1101
          · linarith only [h1085, h1101, h660, h661, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1103 | h1103
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1104 | h1104
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1105 | h1105
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1106 | h1106
                  · linarith only [h1085, h1106, h659, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1108 | h1108
                    · linarith only [h1101, h1108, h659, h661, hlam]
                    · linarith only [h1103, h1106, h1108, h660, h661, hc23, hlam, hphi, u3elo4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1111 | h1111
                  · linarith only [h0, h1105, h1111, h659, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1113 | h1113
                    · linarith only [h0, h1101, h1105, h1111, h1113, h660, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h0, h1105, h1111, h1113, h660, hc13, hlam, hphi, u3elo4]
              · linarith only [h0, h1084, h1104, hlam]
            · linarith only [h0, h1103, hc01, hlam, hphi, ht12, ht23, u3elo2]
      · linarith only [h0, h1084, h660, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1119 | h1119
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1120 | h1120
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1121 | h1121
        · linarith only [h1121, h659, h660, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1123 | h1123
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1124 | h1124
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1125 | h1125
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1126 | h1126
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1127 | h1127
                  · linarith only [h1121, h1127, h659, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h1127, h659, h660, hc13, hlam, hphi, u3elo3]
                · linarith only [h1119, h1125, h1126, h660, hlam]
              · linarith only [h0, h1120, h1125, hlam]
            · linarith only [h0, h1124, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1133 | h1133
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1134 | h1134
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1135 | h1135
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1136 | h1136
                  · linarith only [h1121, h1136, h659, h660, hlam]
                  · linarith only [h1136, h659, h660, hc13, hlam, hphi, u3elo3]
                · linarith only [h1119, h1134, h1135, h660, hlam]
              · linarith only [h0, h1120, h1134, hlam]
            · linarith only [h0, h1133, hc01, hlam, hphi, ht12, ht23, u3elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1142 | h1142
        · linarith only [h0, h1120, h1142, h659, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1144 | h1144
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1145 | h1145
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1146 | h1146
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1147 | h1147
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1148 | h1148
                  · linarith only [h1142, h1148, h659, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1120, h1145, h1146, h1148, h659, hc23, hlam, hphi, u3elo3]
                · linarith only [h0, h1120, h1145, h1146, h1147, h659, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1152 | h1152
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1153 | h1153
                  · linarith only [h0, h1142, h1146, h1153, h659, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h1146, h1153, h659, hc13, hlam, hphi, u3elo3]
                · linarith only [h0, h1119, h1152, hlam]
            · linarith only [h0, h1145, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1158 | h1158
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1159 | h1159
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1160 | h1160
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1161 | h1161
                  · linarith only [h1142, h1161, h659, hlam]
                  · linarith only [h0, h1120, h1158, h1159, h1161, h659, hc23, hlam, hphi, u3elo3]
                · linarith only [h0, h1120, h1158, h1159, h1160, h659, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1165 | h1165
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1166 | h1166
                  · linarith only [h0, h1159, h1166, h659, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h1158, h1159, h1166, h659, hc23, hlam, hphi, u3elo3]
                · linarith only [h0, h1119, h1165, hlam]
            · linarith only [h0, h1158, hc01, hlam, hphi, ht12, ht23, u3elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1171 | h1171
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1172 | h1172
        · linarith only [h1172, h659, h660, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1174 | h1174
          · linarith only [h1119, h1174, h659, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1176 | h1176
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1177 | h1177
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1178 | h1178
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1179 | h1179
                  · linarith only [h1172, h1179, h659, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h1176, h1179, h659, h660, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1182 | h1182
                  · linarith only [h1172, h1177, h1178, h1182, h659, h660, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h1176, h1182, h659, h660, hc23, hlam, hphi, u3elo3]
              · linarith only [h0, h1171, h1176, h1177, h659, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h1176, hc01, hlam, hphi, ht12, ht23, u3elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1187 | h1187
        · linarith only [h0, h1171, h1187, h659, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1189 | h1189
          · linarith only [h1119, h1189, h659, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1191 | h1191
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1192 | h1192
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1193 | h1193
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1194 | h1194
                  · linarith only [h1187, h1194, h659, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1171, h1191, h1192, h1194, h659, hc23, hlam, hphi, u3elo3]
                · linarith only [h0, h1171, h1191, h1192, h1193, h659, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1198 | h1198
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1199 | h1199
                  · linarith only [h0, h1187, h1192, h1199, h659, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h1119, h1191, h1192, h1198, h1199, h659, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1202 | h1202
                  · linarith only [h0, h1192, h1202, h659, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h1191, h1192, h1202, h659, hc23, hlam, hphi, u3elo3]
            · linarith only [h0, h1191, hc01, hlam, hphi, ht12, ht23, u3elo2]

end R2N4
