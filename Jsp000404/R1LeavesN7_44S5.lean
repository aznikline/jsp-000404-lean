import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_44S4

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5626000 in
set_option maxHeartbeats 5626000 in
theorem r1l7_21_15_M_IR_L_I_s3_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h6 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 1 2 4 (by decide) (by decide) with h668 | h668
  · rcases m.htr 1 2 5 (by decide) (by decide) with h669 | h669
    · rcases m.htr 1 3 4 (by decide) (by decide) with h670 | h670
      · rcases m.htr 1 3 5 (by decide) (by decide) with h671 | h671
        · rcases m.htr 1 4 5 (by decide) (by decide) with h672 | h672
          · rcases m.htr 2 3 4 (by decide) (by decide) with h673 | h673
            · rcases m.htr 2 3 5 (by decide) (by decide) with h674 | h674
              · rcases m.htr 2 4 5 (by decide) (by decide) with h675 | h675
                · linarith only [h4, h668, h675, h7, hc02, hc45, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h4, h668, h672, h675, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h668, h672, h674, h7, hc35, hlam, hphi, ht12, ht23, u1ehi4]
            · linarith only [h668, h672, h673, h7, hc34, hlam, hphi, ht12, ht23, u1ehi4]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h680 | h680
            · rcases m.htr 2 3 5 (by decide) (by decide) with h681 | h681
              · rcases m.htr 2 4 5 (by decide) (by decide) with h682 | h682
                · linarith only [h672, h682, hc24, hlam, hphi, ht12, u1ehi3]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h684 | h684
                  · linarith only [h672, h684, hc34, hlam, hphi, ht12, ht23, u1ehi3]
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
                      rcases p686_3 (m.d 0 1) (by simp) with h688 | h688
                      · rcases p686_3 (m.d 1 2) (by simp) with h689 | h689
                        · linarith only [h689, hlam, p686_0]
                        · rcases p686_3 (m.d 1 3) (by simp) with h691 | h691
                          · linarith only [h1, h691, hlam]
                          · linarith only [h691, h7, hlam]
                      · linarith only [h688, hlam, p686_0]
                    · have p686_0 := h686c.1
                      have p686_1 := h686c.2.1
                      have p686_2 := h686c.2.2.1
                      have p686_3 := h686c.2.2.2
                      rcases p686_3 (m.d 0 1) (by simp) with h695 | h695
                      · rcases p686_3 (m.d 1 2) (by simp) with h696 | h696
                        · linarith only [h0, h696, hlam]
                        · rcases p686_3 (m.d 1 3) (by simp) with h698 | h698
                          · linarith only [h698, hlam, p686_0]
                          · rcases p686_3 (m.d 1 4) (by simp) with h700 | h700
                            · linarith only [h2, h700, hlam]
                            · rcases p686_3 (m.d 1 5) (by simp) with h702 | h702
                              · linarith only [h3, h702, hlam]
                              · rcases h5bigk with h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [hlam, p704_0]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  rcases p704_3 (m.d 0 5) (by simp) with h706 | h706
                                  · rcases p704_3 (m.d 1 5) (by simp) with h707 | h707
                                    · linarith only [h3, h707, hlam]
                                    · rcases p704_3 (m.d 2 5) (by simp) with h709 | h709
                                      · linarith only [h0, h4, h669, h672, h7, h709, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p704_1, u1ehi3]
                                      · rcases p704_3 (m.d 3 5) (by simp) with h711 | h711
                                        · linarith only [h5, h711, hlam]
                                        · rcases p704_3 (m.d 4 5) (by simp) with h713 | h713
                                          · linarith only [h6, h713, hlam]
                                          · linarith only [h672, h713, hlam]
                                  · linarith only [h3, h706, hlam]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  rcases p704_3 (m.d 0 5) (by simp) with h717 | h717
                                  · rcases p704_3 (m.d 1 5) (by simp) with h718 | h718
                                    · linarith only [h3, h718, hlam]
                                    · linarith only [h669, h718, hlam]
                                  · linarith only [h717, hlam, p704_0]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  rcases p704_3 (m.d 0 5) (by simp) with h722 | h722
                                  · rcases p704_3 (m.d 1 5) (by simp) with h723 | h723
                                    · linarith only [h3, h723, hlam]
                                    · linarith only [h671, h723, hlam]
                                  · linarith only [h5, h722, hlam]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [h5, h672, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p704_1, u1ehi3]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [h3, hlam, p704_0]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [hlam, p704_0]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [h0, h4, h669, h682, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p704_1]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [h0, h4, h669, h7, hc01, hc35, hlam, hphi, ht0b, ht5b, p704_1]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [h672, hlam, p704_1]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [h3, hc25, hlam, hphi, ht12, p704_1, u1ehi4]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [h669, hlam, p704_1]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [hlam, p704_0]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [h0, h4, h669, h684, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p704_1]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [h682, hlam, p704_1]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [h5, hlam, p704_0]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [h671, hlam, p704_0]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [h681, hlam, p704_0]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [hlam, p704_0]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [h684, hlam, p704_1]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [h6, hlam, p704_0]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [h672, hc45, hlam, hphi, ht12, ht23, ht34, p704_1, u1ehi3]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  rcases p704_3 (m.d 0 5) (by simp) with h745 | h745
                                  · rcases p704_3 (m.d 1 5) (by simp) with h746 | h746
                                    · linarith only [h672, h746, hlam]
                                    · linarith only [h669, h746, hlam]
                                  · linarith only [h0, h3, h4, h669, h672, h7, h745, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  rcases p704_3 (m.d 0 5) (by simp) with h750 | h750
                                  · rcases p704_3 (m.d 1 5) (by simp) with h751 | h751
                                    · linarith only [h672, h751, hlam]
                                    · linarith only [h671, h751, hlam]
                                  · linarith only [h5, h750, hlam]
                                · have p704_0 := h704c.1
                                  have p704_1 := h704c.2.1
                                  have p704_2 := h704c.2.2.1
                                  have p704_3 := h704c.2.2.2
                                  linarith only [hlam, p704_0]
                      · linarith only [h695, hlam, p686_0]
                    · have p686_0 := h686c.1
                      have p686_1 := h686c.2.1
                      have p686_2 := h686c.2.2.1
                      have p686_3 := h686c.2.2.2
                      rcases p686_3 (m.d 0 1) (by simp) with h757 | h757
                      · rcases p686_3 (m.d 1 2) (by simp) with h758 | h758
                        · linarith only [h0, h758, hlam]
                        · linarith only [h668, h758, hlam]
                      · linarith only [h757, hlam, p686_0]
                    · have p686_0 := h686c.1
                      have p686_1 := h686c.2.1
                      have p686_2 := h686c.2.2.1
                      have p686_3 := h686c.2.2.2
                      rcases p686_3 (m.d 0 1) (by simp) with h762 | h762
                      · rcases p686_3 (m.d 1 2) (by simp) with h763 | h763
                        · linarith only [h0, h763, hlam]
                        · linarith only [h669, h763, hlam]
                      · linarith only [h762, hlam, p686_0]
                    · have p686_0 := h686c.1
                      have p686_1 := h686c.2.1
                      have p686_2 := h686c.2.2.1
                      have p686_3 := h686c.2.2.2
                      linarith only [h0, hlam, p686_0]
                    · have p686_0 := h686c.1
                      have p686_1 := h686c.2.1
                      have p686_2 := h686c.2.2.1
                      have p686_3 := h686c.2.2.2
                      linarith only [hlam, p686_0]
                    · have p686_0 := h686c.1
                      have p686_1 := h686c.2.1
                      have p686_2 := h686c.2.2.1
                      have p686_3 := h686c.2.2.2
                      linarith only [h7, hlam, p686_0]
                    · have p686_0 := h686c.1
                      have p686_1 := h686c.2.1
                      have p686_2 := h686c.2.2.1
                      have p686_3 := h686c.2.2.2
                      linarith only [h0, h4, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p686_1, u1ehi3]
                    · have p686_0 := h686c.1
                      have p686_1 := h686c.2.1
                      have p686_2 := h686c.2.2.1
                      have p686_3 := h686c.2.2.2
                      linarith only [h0, h4, h672, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p686_1, u1ehi3]
                    · have p686_0 := h686c.1
                      have p686_1 := h686c.2.1
                      have p686_2 := h686c.2.2.1
                      have p686_3 := h686c.2.2.2
                      linarith only [h1, hlam, p686_0]
                    · have p686_0 := h686c.1
                      have p686_1 := h686c.2.1
                      have p686_2 := h686c.2.2.1
                      have p686_3 := h686c.2.2.2
                      linarith only [hc13, hlam, hphi, p686_1, u1ehi1]
                    · have p686_0 := h686c.1
                      have p686_1 := h686c.2.1
                      have p686_2 := h686c.2.2.1
                      have p686_3 := h686c.2.2.2
                      linarith only [hlam, p686_0]
                    · have p686_0 := h686c.1
                      have p686_1 := h686c.2.1
                      have p686_2 := h686c.2.2.1
                      have p686_3 := h686c.2.2.2
                      linarith only [h0, h4, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p686_1, u1ehi3]
                    · have p686_0 := h686c.1
                      have p686_1 := h686c.2.1
                      have p686_2 := h686c.2.2.1
                      have p686_3 := h686c.2.2.2
                      linarith only [h0, h4, h672, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p686_1, u1ehi3]
                    · have p686_0 := h686c.1
                      have p686_1 := h686c.2.1
                      have p686_2 := h686c.2.2.1
                      have p686_3 := h686c.2.2.2
                      linarith only [h2, hlam, p686_0]
                    · have p686_0 := h686c.1
                      have p686_1 := h686c.2.1
                      have p686_2 := h686c.2.2.1
                      have p686_3 := h686c.2.2.2
                      linarith only [h668, hlam, p686_1]
                    · have p686_0 := h686c.1
                      have p686_1 := h686c.2.1
                      have p686_2 := h686c.2.2.1
                      have p686_3 := h686c.2.2.2
                      linarith only [h670, hlam, p686_0]
                    · have p686_0 := h686c.1
                      have p686_1 := h686c.2.1
                      have p686_2 := h686c.2.2.1
                      have p686_3 := h686c.2.2.2
                      linarith only [hlam, p686_0]
                    · have p686_0 := h686c.1
                      have p686_1 := h686c.2.1
                      have p686_2 := h686c.2.2.1
                      have p686_3 := h686c.2.2.2
                      linarith only [h672, hlam, p686_1]
                    · have p686_0 := h686c.1
                      have p686_1 := h686c.2.1
                      have p686_2 := h686c.2.2.1
                      have p686_3 := h686c.2.2.2
                      linarith only [h3, hlam, p686_0]
                    · have p686_0 := h686c.1
                      have p686_1 := h686c.2.1
                      have p686_2 := h686c.2.2.1
                      have p686_3 := h686c.2.2.2
                      linarith only [h669, hlam, p686_1]
                    · have p686_0 := h686c.1
                      have p686_1 := h686c.2.1
                      have p686_2 := h686c.2.2.1
                      have p686_3 := h686c.2.2.2
                      linarith only [h671, hlam, p686_0]
                    · have p686_0 := h686c.1
                      have p686_1 := h686c.2.1
                      have p686_2 := h686c.2.2.1
                      have p686_3 := h686c.2.2.2
                      linarith only [h669, hc12, hlam, hphi, p686_1, u1ehi3]
                    · have p686_0 := h686c.1
                      have p686_1 := h686c.2.1
                      have p686_2 := h686c.2.2.1
                      have p686_3 := h686c.2.2.2
                      linarith only [hlam, p686_0]
              · linarith only [h681, h7, hc35, hlam, hphi, ht12, ht23, u1ehi1]
            · linarith only [h669, h672, h680, h7, hc34, hlam, hphi, ht12, ht23, u1ehi3]
        · linarith only [h669, h671, h7, hlam]
      · linarith only [h668, h670, h7, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h791 | h791
      · rcases m.htr 1 3 5 (by decide) (by decide) with h792 | h792
        · rcases m.htr 1 4 5 (by decide) (by decide) with h793 | h793
          · linarith only [h668, h669, h793, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h795 | h795
            · rcases m.htr 2 3 5 (by decide) (by decide) with h796 | h796
              · rcases m.htr 2 4 5 (by decide) (by decide) with h797 | h797
                · linarith only [h793, h797, hc24, hlam, hphi, ht12, u1ehi3]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h799 | h799
                  · linarith only [h668, h669, h795, h797, h799, hlam]
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
                      rcases p801_3 (m.d 0 1) (by simp) with h803 | h803
                      · rcases p801_3 (m.d 1 2) (by simp) with h804 | h804
                        · linarith only [h804, hlam, p801_0]
                        · rcases p801_3 (m.d 1 3) (by simp) with h806 | h806
                          · linarith only [h1, h806, hlam]
                          · linarith only [h7, h806, hlam]
                      · linarith only [h803, hlam, p801_0]
                    · have p801_0 := h801c.1
                      have p801_1 := h801c.2.1
                      have p801_2 := h801c.2.2.1
                      have p801_3 := h801c.2.2.2
                      rcases p801_3 (m.d 0 1) (by simp) with h810 | h810
                      · rcases p801_3 (m.d 1 2) (by simp) with h811 | h811
                        · linarith only [h0, h811, hlam]
                        · rcases p801_3 (m.d 1 3) (by simp) with h813 | h813
                          · linarith only [h813, hlam, p801_0]
                          · rcases p801_3 (m.d 1 4) (by simp) with h815 | h815
                            · linarith only [h2, h815, hlam]
                            · rcases p801_3 (m.d 1 5) (by simp) with h817 | h817
                              · linarith only [h3, h817, hlam]
                              · rcases h5bigk with h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c
                                · have p819_0 := h819c.1
                                  have p819_1 := h819c.2.1
                                  have p819_2 := h819c.2.2.1
                                  have p819_3 := h819c.2.2.2
                                  linarith only [hlam, p819_0]
                                · have p819_0 := h819c.1
                                  have p819_1 := h819c.2.1
                                  have p819_2 := h819c.2.2.1
                                  have p819_3 := h819c.2.2.2
                                  rcases p819_3 (m.d 0 5) (by simp) with h821 | h821
                                  · rcases p819_3 (m.d 1 5) (by simp) with h822 | h822
                                    · linarith only [h3, h822, hlam]
                                    · rcases p819_3 (m.d 2 5) (by simp) with h824 | h824
                                      · linarith only [h668, h669, h796, h824, hc23, hlam, hphi, ht12, p819_1, u1ehi3]
                                      · linarith only [h669, h824, hlam]
                                  · linarith only [h3, h821, hlam]
                                · have p819_0 := h819c.1
                                  have p819_1 := h819c.2.1
                                  have p819_2 := h819c.2.2.1
                                  have p819_3 := h819c.2.2.2
                                  linarith only [h0, h4, h5, h668, h669, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p819_1, u1ehi3]
                                · have p819_0 := h819c.1
                                  have p819_1 := h819c.2.1
                                  have p819_2 := h819c.2.2.1
                                  have p819_3 := h819c.2.2.2
                                  rcases p819_3 (m.d 0 5) (by simp) with h829 | h829
                                  · rcases p819_3 (m.d 1 5) (by simp) with h830 | h830
                                    · linarith only [h3, h830, hlam]
                                    · linarith only [h792, h830, hlam]
                                  · linarith only [h5, h829, hlam]
                                · have p819_0 := h819c.1
                                  have p819_1 := h819c.2.1
                                  have p819_2 := h819c.2.2.1
                                  have p819_3 := h819c.2.2.2
                                  linarith only [h0, h4, h5, h793, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p819_1, u1ehi3]
                                · have p819_0 := h819c.1
                                  have p819_1 := h819c.2.1
                                  have p819_2 := h819c.2.2.1
                                  have p819_3 := h819c.2.2.2
                                  linarith only [h3, hlam, p819_0]
                                · have p819_0 := h819c.1
                                  have p819_1 := h819c.2.1
                                  have p819_2 := h819c.2.2.1
                                  have p819_3 := h819c.2.2.2
                                  linarith only [hlam, p819_0]
                                · have p819_0 := h819c.1
                                  have p819_1 := h819c.2.1
                                  have p819_2 := h819c.2.2.1
                                  have p819_3 := h819c.2.2.2
                                  linarith only [h669, hlam, p819_0]
                                · have p819_0 := h819c.1
                                  have p819_1 := h819c.2.1
                                  have p819_2 := h819c.2.2.1
                                  have p819_3 := h819c.2.2.2
                                  linarith only [h792, hc01, hc35, hlam, hphi, ht0b, ht5b, p801_1, p819_1]
                                · have p819_0 := h819c.1
                                  have p819_1 := h819c.2.1
                                  have p819_2 := h819c.2.2.1
                                  have p819_3 := h819c.2.2.2
                                  linarith only [h793, hlam, p819_1]
                                · have p819_0 := h819c.1
                                  have p819_1 := h819c.2.1
                                  have p819_2 := h819c.2.2.1
                                  have p819_3 := h819c.2.2.2
                                  linarith only [h3, hc25, hlam, hphi, ht12, p819_1, u1ehi4]
                                · have p819_0 := h819c.1
                                  have p819_1 := h819c.2.1
                                  have p819_2 := h819c.2.2.1
                                  have p819_3 := h819c.2.2.2
                                  linarith only [h2, h6, h797, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p819_1, u1ehi4]
                                · have p819_0 := h819c.1
                                  have p819_1 := h819c.2.1
                                  have p819_2 := h819c.2.2.1
                                  have p819_3 := h819c.2.2.2
                                  linarith only [hlam, p819_0]
                                · have p819_0 := h819c.1
                                  have p819_1 := h819c.2.1
                                  have p819_2 := h819c.2.2.1
                                  have p819_3 := h819c.2.2.2
                                  rcases p819_3 (m.d 0 5) (by simp) with h843 | h843
                                  · rcases p819_3 (m.d 1 5) (by simp) with h844 | h844
                                    · linarith only [h669, h844, hlam]
                                    · linarith only [h792, h844, hlam]
                                  · linarith only [h5, h843, hlam]
                                · have p819_0 := h819c.1
                                  have p819_1 := h819c.2.1
                                  have p819_2 := h819c.2.2.1
                                  have p819_3 := h819c.2.2.2
                                  linarith only [h797, hlam, p819_1]
                                · have p819_0 := h819c.1
                                  have p819_1 := h819c.2.1
                                  have p819_2 := h819c.2.2.1
                                  have p819_3 := h819c.2.2.2
                                  linarith only [h5, hlam, p819_0]
                                · have p819_0 := h819c.1
                                  have p819_1 := h819c.2.1
                                  have p819_2 := h819c.2.2.1
                                  have p819_3 := h819c.2.2.2
                                  linarith only [h792, hlam, p819_0]
                                · have p819_0 := h819c.1
                                  have p819_1 := h819c.2.1
                                  have p819_2 := h819c.2.2.1
                                  have p819_3 := h819c.2.2.2
                                  linarith only [h796, hlam, p819_0]
                                · have p819_0 := h819c.1
                                  have p819_1 := h819c.2.1
                                  have p819_2 := h819c.2.2.1
                                  have p819_3 := h819c.2.2.2
                                  linarith only [hlam, p819_0]
                                · have p819_0 := h819c.1
                                  have p819_1 := h819c.2.1
                                  have p819_2 := h819c.2.2.1
                                  have p819_3 := h819c.2.2.2
                                  linarith only [h799, hlam, p819_1]
                                · have p819_0 := h819c.1
                                  have p819_1 := h819c.2.1
                                  have p819_2 := h819c.2.2.1
                                  have p819_3 := h819c.2.2.2
                                  linarith only [h6, hlam, p819_0]
                                · have p819_0 := h819c.1
                                  have p819_1 := h819c.2.1
                                  have p819_2 := h819c.2.2.1
                                  have p819_3 := h819c.2.2.2
                                  linarith only [h2, h6, h668, h669, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p819_1, u1ehi3]
                                · have p819_0 := h819c.1
                                  have p819_1 := h819c.2.1
                                  have p819_2 := h819c.2.2.1
                                  have p819_3 := h819c.2.2.2
                                  linarith only [h2, h6, h668, h669, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p819_1, u1ehi3]
                                · have p819_0 := h819c.1
                                  have p819_1 := h819c.2.1
                                  have p819_2 := h819c.2.2.1
                                  have p819_3 := h819c.2.2.2
                                  rcases p819_3 (m.d 0 5) (by simp) with h857 | h857
                                  · rcases p819_3 (m.d 1 5) (by simp) with h858 | h858
                                    · linarith only [h793, h858, hlam]
                                    · linarith only [h792, h858, hlam]
                                  · linarith only [h5, h857, hlam]
                                · have p819_0 := h819c.1
                                  have p819_1 := h819c.2.1
                                  have p819_2 := h819c.2.2.1
                                  have p819_3 := h819c.2.2.2
                                  linarith only [hlam, p819_0]
                      · linarith only [h810, hlam, p801_0]
                    · have p801_0 := h801c.1
                      have p801_1 := h801c.2.1
                      have p801_2 := h801c.2.2.1
                      have p801_3 := h801c.2.2.2
                      rcases p801_3 (m.d 0 1) (by simp) with h864 | h864
                      · rcases p801_3 (m.d 1 2) (by simp) with h865 | h865
                        · linarith only [h0, h865, hlam]
                        · linarith only [h668, h865, hlam]
                      · linarith only [h864, hlam, p801_0]
                    · have p801_0 := h801c.1
                      have p801_1 := h801c.2.1
                      have p801_2 := h801c.2.2.1
                      have p801_3 := h801c.2.2.2
                      rcases p801_3 (m.d 0 1) (by simp) with h869 | h869
                      · rcases p801_3 (m.d 1 2) (by simp) with h870 | h870
                        · linarith only [h0, h870, hlam]
                        · rcases p801_3 (m.d 1 3) (by simp) with h872 | h872
                          · linarith only [h1, h872, hlam]
                          · linarith only [h792, h872, hlam]
                      · linarith only [h869, hlam, p801_0]
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
                      linarith only [h7, hlam, p801_0]
                    · have p801_0 := h801c.1
                      have p801_1 := h801c.2.1
                      have p801_2 := h801c.2.2.1
                      have p801_3 := h801c.2.2.2
                      linarith only [hc12, hlam, hphi, p801_1, u1ehi3]
                    · have p801_0 := h801c.1
                      have p801_1 := h801c.2.1
                      have p801_2 := h801c.2.2.1
                      have p801_3 := h801c.2.2.2
                      linarith only [h669, hlam, p801_0]
                    · have p801_0 := h801c.1
                      have p801_1 := h801c.2.1
                      have p801_2 := h801c.2.2.1
                      have p801_3 := h801c.2.2.2
                      linarith only [h1, hlam, p801_0]
                    · have p801_0 := h801c.1
                      have p801_1 := h801c.2.1
                      have p801_2 := h801c.2.2.1
                      have p801_3 := h801c.2.2.2
                      linarith only [hc13, hlam, hphi, p801_1, u1ehi1]
                    · have p801_0 := h801c.1
                      have p801_1 := h801c.2.1
                      have p801_2 := h801c.2.2.1
                      have p801_3 := h801c.2.2.2
                      linarith only [hlam, p801_0]
                    · have p801_0 := h801c.1
                      have p801_1 := h801c.2.1
                      have p801_2 := h801c.2.2.1
                      have p801_3 := h801c.2.2.2
                      linarith only [h0, h4, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p801_1, u1ehi3]
                    · have p801_0 := h801c.1
                      have p801_1 := h801c.2.1
                      have p801_2 := h801c.2.2.1
                      have p801_3 := h801c.2.2.2
                      linarith only [h0, h4, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p801_1, u1ehi4]
                    · have p801_0 := h801c.1
                      have p801_1 := h801c.2.1
                      have p801_2 := h801c.2.2.1
                      have p801_3 := h801c.2.2.2
                      linarith only [h2, hlam, p801_0]
                    · have p801_0 := h801c.1
                      have p801_1 := h801c.2.1
                      have p801_2 := h801c.2.2.1
                      have p801_3 := h801c.2.2.2
                      linarith only [h668, hlam, p801_1]
                    · have p801_0 := h801c.1
                      have p801_1 := h801c.2.1
                      have p801_2 := h801c.2.2.1
                      have p801_3 := h801c.2.2.2
                      linarith only [h791, hlam, p801_0]
                    · have p801_0 := h801c.1
                      have p801_1 := h801c.2.1
                      have p801_2 := h801c.2.2.1
                      have p801_3 := h801c.2.2.2
                      linarith only [hlam, p801_0]
                    · have p801_0 := h801c.1
                      have p801_1 := h801c.2.1
                      have p801_2 := h801c.2.2.1
                      have p801_3 := h801c.2.2.2
                      linarith only [h793, hlam, p801_1]
                    · have p801_0 := h801c.1
                      have p801_1 := h801c.2.1
                      have p801_2 := h801c.2.2.1
                      have p801_3 := h801c.2.2.2
                      linarith only [h3, hlam, p801_0]
                    · have p801_0 := h801c.1
                      have p801_1 := h801c.2.1
                      have p801_2 := h801c.2.2.1
                      have p801_3 := h801c.2.2.2
                      linarith only [hc15, hlam, hphi, p801_1, u1ehi1]
                    · have p801_0 := h801c.1
                      have p801_1 := h801c.2.1
                      have p801_2 := h801c.2.2.1
                      have p801_3 := h801c.2.2.2
                      linarith only [h792, hlam, p801_0]
                    · have p801_0 := h801c.1
                      have p801_1 := h801c.2.1
                      have p801_2 := h801c.2.2.1
                      have p801_3 := h801c.2.2.2
                      linarith only [h0, h4, h7, h792, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p801_1, u1ehi3]
                    · have p801_0 := h801c.1
                      have p801_1 := h801c.2.1
                      have p801_2 := h801c.2.2.1
                      have p801_3 := h801c.2.2.2
                      linarith only [hlam, p801_0]
              · linarith only [h7, h796, hc35, hlam, hphi, ht12, ht23, u1ehi1]
            · linarith only [h668, h7, h795, hc34, hlam, hphi, ht12, ht23, u1ehi3]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h898 | h898
          · linarith only [h668, h669, h898, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h900 | h900
            · rcases m.htr 2 3 5 (by decide) (by decide) with h901 | h901
              · linarith only [h0, h4, h668, h7, h792, h901, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
              · linarith only [h668, h7, h901, hc35, hlam, hphi, ht12, ht23, u1ehi3]
            · linarith only [h668, h7, h900, hc34, hlam, hphi, ht12, ht23, u1ehi3]
      · linarith only [h668, h7, h791, hlam]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h906 | h906
    · rcases m.htr 1 3 4 (by decide) (by decide) with h907 | h907
      · rcases m.htr 1 3 5 (by decide) (by decide) with h908 | h908
        · rcases m.htr 1 4 5 (by decide) (by decide) with h909 | h909
          · rcases m.htr 2 3 4 (by decide) (by decide) with h910 | h910
            · rcases m.htr 2 3 5 (by decide) (by decide) with h911 | h911
              · rcases m.htr 2 4 5 (by decide) (by decide) with h912 | h912
                · rcases m.htr 3 4 5 (by decide) (by decide) with h913 | h913
                  · rcases h1bigk with h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c
                    · have p914_0 := h914c.1
                      have p914_1 := h914c.2.1
                      have p914_2 := h914c.2.2.1
                      have p914_3 := h914c.2.2.2
                      linarith only [hlam, p914_0]
                    · have p914_0 := h914c.1
                      have p914_1 := h914c.2.1
                      have p914_2 := h914c.2.2.1
                      have p914_3 := h914c.2.2.2
                      rcases p914_3 (m.d 0 1) (by simp) with h916 | h916
                      · rcases p914_3 (m.d 1 2) (by simp) with h917 | h917
                        · linarith only [h917, hlam, p914_0]
                        · rcases p914_3 (m.d 1 3) (by simp) with h919 | h919
                          · linarith only [h1, h919, hlam]
                          · linarith only [h7, h919, hlam]
                      · linarith only [h916, hlam, p914_0]
                    · have p914_0 := h914c.1
                      have p914_1 := h914c.2.1
                      have p914_2 := h914c.2.2.1
                      have p914_3 := h914c.2.2.2
                      linarith only [h907, h913, hc01, hc45, hlam, hphi, ht0b, ht5b, p914_1]
                    · have p914_0 := h914c.1
                      have p914_1 := h914c.2.1
                      have p914_2 := h914c.2.2.1
                      have p914_3 := h914c.2.2.2
                      rcases p914_3 (m.d 0 1) (by simp) with h924 | h924
                      · rcases p914_3 (m.d 1 2) (by simp) with h925 | h925
                        · linarith only [h0, h925, hlam]
                        · rcases p914_3 (m.d 1 3) (by simp) with h927 | h927
                          · linarith only [h1, h927, hlam]
                          · linarith only [h907, h927, hlam]
                      · linarith only [h924, hlam, p914_0]
                    · have p914_0 := h914c.1
                      have p914_1 := h914c.2.1
                      have p914_2 := h914c.2.2.1
                      have p914_3 := h914c.2.2.2
                      rcases p914_3 (m.d 0 1) (by simp) with h931 | h931
                      · rcases p914_3 (m.d 1 2) (by simp) with h932 | h932
                        · linarith only [h0, h932, hlam]
                        · linarith only [h906, h932, hlam]
                      · linarith only [h931, hlam, p914_0]
                    · have p914_0 := h914c.1
                      have p914_1 := h914c.2.1
                      have p914_2 := h914c.2.2.1
                      have p914_3 := h914c.2.2.2
                      linarith only [h0, hlam, p914_0]
                    · have p914_0 := h914c.1
                      have p914_1 := h914c.2.1
                      have p914_2 := h914c.2.2.1
                      have p914_3 := h914c.2.2.2
                      linarith only [hlam, p914_0]
                    · have p914_0 := h914c.1
                      have p914_1 := h914c.2.1
                      have p914_2 := h914c.2.2.1
                      have p914_3 := h914c.2.2.2
                      linarith only [h7, hlam, p914_0]
                    · have p914_0 := h914c.1
                      have p914_1 := h914c.2.1
                      have p914_2 := h914c.2.2.1
                      have p914_3 := h914c.2.2.2
                      linarith only [h668, hlam, p914_0]
                    · have p914_0 := h914c.1
                      have p914_1 := h914c.2.1
                      have p914_2 := h914c.2.2.1
                      have p914_3 := h914c.2.2.2
                      linarith only [h0, h4, h668, h910, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p914_1, u1ehi4]
                    · have p914_0 := h914c.1
                      have p914_1 := h914c.2.1
                      have p914_2 := h914c.2.2.1
                      have p914_3 := h914c.2.2.2
                      linarith only [h1, hlam, p914_0]
                    · have p914_0 := h914c.1
                      have p914_1 := h914c.2.1
                      have p914_2 := h914c.2.2.1
                      have p914_3 := h914c.2.2.2
                      linarith only [hc13, hlam, hphi, p914_1, u1ehi1]
                    · have p914_0 := h914c.1
                      have p914_1 := h914c.2.1
                      have p914_2 := h914c.2.2.1
                      have p914_3 := h914c.2.2.2
                      linarith only [hlam, p914_0]
                    · have p914_0 := h914c.1
                      have p914_1 := h914c.2.1
                      have p914_2 := h914c.2.2.1
                      have p914_3 := h914c.2.2.2
                      linarith only [h0, h4, h668, h7, h906, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p914_1, u1ehi4]
                    · have p914_0 := h914c.1
                      have p914_1 := h914c.2.1
                      have p914_2 := h914c.2.2.1
                      have p914_3 := h914c.2.2.2
                      linarith only [h0, h4, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p914_1, u1ehi4]
                    · have p914_0 := h914c.1
                      have p914_1 := h914c.2.1
                      have p914_2 := h914c.2.2.1
                      have p914_3 := h914c.2.2.2
                      linarith only [h2, hlam, p914_0]
                    · have p914_0 := h914c.1
                      have p914_1 := h914c.2.1
                      have p914_2 := h914c.2.2.1
                      have p914_3 := h914c.2.2.2
                      linarith only [h906, hc14, hlam, hphi, p914_1, u1ehi4]
                    · have p914_0 := h914c.1
                      have p914_1 := h914c.2.1
                      have p914_2 := h914c.2.2.1
                      have p914_3 := h914c.2.2.2
                      linarith only [h907, hlam, p914_0]
                    · have p914_0 := h914c.1
                      have p914_1 := h914c.2.1
                      have p914_2 := h914c.2.2.1
                      have p914_3 := h914c.2.2.2
                      linarith only [hlam, p914_0]
                    · have p914_0 := h914c.1
                      have p914_1 := h914c.2.1
                      have p914_2 := h914c.2.2.1
                      have p914_3 := h914c.2.2.2
                      linarith only [h0, h4, h668, h910, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p914_1, u1ehi4]
                    · have p914_0 := h914c.1
                      have p914_1 := h914c.2.1
                      have p914_2 := h914c.2.2.1
                      have p914_3 := h914c.2.2.2
                      linarith only [h3, hlam, p914_0]
                    · have p914_0 := h914c.1
                      have p914_1 := h914c.2.1
                      have p914_2 := h914c.2.2.1
                      have p914_3 := h914c.2.2.2
                      linarith only [h906, hlam, p914_1]
                    · have p914_0 := h914c.1
                      have p914_1 := h914c.2.1
                      have p914_2 := h914c.2.2.1
                      have p914_3 := h914c.2.2.2
                      linarith only [h908, hlam, p914_0]
                    · have p914_0 := h914c.1
                      have p914_1 := h914c.2.1
                      have p914_2 := h914c.2.2.1
                      have p914_3 := h914c.2.2.2
                      linarith only [h909, hlam, p914_0]
                    · have p914_0 := h914c.1
                      have p914_1 := h914c.2.1
                      have p914_2 := h914c.2.2.1
                      have p914_3 := h914c.2.2.2
                      linarith only [hlam, p914_0]
                  · linarith only [h0, h4, h7, h906, h912, h913, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h668, h912, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
              · linarith only [h668, h906, h910, h911, hc35, hlam, hphi, ht12, ht23, u1ehi4]
            · linarith only [h7, h906, h910, hc34, hlam, hphi, ht12, ht23, u1ehi4]
          · linarith only [h668, h906, h909, hlam]
        · linarith only [h668, h906, h907, h908, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h962 | h962
        · rcases m.htr 1 4 5 (by decide) (by decide) with h963 | h963
          · rcases m.htr 2 3 4 (by decide) (by decide) with h964 | h964
            · linarith only [h0, h4, h907, h962, h964, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · linarith only [h7, h906, h964, hc34, hlam, hphi, ht12, ht23, u1ehi4]
          · linarith only [h668, h906, h963, hlam]
        · linarith only [h7, h906, h962, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h969 | h969
      · rcases m.htr 1 3 5 (by decide) (by decide) with h970 | h970
        · rcases m.htr 1 4 5 (by decide) (by decide) with h971 | h971
          · rcases m.htr 2 3 4 (by decide) (by decide) with h972 | h972
            · rcases m.htr 2 3 5 (by decide) (by decide) with h973 | h973
              · rcases m.htr 2 4 5 (by decide) (by decide) with h974 | h974
                · rcases m.htr 3 4 5 (by decide) (by decide) with h975 | h975
                  · rcases h1bigk with h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c
                    · have p976_0 := h976c.1
                      have p976_1 := h976c.2.1
                      have p976_2 := h976c.2.2.1
                      have p976_3 := h976c.2.2.2
                      linarith only [hlam, p976_0]
                    · have p976_0 := h976c.1
                      have p976_1 := h976c.2.1
                      have p976_2 := h976c.2.2.1
                      have p976_3 := h976c.2.2.2
                      rcases p976_3 (m.d 0 1) (by simp) with h978 | h978
                      · rcases p976_3 (m.d 1 2) (by simp) with h979 | h979
                        · linarith only [h979, hlam, p976_0]
                        · rcases p976_3 (m.d 1 3) (by simp) with h981 | h981
                          · linarith only [h1, h981, hlam]
                          · linarith only [h7, h981, hlam]
                      · linarith only [h978, hlam, p976_0]
                    · have p976_0 := h976c.1
                      have p976_1 := h976c.2.1
                      have p976_2 := h976c.2.2.1
                      have p976_3 := h976c.2.2.2
                      linarith only [h969, h975, hc01, hc45, hlam, hphi, ht0b, ht5b, p976_1]
                    · have p976_0 := h976c.1
                      have p976_1 := h976c.2.1
                      have p976_2 := h976c.2.2.1
                      have p976_3 := h976c.2.2.2
                      rcases p976_3 (m.d 0 1) (by simp) with h986 | h986
                      · rcases p976_3 (m.d 1 2) (by simp) with h987 | h987
                        · linarith only [h0, h987, hlam]
                        · rcases p976_3 (m.d 1 3) (by simp) with h989 | h989
                          · linarith only [h1, h989, hlam]
                          · linarith only [h969, h989, hlam]
                      · linarith only [h986, hlam, p976_0]
                    · have p976_0 := h976c.1
                      have p976_1 := h976c.2.1
                      have p976_2 := h976c.2.2.1
                      have p976_3 := h976c.2.2.2
                      rcases p976_3 (m.d 0 1) (by simp) with h993 | h993
                      · rcases p976_3 (m.d 1 2) (by simp) with h994 | h994
                        · linarith only [h0, h994, hlam]
                        · rcases p976_3 (m.d 1 3) (by simp) with h996 | h996
                          · linarith only [h1, h996, hlam]
                          · linarith only [h970, h996, hlam]
                      · linarith only [h993, hlam, p976_0]
                    · have p976_0 := h976c.1
                      have p976_1 := h976c.2.1
                      have p976_2 := h976c.2.2.1
                      have p976_3 := h976c.2.2.2
                      linarith only [h0, hlam, p976_0]
                    · have p976_0 := h976c.1
                      have p976_1 := h976c.2.1
                      have p976_2 := h976c.2.2.1
                      have p976_3 := h976c.2.2.2
                      linarith only [hlam, p976_0]
                    · have p976_0 := h976c.1
                      have p976_1 := h976c.2.1
                      have p976_2 := h976c.2.2.1
                      have p976_3 := h976c.2.2.2
                      linarith only [h7, hlam, p976_0]
                    · have p976_0 := h976c.1
                      have p976_1 := h976c.2.1
                      have p976_2 := h976c.2.2.1
                      have p976_3 := h976c.2.2.2
                      linarith only [h668, hlam, p976_0]
                    · have p976_0 := h976c.1
                      have p976_1 := h976c.2.1
                      have p976_2 := h976c.2.2.1
                      have p976_3 := h976c.2.2.2
                      linarith only [h906, hlam, p976_0]
                    · have p976_0 := h976c.1
                      have p976_1 := h976c.2.1
                      have p976_2 := h976c.2.2.1
                      have p976_3 := h976c.2.2.2
                      linarith only [h1, hlam, p976_0]
                    · have p976_0 := h976c.1
                      have p976_1 := h976c.2.1
                      have p976_2 := h976c.2.2.1
                      have p976_3 := h976c.2.2.2
                      linarith only [hc13, hlam, hphi, p976_1, u1ehi1]
                    · have p976_0 := h976c.1
                      have p976_1 := h976c.2.1
                      have p976_2 := h976c.2.2.1
                      have p976_3 := h976c.2.2.2
                      linarith only [hlam, p976_0]
                    · have p976_0 := h976c.1
                      have p976_1 := h976c.2.1
                      have p976_2 := h976c.2.2.1
                      have p976_3 := h976c.2.2.2
                      linarith only [h906, h971, hc13, hlam, hphi, p976_1, u1ehi1]
                    · have p976_0 := h976c.1
                      have p976_1 := h976c.2.1
                      have p976_2 := h976c.2.2.1
                      have p976_3 := h976c.2.2.2
                      linarith only [h0, h4, h7, h906, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p976_1, u1ehi1]
                    · have p976_0 := h976c.1
                      have p976_1 := h976c.2.1
                      have p976_2 := h976c.2.2.1
                      have p976_3 := h976c.2.2.2
                      linarith only [h2, hlam, p976_0]
                    · have p976_0 := h976c.1
                      have p976_1 := h976c.2.1
                      have p976_2 := h976c.2.2.1
                      have p976_3 := h976c.2.2.2
                      linarith only [hc14, hlam, hphi, p976_1, u1ehi1]
                    · have p976_0 := h976c.1
                      have p976_1 := h976c.2.1
                      have p976_2 := h976c.2.2.1
                      have p976_3 := h976c.2.2.2
                      linarith only [h969, hlam, p976_0]
                    · have p976_0 := h976c.1
                      have p976_1 := h976c.2.1
                      have p976_2 := h976c.2.2.1
                      have p976_3 := h976c.2.2.2
                      linarith only [hlam, p976_0]
                    · have p976_0 := h976c.1
                      have p976_1 := h976c.2.1
                      have p976_2 := h976c.2.2.1
                      have p976_3 := h976c.2.2.2
                      linarith only [h0, h4, h668, h906, h972, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p976_1, u1ehi1]
                    · have p976_0 := h976c.1
                      have p976_1 := h976c.2.1
                      have p976_2 := h976c.2.2.1
                      have p976_3 := h976c.2.2.2
                      linarith only [h3, hlam, p976_0]
                    · have p976_0 := h976c.1
                      have p976_1 := h976c.2.1
                      have p976_2 := h976c.2.2.1
                      have p976_3 := h976c.2.2.2
                      linarith only [hc15, hlam, hphi, p976_1, u1ehi1]
                    · have p976_0 := h976c.1
                      have p976_1 := h976c.2.1
                      have p976_2 := h976c.2.2.1
                      have p976_3 := h976c.2.2.2
                      linarith only [h970, hlam, p976_0]
                    · have p976_0 := h976c.1
                      have p976_1 := h976c.2.1
                      have p976_2 := h976c.2.2.1
                      have p976_3 := h976c.2.2.2
                      linarith only [h971, hlam, p976_0]
                    · have p976_0 := h976c.1
                      have p976_1 := h976c.2.1
                      have p976_2 := h976c.2.2.1
                      have p976_3 := h976c.2.2.2
                      linarith only [hlam, p976_0]
                  · rcases h1bigk with h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c
                    · have p1020_0 := h1020c.1
                      have p1020_1 := h1020c.2.1
                      have p1020_2 := h1020c.2.2.1
                      have p1020_3 := h1020c.2.2.2
                      linarith only [hlam, p1020_0]
                    · have p1020_0 := h1020c.1
                      have p1020_1 := h1020c.2.1
                      have p1020_2 := h1020c.2.2.1
                      have p1020_3 := h1020c.2.2.2
                      rcases p1020_3 (m.d 0 1) (by simp) with h1022 | h1022
                      · rcases p1020_3 (m.d 1 2) (by simp) with h1023 | h1023
                        · linarith only [h1023, hlam, p1020_0]
                        · rcases p1020_3 (m.d 1 3) (by simp) with h1025 | h1025
                          · linarith only [h1, h1025, hlam]
                          · linarith only [h1025, h7, hlam]
                      · linarith only [h1022, hlam, p1020_0]
                    · have p1020_0 := h1020c.1
                      have p1020_1 := h1020c.2.1
                      have p1020_2 := h1020c.2.2.1
                      have p1020_3 := h1020c.2.2.2
                      linarith only [h969, h971, h975, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1020_1]
                    · have p1020_0 := h1020c.1
                      have p1020_1 := h1020c.2.1
                      have p1020_2 := h1020c.2.2.1
                      have p1020_3 := h1020c.2.2.2
                      linarith only [h971, h975, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1020_1]
                    · have p1020_0 := h1020c.1
                      have p1020_1 := h1020c.2.1
                      have p1020_2 := h1020c.2.2.1
                      have p1020_3 := h1020c.2.2.2
                      rcases p1020_3 (m.d 0 1) (by simp) with h1031 | h1031
                      · rcases p1020_3 (m.d 1 2) (by simp) with h1032 | h1032
                        · linarith only [h0, h1032, hlam]
                        · rcases p1020_3 (m.d 1 3) (by simp) with h1034 | h1034
                          · linarith only [h1, h1034, hlam]
                          · linarith only [h1034, h970, hlam]
                      · linarith only [h1031, hlam, p1020_0]
                    · have p1020_0 := h1020c.1
                      have p1020_1 := h1020c.2.1
                      have p1020_2 := h1020c.2.2.1
                      have p1020_3 := h1020c.2.2.2
                      linarith only [h0, hlam, p1020_0]
                    · have p1020_0 := h1020c.1
                      have p1020_1 := h1020c.2.1
                      have p1020_2 := h1020c.2.2.1
                      have p1020_3 := h1020c.2.2.2
                      linarith only [hlam, p1020_0]
                    · have p1020_0 := h1020c.1
                      have p1020_1 := h1020c.2.1
                      have p1020_2 := h1020c.2.2.1
                      have p1020_3 := h1020c.2.2.2
                      linarith only [h7, hlam, p1020_0]
                    · have p1020_0 := h1020c.1
                      have p1020_1 := h1020c.2.1
                      have p1020_2 := h1020c.2.2.1
                      have p1020_3 := h1020c.2.2.2
                      linarith only [h668, hlam, p1020_0]
                    · have p1020_0 := h1020c.1
                      have p1020_1 := h1020c.2.1
                      have p1020_2 := h1020c.2.2.1
                      have p1020_3 := h1020c.2.2.2
                      linarith only [h906, hlam, p1020_0]
                    · have p1020_0 := h1020c.1
                      have p1020_1 := h1020c.2.1
                      have p1020_2 := h1020c.2.2.1
                      have p1020_3 := h1020c.2.2.2
                      linarith only [h1, hlam, p1020_0]
                    · have p1020_0 := h1020c.1
                      have p1020_1 := h1020c.2.1
                      have p1020_2 := h1020c.2.2.1
                      have p1020_3 := h1020c.2.2.2
                      linarith only [hc13, hlam, hphi, p1020_1, u1ehi1]
                    · have p1020_0 := h1020c.1
                      have p1020_1 := h1020c.2.1
                      have p1020_2 := h1020c.2.2.1
                      have p1020_3 := h1020c.2.2.2
                      linarith only [hlam, p1020_0]
                    · have p1020_0 := h1020c.1
                      have p1020_1 := h1020c.2.1
                      have p1020_2 := h1020c.2.2.1
                      have p1020_3 := h1020c.2.2.2
                      linarith only [h0, h4, h7, h971, h975, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1020_1]
                    · have p1020_0 := h1020c.1
                      have p1020_1 := h1020c.2.1
                      have p1020_2 := h1020c.2.2.1
                      have p1020_3 := h1020c.2.2.2
                      linarith only [h0, h4, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1020_1, u1ehi4]
                    · have p1020_0 := h1020c.1
                      have p1020_1 := h1020c.2.1
                      have p1020_2 := h1020c.2.2.1
                      have p1020_3 := h1020c.2.2.2
                      linarith only [h2, hlam, p1020_0]
                    · have p1020_0 := h1020c.1
                      have p1020_1 := h1020c.2.1
                      have p1020_2 := h1020c.2.2.1
                      have p1020_3 := h1020c.2.2.2
                      linarith only [hc14, hlam, hphi, p1020_1, u1ehi1]
                    · have p1020_0 := h1020c.1
                      have p1020_1 := h1020c.2.1
                      have p1020_2 := h1020c.2.2.1
                      have p1020_3 := h1020c.2.2.2
                      linarith only [h969, hlam, p1020_0]
                    · have p1020_0 := h1020c.1
                      have p1020_1 := h1020c.2.1
                      have p1020_2 := h1020c.2.2.1
                      have p1020_3 := h1020c.2.2.2
                      linarith only [hlam, p1020_0]
                    · have p1020_0 := h1020c.1
                      have p1020_1 := h1020c.2.1
                      have p1020_2 := h1020c.2.2.1
                      have p1020_3 := h1020c.2.2.2
                      linarith only [h0, h4, h668, h906, h972, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1020_1, u1ehi1]
                    · have p1020_0 := h1020c.1
                      have p1020_1 := h1020c.2.1
                      have p1020_2 := h1020c.2.2.1
                      have p1020_3 := h1020c.2.2.2
                      linarith only [h3, hlam, p1020_0]
                    · have p1020_0 := h1020c.1
                      have p1020_1 := h1020c.2.1
                      have p1020_2 := h1020c.2.2.1
                      have p1020_3 := h1020c.2.2.2
                      linarith only [hc15, hlam, hphi, p1020_1, u1ehi1]
                    · have p1020_0 := h1020c.1
                      have p1020_1 := h1020c.2.1
                      have p1020_2 := h1020c.2.2.1
                      have p1020_3 := h1020c.2.2.2
                      linarith only [h970, hlam, p1020_0]
                    · have p1020_0 := h1020c.1
                      have p1020_1 := h1020c.2.1
                      have p1020_2 := h1020c.2.2.1
                      have p1020_3 := h1020c.2.2.2
                      linarith only [h971, hlam, p1020_0]
                    · have p1020_0 := h1020c.1
                      have p1020_1 := h1020c.2.1
                      have p1020_2 := h1020c.2.2.1
                      have p1020_3 := h1020c.2.2.2
                      linarith only [hlam, p1020_0]
                · linarith only [h2, h6, h668, h974, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
              · linarith only [h0, h4, h5, h7, h973, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
            · linarith only [h7, h972, hc34, hlam, hphi, ht12, ht23, u1ehi1]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1061 | h1061
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1062 | h1062
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1063 | h1063
                · linarith only [h1063, h668, h971, hc24, hlam, hphi, ht12, u1ehi1]
                · linarith only [h1063, h2, h6, h668, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
              · linarith only [h1062, h7, h970, hlam]
            · linarith only [h1061, h7, h969, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1068 | h1068
          · linarith only [h1068, h969, h970, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1070 | h1070
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1071 | h1071
              · linarith only [h0, h1071, h4, h969, h970, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h1071, h7, hc35, hlam, hphi, ht12, ht23, u1ehi1]
            · linarith only [h1070, h7, hc34, hlam, hphi, ht12, ht23, u1ehi1]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1075 | h1075
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1076 | h1076
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1077 | h1077
            · linarith only [h1077, h969, hc23, hlam, hphi, ht12, u1ehi2]
            · linarith only [h1077, h7, hc34, hlam, hphi, ht12, ht23, u1ehi1]
          · linarith only [h1075, h1076, h969, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1081 | h1081
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1082 | h1082
            · linarith only [h1082, h969, hc23, hlam, hphi, ht12, u1ehi2]
            · linarith only [h1082, h7, hc34, hlam, hphi, ht12, ht23, u1ehi1]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1085 | h1085
            · linarith only [h1085, h7, h969, hc23, hlam, hphi, ht12, u1ehi1]
            · linarith only [h1085, h7, hc34, hlam, hphi, ht12, ht23, u1ehi1]

set_option maxHeartbeats 5626000 in
set_option maxHeartbeats 5626000 in
theorem r1l7_21_15_M_IR_L_I_s3_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h6 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
  · exact r1l7_21_15_M_IR_L_I_s3_x0_x0_x0_x0 m hb1 hb5 hg0 hg1 hg2 hg3 h4 h5 h6 h7
  · exact r1l7_21_15_M_IR_L_I_s3_x0_x0_x0_x1 m hb1 hb5 hg0 hg1 hg2 hg3 h4 h5 h6 h7

end R2N4
