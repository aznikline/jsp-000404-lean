import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3900000 in
set_option maxHeartbeats 3900000 in
theorem r1l7_20_12_H_I_L_R_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h658 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h2ehi := hb2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h659 | h659
  · rcases m.htr 0 1 5 (by decide) (by decide) with h660 | h660
    · rcases m.htr 0 2 3 (by decide) (by decide) with h661 | h661
      · rcases m.htr 0 2 4 (by decide) (by decide) with h662 | h662
        · rcases m.htr 0 2 5 (by decide) (by decide) with h663 | h663
          · rcases m.htr 0 3 4 (by decide) (by decide) with h664 | h664
            · rcases m.htr 0 3 5 (by decide) (by decide) with h665 | h665
              · rcases m.htr 0 4 5 (by decide) (by decide) with h666 | h666
                · rcases m.htr 1 2 3 (by decide) (by decide) with h667 | h667
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h668 | h668
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h669 | h669
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h670 | h670
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h671 | h671
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h672 | h672
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h673 | h673
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h674 | h674
                                · linarith only [h0, h658, h667, h672, h674, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h0, h658, h670, h671, h674, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h0, h658, h670, h671, h673, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h0, h658, h664, h672, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · linarith only [h0, h658, h664, h666, h668, h671, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                        · linarith only [h0, h658, h664, h667, h670, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h658, h667, h669, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h0, h658, h663, h664, h666, h668, hc24, hlam, hphi, u2ehi4]
                  · linarith only [h0, h658, h663, h664, h666, h667, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h684 | h684
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h685 | h685
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h686 | h686
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h687 | h687
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h688 | h688
                          · linarith only [h0, h658, h666, h687, h688, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h690 | h690
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h691 | h691
                              · linarith only [h659, h666, h685, h691, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h693 | h693
                                · linarith only [h0, h658, h666, h684, h690, h693, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases h0bigk with h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [hlam, p695_0]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h0, hlam, p695_1]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p695_1]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h0, h659, h685, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p695_1, u2ehi3]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p695_1]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p695_1]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [hlam, p695_0]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h0, h658, h684, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p695_1, u2ehi2]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h0, h659, h685, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p695_1, u2ehi3]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h0, h660, h686, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p695_1, u2ehi4]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h658, hlam, p695_1]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h661, hlam, p695_1]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [hlam, p695_0]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h659, h685, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p695_1, u2ehi3]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h0, h658, h660, h686, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p695_1, u2ehi4]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h659, hlam, p695_0]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h662, hlam, p695_0]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h664, hlam, p695_0]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [hlam, p695_0]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h666, hlam, p695_0]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h660, hlam, p695_0]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h663, hlam, p695_1]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h665, hlam, p695_0]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h659, h685, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p695_1, u2ehi3]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [hlam, p695_0]
                            · linarith only [h0, h658, h664, h690, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h0, h658, h664, h684, h687, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h658, h684, h686, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h0, h658, h684, h685, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h658, h663, h665, h684, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h726 | h726
                · linarith only [h664, h665, h726, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h728 | h728
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h729 | h729
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h730 | h730
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h731 | h731
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h732 | h732
                          · linarith only [h0, h658, h726, h731, h732, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h734 | h734
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h735 | h735
                              · linarith only [h659, h726, h729, h735, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h737 | h737
                                · linarith only [h659, h726, h729, h734, h737, hc23, hlam, hphi, u2ehi3]
                                · rcases h0bigk with h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c | h739c
                                  · have p739_0 := h739c.1
                                    have p739_1 := h739c.2.1
                                    have p739_2 := h739c.2.2.1
                                    have p739_3 := h739c.2.2.2
                                    linarith only [hlam, p739_0]
                                  · have p739_0 := h739c.1
                                    have p739_1 := h739c.2.1
                                    have p739_2 := h739c.2.2.1
                                    have p739_3 := h739c.2.2.2
                                    linarith only [h0, hlam, p739_1]
                                  · have p739_0 := h739c.1
                                    have p739_1 := h739c.2.1
                                    have p739_2 := h739c.2.2.1
                                    have p739_3 := h739c.2.2.2
                                    linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p739_1]
                                  · have p739_0 := h739c.1
                                    have p739_1 := h739c.2.1
                                    have p739_2 := h739c.2.2.1
                                    have p739_3 := h739c.2.2.2
                                    linarith only [h0, h659, h729, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p739_1, u2ehi3]
                                  · have p739_0 := h739c.1
                                    have p739_1 := h739c.2.1
                                    have p739_2 := h739c.2.2.1
                                    have p739_3 := h739c.2.2.2
                                    linarith only [h0, h665, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p739_1]
                                  · have p739_0 := h739c.1
                                    have p739_1 := h739c.2.1
                                    have p739_2 := h739c.2.2.1
                                    have p739_3 := h739c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p739_1]
                                  · have p739_0 := h739c.1
                                    have p739_1 := h739c.2.1
                                    have p739_2 := h739c.2.2.1
                                    have p739_3 := h739c.2.2.2
                                    linarith only [hlam, p739_0]
                                  · have p739_0 := h739c.1
                                    have p739_1 := h739c.2.1
                                    have p739_2 := h739c.2.2.1
                                    have p739_3 := h739c.2.2.2
                                    linarith only [h0, h658, h728, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p739_1, u2ehi2]
                                  · have p739_0 := h739c.1
                                    have p739_1 := h739c.2.1
                                    have p739_2 := h739c.2.2.1
                                    have p739_3 := h739c.2.2.2
                                    linarith only [h0, h659, h729, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p739_1, u2ehi3]
                                  · have p739_0 := h739c.1
                                    have p739_1 := h739c.2.1
                                    have p739_2 := h739c.2.2.1
                                    have p739_3 := h739c.2.2.2
                                    linarith only [h0, h658, h665, h728, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p739_1, u2ehi2]
                                  · have p739_0 := h739c.1
                                    have p739_1 := h739c.2.1
                                    have p739_2 := h739c.2.2.1
                                    have p739_3 := h739c.2.2.2
                                    linarith only [h658, hlam, p739_1]
                                  · have p739_0 := h739c.1
                                    have p739_1 := h739c.2.1
                                    have p739_2 := h739c.2.2.1
                                    have p739_3 := h739c.2.2.2
                                    linarith only [h661, hlam, p739_1]
                                  · have p739_0 := h739c.1
                                    have p739_1 := h739c.2.1
                                    have p739_2 := h739c.2.2.1
                                    have p739_3 := h739c.2.2.2
                                    linarith only [hlam, p739_0]
                                  · have p739_0 := h739c.1
                                    have p739_1 := h739c.2.1
                                    have p739_2 := h739c.2.2.1
                                    have p739_3 := h739c.2.2.2
                                    linarith only [h659, h729, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p739_1, u2ehi3]
                                  · have p739_0 := h739c.1
                                    have p739_1 := h739c.2.1
                                    have p739_2 := h739c.2.2.1
                                    have p739_3 := h739c.2.2.2
                                    linarith only [h665, hlam, p739_1]
                                  · have p739_0 := h739c.1
                                    have p739_1 := h739c.2.1
                                    have p739_2 := h739c.2.2.1
                                    have p739_3 := h739c.2.2.2
                                    linarith only [h659, hlam, p739_0]
                                  · have p739_0 := h739c.1
                                    have p739_1 := h739c.2.1
                                    have p739_2 := h739c.2.2.1
                                    have p739_3 := h739c.2.2.2
                                    linarith only [h662, hlam, p739_0]
                                  · have p739_0 := h739c.1
                                    have p739_1 := h739c.2.1
                                    have p739_2 := h739c.2.2.1
                                    have p739_3 := h739c.2.2.2
                                    linarith only [h664, hlam, p739_0]
                                  · have p739_0 := h739c.1
                                    have p739_1 := h739c.2.1
                                    have p739_2 := h739c.2.2.1
                                    have p739_3 := h739c.2.2.2
                                    linarith only [hlam, p739_0]
                                  · have p739_0 := h739c.1
                                    have p739_1 := h739c.2.1
                                    have p739_2 := h739c.2.2.1
                                    have p739_3 := h739c.2.2.2
                                    linarith only [h726, hlam, p739_0]
                                  · have p739_0 := h739c.1
                                    have p739_1 := h739c.2.1
                                    have p739_2 := h739c.2.2.1
                                    have p739_3 := h739c.2.2.2
                                    linarith only [h660, hlam, p739_0]
                                  · have p739_0 := h739c.1
                                    have p739_1 := h739c.2.1
                                    have p739_2 := h739c.2.2.1
                                    have p739_3 := h739c.2.2.2
                                    linarith only [h663, hlam, p739_1]
                                  · have p739_0 := h739c.1
                                    have p739_1 := h739c.2.1
                                    have p739_2 := h739c.2.2.1
                                    have p739_3 := h739c.2.2.2
                                    linarith only [h658, h728, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p739_1, u2ehi2]
                                  · have p739_0 := h739c.1
                                    have p739_1 := h739c.2.1
                                    have p739_2 := h739c.2.2.1
                                    have p739_3 := h739c.2.2.2
                                    linarith only [h659, h660, h729, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p739_1, u2ehi3]
                                  · have p739_0 := h739c.1
                                    have p739_1 := h739c.2.1
                                    have p739_2 := h739c.2.2.1
                                    have p739_3 := h739c.2.2.2
                                    linarith only [hlam, p739_0]
                            · linarith only [h0, h658, h664, h734, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h664, h665, h731, hc13, hc35, hlam, hphi]
                      · linarith only [h0, h658, h728, h730, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h0, h658, h728, h729, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h658, h662, h664, h728, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h770 | h770
              · rcases m.htr 0 4 5 (by decide) (by decide) with h771 | h771
                · rcases m.htr 1 2 3 (by decide) (by decide) with h772 | h772
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h773 | h773
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h774 | h774
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h775 | h775
                        · linarith only [h0, h658, h664, h775, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h777 | h777
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h778 | h778
                            · linarith only [h660, h664, h770, h774, h778, hc23, hlam, hphi, u2ehi4]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h780 | h780
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h781 | h781
                                · rcases h0bigk with h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [hlam, p782_0]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h0, hlam, p782_1]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h0, h660, h770, h774, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p782_1, u2ehi4]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p782_1]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h0, h660, h774, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p782_1, u2ehi4]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p782_1]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [hlam, p782_0]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h0, h660, h770, h774, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p782_1, u2ehi4]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h0, h659, h773, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p782_1, u2ehi3]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h0, h660, h774, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p782_1, u2ehi4]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h658, hlam, p782_1]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h661, hlam, p782_1]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [hlam, p782_0]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h664, hlam, p782_1]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h660, h774, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p782_1, u2ehi4]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h659, hlam, p782_0]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h662, hlam, p782_0]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h770, hc04, hc35, hlam, hphi, ht0b, ht5b, p782_1]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [hlam, p782_0]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h0, h659, h660, h774, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p782_1, u2ehi4]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h660, hlam, p782_0]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h663, hlam, p782_1]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h770, hlam, p782_0]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h771, hlam, p782_1]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [hlam, p782_0]
                                · linarith only [h661, h664, h781, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                              · linarith only [h0, h659, h777, h778, h780, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · linarith only [h664, h770, h771, h773, h777, hc34, hlam, hphi, ht23, u2ehi3]
                      · linarith only [h0, h659, h773, h774, hc25, hlam, hphi, u2ehi3]
                    · linarith only [h0, h658, h772, h773, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h662, h772, hc23, hlam, hphi, u2ehi3]
                · linarith only [h664, h770, h771, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h815 | h815
                · rcases m.htr 1 2 3 (by decide) (by decide) with h816 | h816
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h817 | h817
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h818 | h818
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h819 | h819
                        · linarith only [h0, h658, h664, h819, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h821 | h821
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h822 | h822
                            · linarith only [h658, h664, h816, h822, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h824 | h824
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h825 | h825
                                · rcases h0bigk with h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c
                                  · have p826_0 := h826c.1
                                    have p826_1 := h826c.2.1
                                    have p826_2 := h826c.2.2.1
                                    have p826_3 := h826c.2.2.2
                                    linarith only [hlam, p826_0]
                                  · have p826_0 := h826c.1
                                    have p826_1 := h826c.2.1
                                    have p826_2 := h826c.2.2.1
                                    have p826_3 := h826c.2.2.2
                                    linarith only [h0, hlam, p826_1]
                                  · have p826_0 := h826c.1
                                    have p826_1 := h826c.2.1
                                    have p826_2 := h826c.2.2.1
                                    have p826_3 := h826c.2.2.2
                                    linarith only [h0, h658, h816, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p826_1, u2ehi2]
                                  · have p826_0 := h826c.1
                                    have p826_1 := h826c.2.1
                                    have p826_2 := h826c.2.2.1
                                    have p826_3 := h826c.2.2.2
                                    linarith only [h0, h658, h770, h815, h816, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p826_1, u2ehi2]
                                  · have p826_0 := h826c.1
                                    have p826_1 := h826c.2.1
                                    have p826_2 := h826c.2.2.1
                                    have p826_3 := h826c.2.2.2
                                    linarith only [h0, h658, h770, h816, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p826_1, u2ehi2]
                                  · have p826_0 := h826c.1
                                    have p826_1 := h826c.2.1
                                    have p826_2 := h826c.2.2.1
                                    have p826_3 := h826c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p826_1]
                                  · have p826_0 := h826c.1
                                    have p826_1 := h826c.2.1
                                    have p826_2 := h826c.2.2.1
                                    have p826_3 := h826c.2.2.2
                                    linarith only [hlam, p826_0]
                                  · have p826_0 := h826c.1
                                    have p826_1 := h826c.2.1
                                    have p826_2 := h826c.2.2.1
                                    have p826_3 := h826c.2.2.2
                                    linarith only [h0, h658, h816, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p826_1, u2ehi2]
                                  · have p826_0 := h826c.1
                                    have p826_1 := h826c.2.1
                                    have p826_2 := h826c.2.2.1
                                    have p826_3 := h826c.2.2.2
                                    linarith only [h0, h658, h770, h815, h816, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p826_1, u2ehi2]
                                  · have p826_0 := h826c.1
                                    have p826_1 := h826c.2.1
                                    have p826_2 := h826c.2.2.1
                                    have p826_3 := h826c.2.2.2
                                    linarith only [h0, h658, h770, h816, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p826_1, u2ehi2]
                                  · have p826_0 := h826c.1
                                    have p826_1 := h826c.2.1
                                    have p826_2 := h826c.2.2.1
                                    have p826_3 := h826c.2.2.2
                                    linarith only [h658, hlam, p826_1]
                                  · have p826_0 := h826c.1
                                    have p826_1 := h826c.2.1
                                    have p826_2 := h826c.2.2.1
                                    have p826_3 := h826c.2.2.2
                                    linarith only [h661, hlam, p826_1]
                                  · have p826_0 := h826c.1
                                    have p826_1 := h826c.2.1
                                    have p826_2 := h826c.2.2.1
                                    have p826_3 := h826c.2.2.2
                                    linarith only [hlam, p826_0]
                                  · have p826_0 := h826c.1
                                    have p826_1 := h826c.2.1
                                    have p826_2 := h826c.2.2.1
                                    have p826_3 := h826c.2.2.2
                                    linarith only [h664, hlam, p826_1]
                                  · have p826_0 := h826c.1
                                    have p826_1 := h826c.2.1
                                    have p826_2 := h826c.2.2.1
                                    have p826_3 := h826c.2.2.2
                                    linarith only [h770, hlam, p826_1]
                                  · have p826_0 := h826c.1
                                    have p826_1 := h826c.2.1
                                    have p826_2 := h826c.2.2.1
                                    have p826_3 := h826c.2.2.2
                                    linarith only [h659, hlam, p826_0]
                                  · have p826_0 := h826c.1
                                    have p826_1 := h826c.2.1
                                    have p826_2 := h826c.2.2.1
                                    have p826_3 := h826c.2.2.2
                                    linarith only [h662, hlam, p826_0]
                                  · have p826_0 := h826c.1
                                    have p826_1 := h826c.2.1
                                    have p826_2 := h826c.2.2.1
                                    have p826_3 := h826c.2.2.2
                                    linarith only [h658, h816, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p826_1, u2ehi2]
                                  · have p826_0 := h826c.1
                                    have p826_1 := h826c.2.1
                                    have p826_2 := h826c.2.2.1
                                    have p826_3 := h826c.2.2.2
                                    linarith only [hlam, p826_0]
                                  · have p826_0 := h826c.1
                                    have p826_1 := h826c.2.1
                                    have p826_2 := h826c.2.2.1
                                    have p826_3 := h826c.2.2.2
                                    linarith only [h658, h659, h770, h816, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p826_1, u2ehi2]
                                  · have p826_0 := h826c.1
                                    have p826_1 := h826c.2.1
                                    have p826_2 := h826c.2.2.1
                                    have p826_3 := h826c.2.2.2
                                    linarith only [h660, hlam, p826_0]
                                  · have p826_0 := h826c.1
                                    have p826_1 := h826c.2.1
                                    have p826_2 := h826c.2.2.1
                                    have p826_3 := h826c.2.2.2
                                    linarith only [h663, hlam, p826_1]
                                  · have p826_0 := h826c.1
                                    have p826_1 := h826c.2.1
                                    have p826_2 := h826c.2.2.1
                                    have p826_3 := h826c.2.2.2
                                    linarith only [h658, h816, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p826_1, u2ehi2]
                                  · have p826_0 := h826c.1
                                    have p826_1 := h826c.2.1
                                    have p826_2 := h826c.2.2.1
                                    have p826_3 := h826c.2.2.2
                                    linarith only [h815, hlam, p826_1]
                                  · have p826_0 := h826c.1
                                    have p826_1 := h826c.2.1
                                    have p826_2 := h826c.2.2.1
                                    have p826_3 := h826c.2.2.2
                                    linarith only [hlam, p826_0]
                                · linarith only [h658, h664, h816, h825, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                              · linarith only [h0, h659, h821, h822, h824, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · linarith only [h664, h815, h817, h821, hc34, hlam, hphi, ht23, u2ehi3]
                      · linarith only [h0, h658, h816, h818, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h0, h658, h816, h817, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h659, h662, h816, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h858 | h858
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h859 | h859
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h860 | h860
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h861 | h861
                        · linarith only [h658, h664, h861, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h863 | h863
                          · linarith only [h0, h659, h664, h815, h863, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h865 | h865
                            · linarith only [h658, h664, h858, h865, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h867 | h867
                              · linarith only [h658, h664, h815, h858, h867, hc24, hlam, hphi, u2ehi2]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h869 | h869
                                · linarith only [h658, h664, h815, h858, h869, hc34, hlam, hphi, ht23, u2ehi2]
                                · linarith only [h658, h664, h858, h869, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h0, h658, h858, h860, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h0, h658, h858, h859, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h659, h662, h858, hc23, hlam, hphi, u2ehi3]
          · linarith only [h661, h663, hc25, hlam, hphi, u2ehi2]
        · linarith only [h661, h662, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h658, h661, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h878 | h878
      · rcases m.htr 0 2 4 (by decide) (by decide) with h879 | h879
        · rcases m.htr 0 2 5 (by decide) (by decide) with h880 | h880
          · rcases m.htr 0 3 4 (by decide) (by decide) with h881 | h881
            · rcases m.htr 0 3 5 (by decide) (by decide) with h882 | h882
              · linarith only [h658, h660, h882, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h884 | h884
                · linarith only [h658, h660, h881, h884, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h886 | h886
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h887 | h887
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h888 | h888
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h889 | h889
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h890 | h890
                          · linarith only [h658, h660, h884, h888, h889, h890, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h658, h660, h889, h890, hc34, hc45, hlam, hphi]
                        · linarith only [h881, h882, h889, hc13, hc35, hlam, hphi]
                      · linarith only [h0, h659, h887, h888, hc25, hlam, hphi, u2ehi3]
                    · linarith only [h0, h880, h887, hc24, hlam, hphi, u2ehi4]
                  · linarith only [h0, h658, h879, h881, h886, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h897 | h897
              · linarith only [h658, h660, h897, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h899 | h899
                · linarith only [h659, h660, h899, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h901 | h901
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h902 | h902
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h903 | h903
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h904 | h904
                        · linarith only [h658, h881, h904, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h906 | h906
                          · linarith only [h659, h660, h899, h906, hlam]
                          · linarith only [h659, h660, h901, h904, h906, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h0, h658, h901, h903, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h0, h658, h901, h902, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h880, h901, hc23, hlam, hphi, u2ehi4]
          · linarith only [h878, h880, hc25, hlam, hphi, u2ehi2]
        · linarith only [h878, h879, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h658, h878, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h915 | h915
    · rcases m.htr 0 2 3 (by decide) (by decide) with h916 | h916
      · rcases m.htr 0 2 4 (by decide) (by decide) with h917 | h917
        · rcases m.htr 0 2 5 (by decide) (by decide) with h918 | h918
          · rcases m.htr 0 3 4 (by decide) (by decide) with h919 | h919
            · linarith only [h658, h659, h919, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h921 | h921
              · rcases m.htr 0 4 5 (by decide) (by decide) with h922 | h922
                · rcases m.htr 1 2 3 (by decide) (by decide) with h923 | h923
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h924 | h924
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h925 | h925
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h926 | h926
                        · linarith only [h658, h659, h919, h926, hlam]
                        · linarith only [h658, h659, h923, h926, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h658, h659, h923, h924, h925, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h0, h658, h917, h923, h924, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h0, h658, h918, h921, h923, hc23, hlam, hphi, u2ehi4]
                · linarith only [h658, h659, h921, h922, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h933 | h933
                · rcases m.htr 1 2 3 (by decide) (by decide) with h934 | h934
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h935 | h935
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h936 | h936
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h937 | h937
                        · linarith only [h658, h919, h937, hlam]
                        · linarith only [h658, h659, h934, h937, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h658, h659, h934, h935, h936, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h0, h658, h934, h935, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h917, h934, hc23, hlam, hphi, u2ehi3]
                · linarith only [h659, h915, h933, hlam]
          · linarith only [h916, h918, hc25, hlam, hphi, u2ehi2]
        · linarith only [h916, h917, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h658, h916, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h947 | h947
      · rcases m.htr 0 2 4 (by decide) (by decide) with h948 | h948
        · rcases m.htr 0 2 5 (by decide) (by decide) with h949 | h949
          · rcases m.htr 0 3 4 (by decide) (by decide) with h950 | h950
            · linarith only [h658, h659, h950, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h952 | h952
              · linarith only [h658, h915, h952, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h954 | h954
                · rcases m.htr 1 2 3 (by decide) (by decide) with h955 | h955
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h956 | h956
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h957 | h957
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h958 | h958
                        · linarith only [h658, h659, h950, h956, h958, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h658, h659, h955, h958, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h658, h659, h949, h955, h956, h957, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h658, h948, h955, h956, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h0, h948, h955, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h964 | h964
                  · linarith only [h658, h659, h954, h964, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h0, h949, h964, hc23, hlam, hphi, u2ehi4]
          · linarith only [h947, h949, hc25, hlam, hphi, u2ehi2]
        · linarith only [h947, h948, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h658, h947, hlam]

set_option maxHeartbeats 3900000 in
set_option maxHeartbeats 3900000 in
theorem r1l7_20_12_H_I_L_R_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h658 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h970 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h2ehi := hb2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h971 | h971
  · rcases m.htr 0 2 3 (by decide) (by decide) with h972 | h972
    · rcases m.htr 0 2 4 (by decide) (by decide) with h973 | h973
      · rcases m.htr 0 2 5 (by decide) (by decide) with h974 | h974
        · rcases m.htr 0 3 4 (by decide) (by decide) with h975 | h975
          · rcases m.htr 0 3 5 (by decide) (by decide) with h976 | h976
            · rcases m.htr 0 4 5 (by decide) (by decide) with h977 | h977
              · rcases m.htr 1 2 3 (by decide) (by decide) with h978 | h978
                · rcases m.htr 1 2 4 (by decide) (by decide) with h979 | h979
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h980 | h980
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h981 | h981
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h982 | h982
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h983 | h983
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h984 | h984
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h985 | h985
                              · rcases h0bigk with h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c
                                · have p986_0 := h986c.1
                                  have p986_1 := h986c.2.1
                                  have p986_2 := h986c.2.2.1
                                  have p986_3 := h986c.2.2.2
                                  linarith only [hlam, p986_0]
                                · have p986_0 := h986c.1
                                  have p986_1 := h986c.2.1
                                  have p986_2 := h986c.2.2.1
                                  have p986_3 := h986c.2.2.2
                                  linarith only [h0, hlam, p986_1]
                                · have p986_0 := h986c.1
                                  have p986_1 := h986c.2.1
                                  have p986_2 := h986c.2.2.1
                                  have p986_3 := h986c.2.2.2
                                  linarith only [h658, hlam, p986_0]
                                · have p986_0 := h986c.1
                                  have p986_1 := h986c.2.1
                                  have p986_2 := h986c.2.2.1
                                  have p986_3 := h986c.2.2.2
                                  linarith only [h658, h978, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p986_1]
                                · have p986_0 := h986c.1
                                  have p986_1 := h986c.2.1
                                  have p986_2 := h986c.2.2.1
                                  have p986_3 := h986c.2.2.2
                                  linarith only [h658, h978, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p986_1]
                                · have p986_0 := h986c.1
                                  have p986_1 := h986c.2.1
                                  have p986_2 := h986c.2.2.1
                                  have p986_3 := h986c.2.2.2
                                  linarith only [h970, h980, h982, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p986_1, u2ehi4]
                                · have p986_0 := h986c.1
                                  have p986_1 := h986c.2.1
                                  have p986_2 := h986c.2.2.1
                                  have p986_3 := h986c.2.2.2
                                  linarith only [hlam, p986_0]
                                · have p986_0 := h986c.1
                                  have p986_1 := h986c.2.1
                                  have p986_2 := h986c.2.2.1
                                  have p986_3 := h986c.2.2.2
                                  linarith only [h0, h658, h970, h980, h982, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p986_1, u2ehi4]
                                · have p986_0 := h986c.1
                                  have p986_1 := h986c.2.1
                                  have p986_2 := h986c.2.2.1
                                  have p986_3 := h986c.2.2.2
                                  linarith only [h0, h970, h980, h982, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p986_1, u2ehi4]
                                · have p986_0 := h986c.1
                                  have p986_1 := h986c.2.1
                                  have p986_2 := h986c.2.2.1
                                  have p986_3 := h986c.2.2.2
                                  linarith only [h0, h971, h980, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p986_1, u2ehi4]
                                · have p986_0 := h986c.1
                                  have p986_1 := h986c.2.1
                                  have p986_2 := h986c.2.2.1
                                  have p986_3 := h986c.2.2.2
                                  linarith only [h970, h980, h982, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p986_1, u2ehi4]
                                · have p986_0 := h986c.1
                                  have p986_1 := h986c.2.1
                                  have p986_2 := h986c.2.2.1
                                  have p986_3 := h986c.2.2.2
                                  linarith only [h972, hlam, p986_1]
                                · have p986_0 := h986c.1
                                  have p986_1 := h986c.2.1
                                  have p986_2 := h986c.2.2.1
                                  have p986_3 := h986c.2.2.2
                                  linarith only [hlam, p986_0]
                                · have p986_0 := h986c.1
                                  have p986_1 := h986c.2.1
                                  have p986_2 := h986c.2.2.1
                                  have p986_3 := h986c.2.2.2
                                  linarith only [h0, h970, h972, h980, h982, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p986_1, u2ehi4]
                                · have p986_0 := h986c.1
                                  have p986_1 := h986c.2.1
                                  have p986_2 := h986c.2.2.1
                                  have p986_3 := h986c.2.2.2
                                  linarith only [h0, h971, h972, h980, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p986_1, u2ehi4]
                                · have p986_0 := h986c.1
                                  have p986_1 := h986c.2.1
                                  have p986_2 := h986c.2.2.1
                                  have p986_3 := h986c.2.2.2
                                  linarith only [h970, hlam, p986_0]
                                · have p986_0 := h986c.1
                                  have p986_1 := h986c.2.1
                                  have p986_2 := h986c.2.2.1
                                  have p986_3 := h986c.2.2.2
                                  linarith only [h973, hlam, p986_0]
                                · have p986_0 := h986c.1
                                  have p986_1 := h986c.2.1
                                  have p986_2 := h986c.2.2.1
                                  have p986_3 := h986c.2.2.2
                                  linarith only [h975, hlam, p986_0]
                                · have p986_0 := h986c.1
                                  have p986_1 := h986c.2.1
                                  have p986_2 := h986c.2.2.1
                                  have p986_3 := h986c.2.2.2
                                  linarith only [hlam, p986_0]
                                · have p986_0 := h986c.1
                                  have p986_1 := h986c.2.1
                                  have p986_2 := h986c.2.2.1
                                  have p986_3 := h986c.2.2.2
                                  linarith only [h971, h980, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p986_1, u2ehi4]
                                · have p986_0 := h986c.1
                                  have p986_1 := h986c.2.1
                                  have p986_2 := h986c.2.2.1
                                  have p986_3 := h986c.2.2.2
                                  linarith only [h971, hlam, p986_0]
                                · have p986_0 := h986c.1
                                  have p986_1 := h986c.2.1
                                  have p986_2 := h986c.2.2.1
                                  have p986_3 := h986c.2.2.2
                                  linarith only [h974, hlam, p986_1]
                                · have p986_0 := h986c.1
                                  have p986_1 := h986c.2.1
                                  have p986_2 := h986c.2.2.1
                                  have p986_3 := h986c.2.2.2
                                  linarith only [h976, hlam, p986_0]
                                · have p986_0 := h986c.1
                                  have p986_1 := h986c.2.1
                                  have p986_2 := h986c.2.2.1
                                  have p986_3 := h986c.2.2.2
                                  linarith only [h977, hlam, p986_1]
                                · have p986_0 := h986c.1
                                  have p986_1 := h986c.2.1
                                  have p986_2 := h986c.2.2.1
                                  have p986_3 := h986c.2.2.2
                                  linarith only [hlam, p986_0]
                              · linarith only [h658, h970, h978, h982, h985, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h658, h970, h978, h982, h984, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h658, h970, h978, h981, h983, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h658, h970, h977, h978, h979, h982, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h658, h970, h979, h981, hc34, hlam, hphi, ht23, u2ehi3]
                    · linarith only [h658, h970, h978, h979, h980, hc25, hlam, hphi, u2ehi3]
                  · linarith only [h658, h970, h973, h978, h979, hlam]
                · linarith only [h0, h972, h978, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1020 | h1020
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1021 | h1021
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1022 | h1022
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1023 | h1023
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1024 | h1024
                        · linarith only [h1024, h970, h977, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1026 | h1026
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1027 | h1027
                            · linarith only [h1021, h1027, h970, h977, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1029 | h1029
                              · linarith only [h1026, h1029, h972, h977, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                              · rcases h0bigk with h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c | h1031c
                                · have p1031_0 := h1031c.1
                                  have p1031_1 := h1031c.2.1
                                  have p1031_2 := h1031c.2.2.1
                                  have p1031_3 := h1031c.2.2.2
                                  linarith only [hlam, p1031_0]
                                · have p1031_0 := h1031c.1
                                  have p1031_1 := h1031c.2.1
                                  have p1031_2 := h1031c.2.2.1
                                  have p1031_3 := h1031c.2.2.2
                                  linarith only [h0, hlam, p1031_1]
                                · have p1031_0 := h1031c.1
                                  have p1031_1 := h1031c.2.1
                                  have p1031_2 := h1031c.2.2.1
                                  have p1031_3 := h1031c.2.2.2
                                  linarith only [h658, hlam, p1031_0]
                                · have p1031_0 := h1031c.1
                                  have p1031_1 := h1031c.2.1
                                  have p1031_2 := h1031c.2.2.1
                                  have p1031_3 := h1031c.2.2.2
                                  linarith only [h1021, h970, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1031_1, u2ehi3]
                                · have p1031_0 := h1031c.1
                                  have p1031_1 := h1031c.2.1
                                  have p1031_2 := h1031c.2.2.1
                                  have p1031_3 := h1031c.2.2.2
                                  linarith only [h1021, h658, h970, h977, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1031_1, u2ehi3]
                                · have p1031_0 := h1031c.1
                                  have p1031_1 := h1031c.2.1
                                  have p1031_2 := h1031c.2.2.1
                                  have p1031_3 := h1031c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p1031_1]
                                · have p1031_0 := h1031c.1
                                  have p1031_1 := h1031c.2.1
                                  have p1031_2 := h1031c.2.2.1
                                  have p1031_3 := h1031c.2.2.2
                                  linarith only [hlam, p1031_0]
                                · have p1031_0 := h1031c.1
                                  have p1031_1 := h1031c.2.1
                                  have p1031_2 := h1031c.2.2.1
                                  have p1031_3 := h1031c.2.2.2
                                  linarith only [h0, h1021, h1024, h658, h971, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1031_1, u2ehi3]
                                · have p1031_0 := h1031c.1
                                  have p1031_1 := h1031c.2.1
                                  have p1031_2 := h1031c.2.2.1
                                  have p1031_3 := h1031c.2.2.2
                                  linarith only [h0, h1021, h970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1031_1, u2ehi3]
                                · have p1031_0 := h1031c.1
                                  have p1031_1 := h1031c.2.1
                                  have p1031_2 := h1031c.2.2.1
                                  have p1031_3 := h1031c.2.2.2
                                  linarith only [h0, h1021, h970, h977, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1031_1, u2ehi3]
                                · have p1031_0 := h1031c.1
                                  have p1031_1 := h1031c.2.1
                                  have p1031_2 := h1031c.2.2.1
                                  have p1031_3 := h1031c.2.2.2
                                  linarith only [h1021, h1024, h971, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1031_1, u2ehi3]
                                · have p1031_0 := h1031c.1
                                  have p1031_1 := h1031c.2.1
                                  have p1031_2 := h1031c.2.2.1
                                  have p1031_3 := h1031c.2.2.2
                                  linarith only [h972, hlam, p1031_1]
                                · have p1031_0 := h1031c.1
                                  have p1031_1 := h1031c.2.1
                                  have p1031_2 := h1031c.2.2.1
                                  have p1031_3 := h1031c.2.2.2
                                  linarith only [hlam, p1031_0]
                                · have p1031_0 := h1031c.1
                                  have p1031_1 := h1031c.2.1
                                  have p1031_2 := h1031c.2.2.1
                                  have p1031_3 := h1031c.2.2.2
                                  linarith only [h0, h1021, h970, h972, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1031_1, u2ehi3]
                                · have p1031_0 := h1031c.1
                                  have p1031_1 := h1031c.2.1
                                  have p1031_2 := h1031c.2.2.1
                                  have p1031_3 := h1031c.2.2.2
                                  linarith only [h0, h1021, h970, h972, h977, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1031_1, u2ehi3]
                                · have p1031_0 := h1031c.1
                                  have p1031_1 := h1031c.2.1
                                  have p1031_2 := h1031c.2.2.1
                                  have p1031_3 := h1031c.2.2.2
                                  linarith only [h970, hlam, p1031_0]
                                · have p1031_0 := h1031c.1
                                  have p1031_1 := h1031c.2.1
                                  have p1031_2 := h1031c.2.2.1
                                  have p1031_3 := h1031c.2.2.2
                                  linarith only [h973, hlam, p1031_0]
                                · have p1031_0 := h1031c.1
                                  have p1031_1 := h1031c.2.1
                                  have p1031_2 := h1031c.2.2.1
                                  have p1031_3 := h1031c.2.2.2
                                  linarith only [h975, hlam, p1031_0]
                                · have p1031_0 := h1031c.1
                                  have p1031_1 := h1031c.2.1
                                  have p1031_2 := h1031c.2.2.1
                                  have p1031_3 := h1031c.2.2.2
                                  linarith only [hlam, p1031_0]
                                · have p1031_0 := h1031c.1
                                  have p1031_1 := h1031c.2.1
                                  have p1031_2 := h1031c.2.2.1
                                  have p1031_3 := h1031c.2.2.2
                                  linarith only [h977, hlam, p1031_0]
                                · have p1031_0 := h1031c.1
                                  have p1031_1 := h1031c.2.1
                                  have p1031_2 := h1031c.2.2.1
                                  have p1031_3 := h1031c.2.2.2
                                  linarith only [h971, hlam, p1031_0]
                                · have p1031_0 := h1031c.1
                                  have p1031_1 := h1031c.2.1
                                  have p1031_2 := h1031c.2.2.1
                                  have p1031_3 := h1031c.2.2.2
                                  linarith only [h974, hlam, p1031_1]
                                · have p1031_0 := h1031c.1
                                  have p1031_1 := h1031c.2.1
                                  have p1031_2 := h1031c.2.2.1
                                  have p1031_3 := h1031c.2.2.2
                                  linarith only [h976, hlam, p1031_0]
                                · have p1031_0 := h1031c.1
                                  have p1031_1 := h1031c.2.1
                                  have p1031_2 := h1031c.2.2.1
                                  have p1031_3 := h1031c.2.2.2
                                  linarith only [h1021, h970, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1031_1, u2ehi3]
                                · have p1031_0 := h1031c.1
                                  have p1031_1 := h1031c.2.1
                                  have p1031_2 := h1031c.2.2.1
                                  have p1031_3 := h1031c.2.2.2
                                  linarith only [hlam, p1031_0]
                          · linarith only [h1026, h975, h977, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h1023, h658, h975, h977, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h1020, h1021, h1022, h658, h970, hc25, hlam, hphi, u2ehi3]
                  · linarith only [h1020, h1021, h658, h971, h974, hc24, hlam, hphi, u2ehi4]
                · linarith only [h0, h1020, h971, h973, h977, hc23, hlam, hphi, u2ehi3]
            · linarith only [h658, h971, h976, hlam]
          · linarith only [h658, h970, h975, hlam]
        · linarith only [h972, h974, hc25, hlam, hphi, u2ehi2]
      · linarith only [h972, h973, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1066 | h1066
      · linarith only [h1066, h972, hc23, hlam, hphi, u2ehi3]
      · linarith only [h0, h1066, h970, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1069 | h1069
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1070 | h1070
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1071 | h1071
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1072 | h1072
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1073 | h1073
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1074 | h1074
              · linarith only [h1074, h970, h971, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1076 | h1076
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1077 | h1077
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1078 | h1078
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1079 | h1079
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1080 | h1080
                        · linarith only [h1074, h1076, h1080, h658, h970, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h1077, h1080, h970, h971, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                      · linarith only [h1077, h1079, h658, h970, hc34, hlam, hphi, ht23, u2ehi3]
                    · linarith only [h1071, h1076, h1077, h1078, h658, h970, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                  · linarith only [h0, h1070, h1077, h970, hlam]
                · linarith only [h0, h1070, h1076, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1087 | h1087
              · linarith only [h1073, h1087, h658, h970, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1089 | h1089
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1090 | h1090
                  · linarith only [h1073, h1090, h658, h970, hc35, hlam, hphi, ht23, u2ehi3]
                  · linarith only [h1070, h1087, h1089, h1090, h658, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · linarith only [h0, h1069, h1070, h1089, h970, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
          · linarith only [h1072, h658, h970, hlam]
        · linarith only [h1069, h1071, hc25, hlam, hphi, u2ehi2]
      · linarith only [h1069, h1070, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1097 | h1097
      · linarith only [h1069, h1097, hc23, hlam, hphi, u2ehi3]
      · linarith only [h0, h1097, h970, hlam]

set_option maxHeartbeats 3900000 in
set_option maxHeartbeats 3900000 in
theorem r1l7_20_12_H_I_L_R_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h658 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h970 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1100 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h2ehi := hb2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1101 | h1101
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1102 | h1102
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1103 | h1103
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1104 | h1104
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1105 | h1105
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1106 | h1106
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1107 | h1107
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1108 | h1108
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1109 | h1109
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1110 | h1110
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1111 | h1111
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1112 | h1112
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1113 | h1113
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1114 | h1114
                            · rcases h0bigk with h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c
                              · have p1115_0 := h1115c.1
                                have p1115_1 := h1115c.2.1
                                have p1115_2 := h1115c.2.2.1
                                have p1115_3 := h1115c.2.2.2
                                linarith only [hlam, p1115_0]
                              · have p1115_0 := h1115c.1
                                have p1115_1 := h1115c.2.1
                                have p1115_2 := h1115c.2.2.1
                                have p1115_3 := h1115c.2.2.2
                                linarith only [h0, hlam, p1115_1]
                              · have p1115_0 := h1115c.1
                                have p1115_1 := h1115c.2.1
                                have p1115_2 := h1115c.2.2.1
                                have p1115_3 := h1115c.2.2.2
                                linarith only [h658, hlam, p1115_0]
                              · have p1115_0 := h1115c.1
                                have p1115_1 := h1115c.2.1
                                have p1115_2 := h1115c.2.2.1
                                have p1115_3 := h1115c.2.2.2
                                linarith only [h970, hlam, p1115_1]
                              · have p1115_0 := h1115c.1
                                have p1115_1 := h1115c.2.1
                                have p1115_2 := h1115c.2.2.1
                                have p1115_3 := h1115c.2.2.2
                                linarith only [h1110, h970, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p1115_1]
                              · have p1115_0 := h1115c.1
                                have p1115_1 := h1115c.2.1
                                have p1115_2 := h1115c.2.2.1
                                have p1115_3 := h1115c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p1115_1]
                              · have p1115_0 := h1115c.1
                                have p1115_1 := h1115c.2.1
                                have p1115_2 := h1115c.2.2.1
                                have p1115_3 := h1115c.2.2.2
                                linarith only [hlam, p1115_0]
                              · have p1115_0 := h1115c.1
                                have p1115_1 := h1115c.2.1
                                have p1115_2 := h1115c.2.2.1
                                have p1115_3 := h1115c.2.2.2
                                linarith only [h0, h1100, h1104, h1109, h970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1115_1, u2ehi4]
                              · have p1115_0 := h1115c.1
                                have p1115_1 := h1115c.2.1
                                have p1115_2 := h1115c.2.2.1
                                have p1115_3 := h1115c.2.2.2
                                linarith only [h0, h1100, h1109, h970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1115_1, u2ehi4]
                              · have p1115_0 := h1115c.1
                                have p1115_1 := h1115c.2.1
                                have p1115_2 := h1115c.2.2.1
                                have p1115_3 := h1115c.2.2.2
                                linarith only [h0, h1100, h1109, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1115_1, u2ehi4]
                              · have p1115_0 := h1115c.1
                                have p1115_1 := h1115c.2.1
                                have p1115_2 := h1115c.2.2.1
                                have p1115_3 := h1115c.2.2.2
                                linarith only [h1100, h1109, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1115_1, u2ehi4]
                              · have p1115_0 := h1115c.1
                                have p1115_1 := h1115c.2.1
                                have p1115_2 := h1115c.2.2.1
                                have p1115_3 := h1115c.2.2.2
                                linarith only [h1101, hlam, p1115_1]
                              · have p1115_0 := h1115c.1
                                have p1115_1 := h1115c.2.1
                                have p1115_2 := h1115c.2.2.1
                                have p1115_3 := h1115c.2.2.2
                                linarith only [hlam, p1115_0]
                              · have p1115_0 := h1115c.1
                                have p1115_1 := h1115c.2.1
                                have p1115_2 := h1115c.2.2.1
                                have p1115_3 := h1115c.2.2.2
                                linarith only [h0, h1100, h1101, h1109, h970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1115_1, u2ehi4]
                              · have p1115_0 := h1115c.1
                                have p1115_1 := h1115c.2.1
                                have p1115_2 := h1115c.2.2.1
                                have p1115_3 := h1115c.2.2.2
                                linarith only [h0, h1100, h1101, h1109, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1115_1, u2ehi4]
                              · have p1115_0 := h1115c.1
                                have p1115_1 := h1115c.2.1
                                have p1115_2 := h1115c.2.2.1
                                have p1115_3 := h1115c.2.2.2
                                linarith only [h1100, h1109, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1115_1, u2ehi4]
                              · have p1115_0 := h1115c.1
                                have p1115_1 := h1115c.2.1
                                have p1115_2 := h1115c.2.2.1
                                have p1115_3 := h1115c.2.2.2
                                linarith only [h1102, hlam, p1115_0]
                              · have p1115_0 := h1115c.1
                                have p1115_1 := h1115c.2.1
                                have p1115_2 := h1115c.2.2.1
                                have p1115_3 := h1115c.2.2.2
                                linarith only [h1104, hlam, p1115_0]
                              · have p1115_0 := h1115c.1
                                have p1115_1 := h1115c.2.1
                                have p1115_2 := h1115c.2.2.1
                                have p1115_3 := h1115c.2.2.2
                                linarith only [hlam, p1115_0]
                              · have p1115_0 := h1115c.1
                                have p1115_1 := h1115c.2.1
                                have p1115_2 := h1115c.2.2.1
                                have p1115_3 := h1115c.2.2.2
                                linarith only [h0, h1100, h1101, h1104, h1109, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1115_1, u2ehi4]
                              · have p1115_0 := h1115c.1
                                have p1115_1 := h1115c.2.1
                                have p1115_2 := h1115c.2.2.1
                                have p1115_3 := h1115c.2.2.2
                                linarith only [h1100, hlam, p1115_0]
                              · have p1115_0 := h1115c.1
                                have p1115_1 := h1115c.2.1
                                have p1115_2 := h1115c.2.2.1
                                have p1115_3 := h1115c.2.2.2
                                linarith only [h1103, hlam, p1115_1]
                              · have p1115_0 := h1115c.1
                                have p1115_1 := h1115c.2.1
                                have p1115_2 := h1115c.2.2.1
                                have p1115_3 := h1115c.2.2.2
                                linarith only [h1105, hlam, p1115_0]
                              · have p1115_0 := h1115c.1
                                have p1115_1 := h1115c.2.1
                                have p1115_2 := h1115c.2.2.1
                                have p1115_3 := h1115c.2.2.2
                                linarith only [h1106, hlam, p1115_1]
                              · have p1115_0 := h1115c.1
                                have p1115_1 := h1115c.2.1
                                have p1115_2 := h1115c.2.2.1
                                have p1115_3 := h1115c.2.2.2
                                linarith only [hlam, p1115_0]
                            · rcases h0bigk with h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c
                              · have p1141_0 := h1141c.1
                                have p1141_1 := h1141c.2.1
                                have p1141_2 := h1141c.2.2.1
                                have p1141_3 := h1141c.2.2.2
                                linarith only [hlam, p1141_0]
                              · have p1141_0 := h1141c.1
                                have p1141_1 := h1141c.2.1
                                have p1141_2 := h1141c.2.2.1
                                have p1141_3 := h1141c.2.2.2
                                linarith only [h0, hlam, p1141_1]
                              · have p1141_0 := h1141c.1
                                have p1141_1 := h1141c.2.1
                                have p1141_2 := h1141c.2.2.1
                                have p1141_3 := h1141c.2.2.2
                                linarith only [h658, hlam, p1141_0]
                              · have p1141_0 := h1141c.1
                                have p1141_1 := h1141c.2.1
                                have p1141_2 := h1141c.2.2.1
                                have p1141_3 := h1141c.2.2.2
                                linarith only [h970, hlam, p1141_1]
                              · have p1141_0 := h1141c.1
                                have p1141_1 := h1141c.2.1
                                have p1141_2 := h1141c.2.2.1
                                have p1141_3 := h1141c.2.2.2
                                linarith only [h1107, h1110, h970, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1141_1]
                              · have p1141_0 := h1141c.1
                                have p1141_1 := h1141c.2.1
                                have p1141_2 := h1141c.2.2.1
                                have p1141_3 := h1141c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p1141_1]
                              · have p1141_0 := h1141c.1
                                have p1141_1 := h1141c.2.1
                                have p1141_2 := h1141c.2.2.1
                                have p1141_3 := h1141c.2.2.2
                                linarith only [hlam, p1141_0]
                              · have p1141_0 := h1141c.1
                                have p1141_1 := h1141c.2.1
                                have p1141_2 := h1141c.2.2.1
                                have p1141_3 := h1141c.2.2.2
                                linarith only [h0, h658, hc01, hc12, hlam, hphi, p1141_1]
                              · have p1141_0 := h1141c.1
                                have p1141_1 := h1141c.2.1
                                have p1141_2 := h1141c.2.2.1
                                have p1141_3 := h1141c.2.2.2
                                linarith only [h0, h1100, h1109, h970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1141_1, u2ehi4]
                              · have p1141_0 := h1141c.1
                                have p1141_1 := h1141c.2.1
                                have p1141_2 := h1141c.2.2.1
                                have p1141_3 := h1141c.2.2.2
                                linarith only [h0, h1100, h1109, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1141_1, u2ehi4]
                              · have p1141_0 := h1141c.1
                                have p1141_1 := h1141c.2.1
                                have p1141_2 := h1141c.2.2.1
                                have p1141_3 := h1141c.2.2.2
                                linarith only [h1100, h1109, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1141_1, u2ehi4]
                              · have p1141_0 := h1141c.1
                                have p1141_1 := h1141c.2.1
                                have p1141_2 := h1141c.2.2.1
                                have p1141_3 := h1141c.2.2.2
                                linarith only [h1101, hlam, p1141_1]
                              · have p1141_0 := h1141c.1
                                have p1141_1 := h1141c.2.1
                                have p1141_2 := h1141c.2.2.1
                                have p1141_3 := h1141c.2.2.2
                                linarith only [hlam, p1141_0]
                              · have p1141_0 := h1141c.1
                                have p1141_1 := h1141c.2.1
                                have p1141_2 := h1141c.2.2.1
                                have p1141_3 := h1141c.2.2.2
                                linarith only [h1100, h1107, h1109, h658, h970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1141_1, u2ehi4]
                              · have p1141_0 := h1141c.1
                                have p1141_1 := h1141c.2.1
                                have p1141_2 := h1141c.2.2.1
                                have p1141_3 := h1141c.2.2.2
                                linarith only [h1100, h1107, h1109, h658, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1141_1, u2ehi4]
                              · have p1141_0 := h1141c.1
                                have p1141_1 := h1141c.2.1
                                have p1141_2 := h1141c.2.2.1
                                have p1141_3 := h1141c.2.2.2
                                linarith only [h1100, h1109, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1141_1, u2ehi4]
                              · have p1141_0 := h1141c.1
                                have p1141_1 := h1141c.2.1
                                have p1141_2 := h1141c.2.2.1
                                have p1141_3 := h1141c.2.2.2
                                linarith only [h1102, hlam, p1141_0]
                              · have p1141_0 := h1141c.1
                                have p1141_1 := h1141c.2.1
                                have p1141_2 := h1141c.2.2.1
                                have p1141_3 := h1141c.2.2.2
                                linarith only [h1104, hlam, p1141_0]
                              · have p1141_0 := h1141c.1
                                have p1141_1 := h1141c.2.1
                                have p1141_2 := h1141c.2.2.1
                                have p1141_3 := h1141c.2.2.2
                                linarith only [hlam, p1141_0]
                              · have p1141_0 := h1141c.1
                                have p1141_1 := h1141c.2.1
                                have p1141_2 := h1141c.2.2.1
                                have p1141_3 := h1141c.2.2.2
                                linarith only [h1100, h1107, h1109, h1110, h970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1141_1, u2ehi4]
                              · have p1141_0 := h1141c.1
                                have p1141_1 := h1141c.2.1
                                have p1141_2 := h1141c.2.2.1
                                have p1141_3 := h1141c.2.2.2
                                linarith only [h1100, hlam, p1141_0]
                              · have p1141_0 := h1141c.1
                                have p1141_1 := h1141c.2.1
                                have p1141_2 := h1141c.2.2.1
                                have p1141_3 := h1141c.2.2.2
                                linarith only [h1103, hlam, p1141_1]
                              · have p1141_0 := h1141c.1
                                have p1141_1 := h1141c.2.1
                                have p1141_2 := h1141c.2.2.1
                                have p1141_3 := h1141c.2.2.2
                                linarith only [h1105, hlam, p1141_0]
                              · have p1141_0 := h1141c.1
                                have p1141_1 := h1141c.2.1
                                have p1141_2 := h1141c.2.2.1
                                have p1141_3 := h1141c.2.2.2
                                linarith only [h1106, hlam, p1141_1]
                              · have p1141_0 := h1141c.1
                                have p1141_1 := h1141c.2.1
                                have p1141_2 := h1141c.2.2.1
                                have p1141_3 := h1141c.2.2.2
                                linarith only [hlam, p1141_0]
                          · linarith only [h1100, h1107, h1110, h1111, h1113, h970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1168 | h1168
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1169 | h1169
                            · rcases h0bigk with h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c | h1170c
                              · have p1170_0 := h1170c.1
                                have p1170_1 := h1170c.2.1
                                have p1170_2 := h1170c.2.2.1
                                have p1170_3 := h1170c.2.2.2
                                linarith only [hlam, p1170_0]
                              · have p1170_0 := h1170c.1
                                have p1170_1 := h1170c.2.1
                                have p1170_2 := h1170c.2.2.1
                                have p1170_3 := h1170c.2.2.2
                                linarith only [h0, hlam, p1170_1]
                              · have p1170_0 := h1170c.1
                                have p1170_1 := h1170c.2.1
                                have p1170_2 := h1170c.2.2.1
                                have p1170_3 := h1170c.2.2.2
                                linarith only [h658, hlam, p1170_0]
                              · have p1170_0 := h1170c.1
                                have p1170_1 := h1170c.2.1
                                have p1170_2 := h1170c.2.2.1
                                have p1170_3 := h1170c.2.2.2
                                linarith only [h970, hlam, p1170_1]
                              · have p1170_0 := h1170c.1
                                have p1170_1 := h1170c.2.1
                                have p1170_2 := h1170c.2.2.1
                                have p1170_3 := h1170c.2.2.2
                                linarith only [h1107, h1110, h970, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1170_1]
                              · have p1170_0 := h1170c.1
                                have p1170_1 := h1170c.2.1
                                have p1170_2 := h1170c.2.2.1
                                have p1170_3 := h1170c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p1170_1]
                              · have p1170_0 := h1170c.1
                                have p1170_1 := h1170c.2.1
                                have p1170_2 := h1170c.2.2.1
                                have p1170_3 := h1170c.2.2.2
                                linarith only [hlam, p1170_0]
                              · have p1170_0 := h1170c.1
                                have p1170_1 := h1170c.2.1
                                have p1170_2 := h1170c.2.2.1
                                have p1170_3 := h1170c.2.2.2
                                linarith only [h0, h1104, h1112, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1170_1]
                              · have p1170_0 := h1170c.1
                                have p1170_1 := h1170c.2.1
                                have p1170_2 := h1170c.2.2.1
                                have p1170_3 := h1170c.2.2.2
                                linarith only [h0, h1100, h970, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p1170_1]
                              · have p1170_0 := h1170c.1
                                have p1170_1 := h1170c.2.1
                                have p1170_2 := h1170c.2.2.1
                                have p1170_3 := h1170c.2.2.2
                                linarith only [h0, h1103, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1170_1, u2ehi4]
                              · have p1170_0 := h1170c.1
                                have p1170_1 := h1170c.2.1
                                have p1170_2 := h1170c.2.2.1
                                have p1170_3 := h1170c.2.2.2
                                linarith only [h1100, h1103, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1170_1, u2ehi4]
                              · have p1170_0 := h1170c.1
                                have p1170_1 := h1170c.2.1
                                have p1170_2 := h1170c.2.2.1
                                have p1170_3 := h1170c.2.2.2
                                linarith only [h1101, hlam, p1170_1]
                              · have p1170_0 := h1170c.1
                                have p1170_1 := h1170c.2.1
                                have p1170_2 := h1170c.2.2.1
                                have p1170_3 := h1170c.2.2.2
                                linarith only [hlam, p1170_0]
                              · have p1170_0 := h1170c.1
                                have p1170_1 := h1170c.2.1
                                have p1170_2 := h1170c.2.2.1
                                have p1170_3 := h1170c.2.2.2
                                linarith only [h1100, h1103, h1107, h658, h970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1170_1, u2ehi4]
                              · have p1170_0 := h1170c.1
                                have p1170_1 := h1170c.2.1
                                have p1170_2 := h1170c.2.2.1
                                have p1170_3 := h1170c.2.2.2
                                linarith only [h1103, h1107, h658, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1170_1, u2ehi4]
                              · have p1170_0 := h1170c.1
                                have p1170_1 := h1170c.2.1
                                have p1170_2 := h1170c.2.2.1
                                have p1170_3 := h1170c.2.2.2
                                linarith only [h1100, h1103, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1170_1, u2ehi4]
                              · have p1170_0 := h1170c.1
                                have p1170_1 := h1170c.2.1
                                have p1170_2 := h1170c.2.2.1
                                have p1170_3 := h1170c.2.2.2
                                linarith only [h1102, hlam, p1170_0]
                              · have p1170_0 := h1170c.1
                                have p1170_1 := h1170c.2.1
                                have p1170_2 := h1170c.2.2.1
                                have p1170_3 := h1170c.2.2.2
                                linarith only [h1104, hlam, p1170_0]
                              · have p1170_0 := h1170c.1
                                have p1170_1 := h1170c.2.1
                                have p1170_2 := h1170c.2.2.1
                                have p1170_3 := h1170c.2.2.2
                                linarith only [hlam, p1170_0]
                              · have p1170_0 := h1170c.1
                                have p1170_1 := h1170c.2.1
                                have p1170_2 := h1170c.2.2.1
                                have p1170_3 := h1170c.2.2.2
                                linarith only [h1103, h1107, h1110, h970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1170_1, u2ehi4]
                              · have p1170_0 := h1170c.1
                                have p1170_1 := h1170c.2.1
                                have p1170_2 := h1170c.2.2.1
                                have p1170_3 := h1170c.2.2.2
                                linarith only [h1100, hlam, p1170_0]
                              · have p1170_0 := h1170c.1
                                have p1170_1 := h1170c.2.1
                                have p1170_2 := h1170c.2.2.1
                                have p1170_3 := h1170c.2.2.2
                                linarith only [h1103, hlam, p1170_1]
                              · have p1170_0 := h1170c.1
                                have p1170_1 := h1170c.2.1
                                have p1170_2 := h1170c.2.2.1
                                have p1170_3 := h1170c.2.2.2
                                linarith only [h1105, hlam, p1170_0]
                              · have p1170_0 := h1170c.1
                                have p1170_1 := h1170c.2.1
                                have p1170_2 := h1170c.2.2.1
                                have p1170_3 := h1170c.2.2.2
                                linarith only [h1106, hlam, p1170_1]
                              · have p1170_0 := h1170c.1
                                have p1170_1 := h1170c.2.1
                                have p1170_2 := h1170c.2.2.1
                                have p1170_3 := h1170c.2.2.2
                                linarith only [hlam, p1170_0]
                            · linarith only [h1112, h1169, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                          · linarith only [h0, h1100, h1111, h1112, h1168, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h1100, h1103, h1111, h970, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                    · linarith only [h1104, h1110, h658, hlam]
                  · linarith only [h0, h1101, h1109, hc25, hlam, hphi, u2ehi2]
                · linarith only [h1100, h1102, h1103, h1107, h1108, h658, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
              · linarith only [h0, h1100, h1103, h1107, hc23, hlam, hphi, u2ehi4]
            · linarith only [h1100, h1106, h970, hlam]
          · linarith only [h1100, h1105, h658, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1205 | h1205
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1206 | h1206
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1207 | h1207
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1208 | h1208
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1209 | h1209
                  · linarith only [h1100, h1104, h1209, h658, hc34, hlam, hphi, ht23, u2ehi4]
                  · linarith only [h0, h1101, h1209, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h1102, h1208, hlam]
              · linarith only [h0, h1101, h1207, hlam]
            · linarith only [h1100, h1104, h1206, h658, hlam]
          · linarith only [h1100, h1205, h658, hlam]
      · linarith only [h1101, h1103, hc25, hlam, hphi, u2ehi2]
    · linarith only [h1101, h1102, hc24, hlam, hphi, u2ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1218 | h1218
    · linarith only [h1101, h1218, hc23, hlam, hphi, u2ehi3]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1220 | h1220
      · linarith only [h1101, h1220, hc23, hlam, hphi, u2ehi4]
      · linarith only [h0, h1100, h1220, hlam]

end R2N4
