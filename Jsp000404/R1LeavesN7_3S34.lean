import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11016000 in
set_option maxHeartbeats 11016000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s16_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg17994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h19110 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h22593 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h23332 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h23666 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  have h16563 := hg16563
  have h17994 := hg17994
  rcases m.htr 0 3 5 (by decide) (by decide) with h23667 | h23667
  · rcases m.htr 0 4 5 (by decide) (by decide) with h23668 | h23668
    · rcases m.htr 1 2 3 (by decide) (by decide) with h23669 | h23669
      · rcases m.htr 1 2 4 (by decide) (by decide) with h23670 | h23670
        · rcases m.htr 1 2 5 (by decide) (by decide) with h23671 | h23671
          · rcases m.htr 1 3 4 (by decide) (by decide) with h23672 | h23672
            · rcases m.htr 1 3 5 (by decide) (by decide) with h23673 | h23673
              · rcases m.htr 1 4 5 (by decide) (by decide) with h23674 | h23674
                · rcases m.htr 2 3 4 (by decide) (by decide) with h23675 | h23675
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h23676 | h23676
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h23677 | h23677
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h23678 | h23678
                        · rcases h1bigk with h23679c | h23679c | h23679c | h23679c | h23679c | h23679c | h23679c | h23679c | h23679c | h23679c | h23679c | h23679c | h23679c | h23679c | h23679c | h23679c | h23679c | h23679c | h23679c | h23679c | h23679c | h23679c | h23679c | h23679c | h23679c
                          · have p23679_0 := h23679c.1
                            have p23679_1 := h23679c.2.1
                            have p23679_2 := h23679c.2.2.1
                            have p23679_3 := h23679c.2.2.2
                            linarith only [hlam, p23679_0]
                          · have p23679_0 := h23679c.1
                            have p23679_1 := h23679c.2.1
                            have p23679_2 := h23679c.2.2.1
                            have p23679_3 := h23679c.2.2.2
                            linarith only [h0, hlam, p23679_0]
                          · have p23679_0 := h23679c.1
                            have p23679_1 := h23679c.2.1
                            have p23679_2 := h23679c.2.2.1
                            have p23679_3 := h23679c.2.2.2
                            linarith only [h14799, hlam, p23679_0]
                          · have p23679_0 := h23679c.1
                            have p23679_1 := h23679c.2.1
                            have p23679_2 := h23679c.2.2.1
                            have p23679_3 := h23679c.2.2.2
                            linarith only [h16563, hlam, p23679_0]
                          · have p23679_0 := h23679c.1
                            have p23679_1 := h23679c.2.1
                            have p23679_2 := h23679c.2.2.1
                            have p23679_3 := h23679c.2.2.2
                            linarith only [h17994, hlam, p23679_0]
                          · have p23679_0 := h23679c.1
                            have p23679_1 := h23679c.2.1
                            have p23679_2 := h23679c.2.2.1
                            have p23679_3 := h23679c.2.2.2
                            rcases p23679_3 (m.d 0 1) (by simp) with h23685 | h23685
                            · linarith only [h23685, hlam, p23679_0]
                            · rcases p23679_3 (m.d 1 2) (by simp) with h23687 | h23687
                              · rcases p23679_3 (m.d 1 3) (by simp) with h23688 | h23688
                                · linarith only [h23669, h23688, hlam]
                                · linarith only [h14799, h23688, hlam]
                              · linarith only [h23687, hlam, p23679_0]
                          · have p23679_0 := h23679c.1
                            have p23679_1 := h23679c.2.1
                            have p23679_2 := h23679c.2.2.1
                            have p23679_3 := h23679c.2.2.2
                            linarith only [hlam, p23679_0]
                          · have p23679_0 := h23679c.1
                            have p23679_1 := h23679c.2.1
                            have p23679_2 := h23679c.2.2.1
                            have p23679_3 := h23679c.2.2.2
                            linarith only [h14799, hc01, hc12, hlam, hphi, p23679_1]
                          · have p23679_0 := h23679c.1
                            have p23679_1 := h23679c.2.1
                            have p23679_2 := h23679c.2.2.1
                            have p23679_3 := h23679c.2.2.2
                            linarith only [h0, h23332, h23671, h23674, hc01, hc12, hlam, hphi, p23679_1]
                          · have p23679_0 := h23679c.1
                            have p23679_1 := h23679c.2.1
                            have p23679_2 := h23679c.2.2.1
                            have p23679_3 := h23679c.2.2.2
                            linarith only [h0, h23332, h23671, hc01, hc12, hlam, hphi, p23679_1]
                          · have p23679_0 := h23679c.1
                            have p23679_1 := h23679c.2.1
                            have p23679_2 := h23679c.2.2.1
                            have p23679_3 := h23679c.2.2.2
                            rcases p23679_3 (m.d 0 1) (by simp) with h23696 | h23696
                            · linarith only [h23696, hlam, p23679_0]
                            · rcases p23679_3 (m.d 1 2) (by simp) with h23698 | h23698
                              · rcases p23679_3 (m.d 1 3) (by simp) with h23699 | h23699
                                · rcases p23679_3 (m.d 1 4) (by simp) with h23700 | h23700
                                  · linarith only [h23672, h23700, hlam]
                                  · linarith only [h16563, h23700, hlam]
                                · linarith only [h23699, hlam, p23679_0]
                              · linarith only [h0, h23698, hlam]
                          · have p23679_0 := h23679c.1
                            have p23679_1 := h23679c.2.1
                            have p23679_2 := h23679c.2.2.1
                            have p23679_3 := h23679c.2.2.2
                            linarith only [h23669, hlam, p23679_1]
                          · have p23679_0 := h23679c.1
                            have p23679_1 := h23679c.2.1
                            have p23679_2 := h23679c.2.2.1
                            have p23679_3 := h23679c.2.2.2
                            linarith only [hlam, p23679_0]
                          · have p23679_0 := h23679c.1
                            have p23679_1 := h23679c.2.1
                            have p23679_2 := h23679c.2.2.1
                            have p23679_3 := h23679c.2.2.2
                            linarith only [h0, h23332, h23671, h23674, hc01, hc13, hlam, hphi, p23679_1]
                          · have p23679_0 := h23679c.1
                            have p23679_1 := h23679c.2.1
                            have p23679_2 := h23679c.2.2.1
                            have p23679_3 := h23679c.2.2.2
                            linarith only [h0, h23332, h23669, h23671, hc01, hc12, hlam, hphi, p23679_1]
                          · have p23679_0 := h23679c.1
                            have p23679_1 := h23679c.2.1
                            have p23679_2 := h23679c.2.2.1
                            have p23679_3 := h23679c.2.2.2
                            rcases p23679_3 (m.d 0 1) (by simp) with h23709 | h23709
                            · linarith only [h23709, hlam, p23679_0]
                            · rcases p23679_3 (m.d 1 2) (by simp) with h23711 | h23711
                              · rcases p23679_3 (m.d 1 3) (by simp) with h23712 | h23712
                                · rcases p23679_3 (m.d 1 4) (by simp) with h23713 | h23713
                                  · rcases p23679_3 (m.d 1 5) (by simp) with h23714 | h23714
                                    · linarith only [h23674, h23714, hlam]
                                    · linarith only [h17994, h23714, hlam]
                                  · linarith only [h23713, hlam, p23679_0]
                                · linarith only [h14799, h23712, hlam]
                              · linarith only [h0, h23711, hlam]
                          · have p23679_0 := h23679c.1
                            have p23679_1 := h23679c.2.1
                            have p23679_2 := h23679c.2.2.1
                            have p23679_3 := h23679c.2.2.2
                            linarith only [h23670, hlam, p23679_1]
                          · have p23679_0 := h23679c.1
                            have p23679_1 := h23679c.2.1
                            have p23679_2 := h23679c.2.2.1
                            have p23679_3 := h23679c.2.2.2
                            linarith only [h23672, hlam, p23679_0]
                          · have p23679_0 := h23679c.1
                            have p23679_1 := h23679c.2.1
                            have p23679_2 := h23679c.2.2.1
                            have p23679_3 := h23679c.2.2.2
                            linarith only [hlam, p23679_0]
                          · have p23679_0 := h23679c.1
                            have p23679_1 := h23679c.2.1
                            have p23679_2 := h23679c.2.2.1
                            have p23679_3 := h23679c.2.2.2
                            linarith only [h0, h23332, h23671, hc01, hc14, hlam, hphi, p23679_1]
                          · have p23679_0 := h23679c.1
                            have p23679_1 := h23679c.2.1
                            have p23679_2 := h23679c.2.2.1
                            have p23679_3 := h23679c.2.2.2
                            rcases p23679_3 (m.d 0 1) (by simp) with h23724 | h23724
                            · linarith only [h23724, hlam, p23679_0]
                            · rcases p23679_3 (m.d 1 2) (by simp) with h23726 | h23726
                              · rcases p23679_3 (m.d 1 3) (by simp) with h23727 | h23727
                                · rcases p23679_3 (m.d 1 4) (by simp) with h23728 | h23728
                                  · rcases p23679_3 (m.d 1 5) (by simp) with h23729 | h23729
                                    · rcases h3bigk with h23730c | h23730c | h23730c | h23730c | h23730c | h23730c | h23730c | h23730c | h23730c | h23730c | h23730c | h23730c | h23730c | h23730c | h23730c | h23730c | h23730c | h23730c | h23730c | h23730c | h23730c | h23730c | h23730c | h23730c | h23730c
                                      · have p23730_0 := h23730c.1
                                        have p23730_1 := h23730c.2.1
                                        have p23730_2 := h23730c.2.2.1
                                        have p23730_3 := h23730c.2.2.2
                                        linarith only [hlam, p23730_0]
                                      · have p23730_0 := h23730c.1
                                        have p23730_1 := h23730c.2.1
                                        have p23730_2 := h23730c.2.2.1
                                        have p23730_3 := h23730c.2.2.2
                                        linarith only [h14799, hlam, p23730_1]
                                      · have p23730_0 := h23730c.1
                                        have p23730_1 := h23730c.2.1
                                        have p23730_2 := h23730c.2.2.1
                                        have p23730_3 := h23730c.2.2.2
                                        linarith only [h19110, hlam, p23730_1]
                                      · have p23730_0 := h23730c.1
                                        have p23730_1 := h23730c.2.1
                                        have p23730_2 := h23730c.2.2.1
                                        have p23730_3 := h23730c.2.2.2
                                        linarith only [h19110, h23669, h23678, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p23730_1]
                                      · have p23730_0 := h23730c.1
                                        have p23730_1 := h23730c.2.1
                                        have p23730_2 := h23730c.2.2.1
                                        have p23730_3 := h23730c.2.2.2
                                        rcases p23730_3 (m.d 0 3) (by simp) with h23735 | h23735
                                        · rcases p23730_3 (m.d 1 3) (by simp) with h23736 | h23736
                                          · rcases p23730_3 (m.d 2 3) (by simp) with h23737 | h23737
                                            · rcases p23730_3 (m.d 3 4) (by simp) with h23738 | h23738
                                              · linarith only [h23666, h23738, hlam]
                                              · linarith only [h23678, h23738, hlam]
                                            · linarith only [h23676, h23737, hlam]
                                          · linarith only [h23673, h23736, hlam]
                                        · linarith only [h23735, hlam, p23730_0]
                                      · have p23730_0 := h23730c.1
                                        have p23730_1 := h23730c.2.1
                                        have p23730_2 := h23730c.2.2.1
                                        have p23730_3 := h23730c.2.2.2
                                        linarith only [h23666, h23669, h23678, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p23730_1]
                                      · have p23730_0 := h23730c.1
                                        have p23730_1 := h23730c.2.1
                                        have p23730_2 := h23730c.2.2.1
                                        have p23730_3 := h23730c.2.2.2
                                        linarith only [hlam, p23730_0]
                                      · have p23730_0 := h23730c.1
                                        have p23730_1 := h23730c.2.1
                                        have p23730_2 := h23730c.2.2.1
                                        have p23730_3 := h23730c.2.2.2
                                        linarith only [h0, h19110, h23669, hc01, hc12, hlam, hphi, p23730_1]
                                      · have p23730_0 := h23730c.1
                                        have p23730_1 := h23730c.2.1
                                        have p23730_2 := h23730c.2.2.1
                                        have p23730_3 := h23730c.2.2.2
                                        rcases p23730_3 (m.d 0 3) (by simp) with h23747 | h23747
                                        · linarith only [h14799, h23747, hlam]
                                        · linarith only [h23666, h23747, hlam]
                                      · have p23730_0 := h23730c.1
                                        have p23730_1 := h23730c.2.1
                                        have p23730_2 := h23730c.2.2.1
                                        have p23730_3 := h23730c.2.2.2
                                        rcases p23730_3 (m.d 0 3) (by simp) with h23750 | h23750
                                        · linarith only [h14799, h23750, hlam]
                                        · linarith only [h23667, h23750, hlam]
                                      · have p23730_0 := h23730c.1
                                        have p23730_1 := h23730c.2.1
                                        have p23730_2 := h23730c.2.2.1
                                        have p23730_3 := h23730c.2.2.2
                                        linarith only [h23666, h23678, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p23730_1]
                                      · have p23730_0 := h23730c.1
                                        have p23730_1 := h23730c.2.1
                                        have p23730_2 := h23730c.2.2.1
                                        have p23730_3 := h23730c.2.2.2
                                        linarith only [h23669, hlam, p23730_0]
                                      · have p23730_0 := h23730c.1
                                        have p23730_1 := h23730c.2.1
                                        have p23730_2 := h23730c.2.2.1
                                        have p23730_3 := h23730c.2.2.2
                                        linarith only [hlam, p23730_0]
                                      · have p23730_0 := h23730c.1
                                        have p23730_1 := h23730c.2.1
                                        have p23730_2 := h23730c.2.2.1
                                        have p23730_3 := h23730c.2.2.2
                                        linarith only [h23669, h23678, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p23730_1]
                                      · have p23730_0 := h23730c.1
                                        have p23730_1 := h23730c.2.1
                                        have p23730_2 := h23730c.2.2.1
                                        have p23730_3 := h23730c.2.2.2
                                        rcases p23730_3 (m.d 0 3) (by simp) with h23757 | h23757
                                        · linarith only [h19110, h23757, hlam]
                                        · linarith only [h23667, h23757, hlam]
                                      · have p23730_0 := h23730c.1
                                        have p23730_1 := h23730c.2.1
                                        have p23730_2 := h23730c.2.2.1
                                        have p23730_3 := h23730c.2.2.2
                                        linarith only [h23666, hlam, p23730_0]
                                      · have p23730_0 := h23730c.1
                                        have p23730_1 := h23730c.2.1
                                        have p23730_2 := h23730c.2.2.1
                                        have p23730_3 := h23730c.2.2.2
                                        linarith only [h23672, hlam, p23730_0]
                                      · have p23730_0 := h23730c.1
                                        have p23730_1 := h23730c.2.1
                                        have p23730_2 := h23730c.2.2.1
                                        have p23730_3 := h23730c.2.2.2
                                        linarith only [h23675, hlam, p23730_0]
                                      · have p23730_0 := h23730c.1
                                        have p23730_1 := h23730c.2.1
                                        have p23730_2 := h23730c.2.2.1
                                        have p23730_3 := h23730c.2.2.2
                                        linarith only [hlam, p23730_0]
                                      · have p23730_0 := h23730c.1
                                        have p23730_1 := h23730c.2.1
                                        have p23730_2 := h23730c.2.2.1
                                        have p23730_3 := h23730c.2.2.2
                                        linarith only [h19110, h23666, h23669, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p23730_1]
                                      · have p23730_0 := h23730c.1
                                        have p23730_1 := h23730c.2.1
                                        have p23730_2 := h23730c.2.2.1
                                        have p23730_3 := h23730c.2.2.2
                                        linarith only [h23667, hlam, p23730_0]
                                      · have p23730_0 := h23730c.1
                                        have p23730_1 := h23730c.2.1
                                        have p23730_2 := h23730c.2.2.1
                                        have p23730_3 := h23730c.2.2.2
                                        linarith only [h23673, hlam, p23730_0]
                                      · have p23730_0 := h23730c.1
                                        have p23730_1 := h23730c.2.1
                                        have p23730_2 := h23730c.2.2.1
                                        have p23730_3 := h23730c.2.2.2
                                        linarith only [h23676, hlam, p23730_0]
                                      · have p23730_0 := h23730c.1
                                        have p23730_1 := h23730c.2.1
                                        have p23730_2 := h23730c.2.2.1
                                        have p23730_3 := h23730c.2.2.2
                                        linarith only [h23678, hlam, p23730_0]
                                      · have p23730_0 := h23730c.1
                                        have p23730_1 := h23730c.2.1
                                        have p23730_2 := h23730c.2.2.1
                                        have p23730_3 := h23730c.2.2.2
                                        linarith only [hlam, p23730_0]
                                    · linarith only [h23729, hlam, p23679_0]
                                  · linarith only [h16563, h23728, hlam]
                                · linarith only [h14799, h23727, hlam]
                              · linarith only [h0, h23726, hlam]
                          · have p23679_0 := h23679c.1
                            have p23679_1 := h23679c.2.1
                            have p23679_2 := h23679c.2.2.1
                            have p23679_3 := h23679c.2.2.2
                            linarith only [h23671, hlam, p23679_1]
                          · have p23679_0 := h23679c.1
                            have p23679_1 := h23679c.2.1
                            have p23679_2 := h23679c.2.2.1
                            have p23679_3 := h23679c.2.2.2
                            linarith only [h23673, hlam, p23679_0]
                          · have p23679_0 := h23679c.1
                            have p23679_1 := h23679c.2.1
                            have p23679_2 := h23679c.2.2.1
                            have p23679_3 := h23679c.2.2.2
                            linarith only [h23674, hlam, p23679_0]
                          · have p23679_0 := h23679c.1
                            have p23679_1 := h23679c.2.1
                            have p23679_2 := h23679c.2.2.1
                            have p23679_3 := h23679c.2.2.2
                            linarith only [hlam, p23679_0]
                        · rcases h1bigk with h23778c | h23778c | h23778c | h23778c | h23778c | h23778c | h23778c | h23778c | h23778c | h23778c | h23778c | h23778c | h23778c | h23778c | h23778c | h23778c | h23778c | h23778c | h23778c | h23778c | h23778c | h23778c | h23778c | h23778c | h23778c
                          · have p23778_0 := h23778c.1
                            have p23778_1 := h23778c.2.1
                            have p23778_2 := h23778c.2.2.1
                            have p23778_3 := h23778c.2.2.2
                            linarith only [hlam, p23778_0]
                          · have p23778_0 := h23778c.1
                            have p23778_1 := h23778c.2.1
                            have p23778_2 := h23778c.2.2.1
                            have p23778_3 := h23778c.2.2.2
                            linarith only [h0, hlam, p23778_0]
                          · have p23778_0 := h23778c.1
                            have p23778_1 := h23778c.2.1
                            have p23778_2 := h23778c.2.2.1
                            have p23778_3 := h23778c.2.2.2
                            linarith only [h14799, hlam, p23778_0]
                          · have p23778_0 := h23778c.1
                            have p23778_1 := h23778c.2.1
                            have p23778_2 := h23778c.2.2.1
                            have p23778_3 := h23778c.2.2.2
                            linarith only [h16563, hlam, p23778_0]
                          · have p23778_0 := h23778c.1
                            have p23778_1 := h23778c.2.1
                            have p23778_2 := h23778c.2.2.1
                            have p23778_3 := h23778c.2.2.2
                            linarith only [h17994, hlam, p23778_0]
                          · have p23778_0 := h23778c.1
                            have p23778_1 := h23778c.2.1
                            have p23778_2 := h23778c.2.2.1
                            have p23778_3 := h23778c.2.2.2
                            rcases p23778_3 (m.d 0 1) (by simp) with h23784 | h23784
                            · linarith only [h23784, hlam, p23778_0]
                            · rcases p23778_3 (m.d 1 2) (by simp) with h23786 | h23786
                              · rcases p23778_3 (m.d 1 3) (by simp) with h23787 | h23787
                                · linarith only [h23669, h23787, hlam]
                                · linarith only [h14799, h23787, hlam]
                              · linarith only [h23786, hlam, p23778_0]
                          · have p23778_0 := h23778c.1
                            have p23778_1 := h23778c.2.1
                            have p23778_2 := h23778c.2.2.1
                            have p23778_3 := h23778c.2.2.2
                            linarith only [hlam, p23778_0]
                          · have p23778_0 := h23778c.1
                            have p23778_1 := h23778c.2.1
                            have p23778_2 := h23778c.2.2.1
                            have p23778_3 := h23778c.2.2.2
                            linarith only [h14799, hc01, hc12, hlam, hphi, p23778_1]
                          · have p23778_0 := h23778c.1
                            have p23778_1 := h23778c.2.1
                            have p23778_2 := h23778c.2.2.1
                            have p23778_3 := h23778c.2.2.2
                            linarith only [h16563, hc01, hc12, hlam, hphi, p23778_1]
                          · have p23778_0 := h23778c.1
                            have p23778_1 := h23778c.2.1
                            have p23778_2 := h23778c.2.2.1
                            have p23778_3 := h23778c.2.2.2
                            linarith only [h17994, hc01, hc12, hlam, hphi, p23778_1]
                          · have p23778_0 := h23778c.1
                            have p23778_1 := h23778c.2.1
                            have p23778_2 := h23778c.2.2.1
                            have p23778_3 := h23778c.2.2.2
                            rcases p23778_3 (m.d 0 1) (by simp) with h23795 | h23795
                            · linarith only [h23795, hlam, p23778_0]
                            · rcases p23778_3 (m.d 1 2) (by simp) with h23797 | h23797
                              · rcases p23778_3 (m.d 1 3) (by simp) with h23798 | h23798
                                · rcases p23778_3 (m.d 1 4) (by simp) with h23799 | h23799
                                  · linarith only [h23672, h23799, hlam]
                                  · linarith only [h16563, h23799, hlam]
                                · linarith only [h23798, hlam, p23778_0]
                              · linarith only [h0, h23797, hlam]
                          · have p23778_0 := h23778c.1
                            have p23778_1 := h23778c.2.1
                            have p23778_2 := h23778c.2.2.1
                            have p23778_3 := h23778c.2.2.2
                            linarith only [h23669, hlam, p23778_1]
                          · have p23778_0 := h23778c.1
                            have p23778_1 := h23778c.2.1
                            have p23778_2 := h23778c.2.2.1
                            have p23778_3 := h23778c.2.2.2
                            linarith only [hlam, p23778_0]
                          · have p23778_0 := h23778c.1
                            have p23778_1 := h23778c.2.1
                            have p23778_2 := h23778c.2.2.1
                            have p23778_3 := h23778c.2.2.2
                            linarith only [h16563, hc01, hc13, hlam, hphi, p23778_1]
                          · have p23778_0 := h23778c.1
                            have p23778_1 := h23778c.2.1
                            have p23778_2 := h23778c.2.2.1
                            have p23778_3 := h23778c.2.2.2
                            linarith only [h0, h23332, h23669, h23671, hc01, hc12, hlam, hphi, p23778_1]
                          · have p23778_0 := h23778c.1
                            have p23778_1 := h23778c.2.1
                            have p23778_2 := h23778c.2.2.1
                            have p23778_3 := h23778c.2.2.2
                            rcases p23778_3 (m.d 0 1) (by simp) with h23808 | h23808
                            · linarith only [h23808, hlam, p23778_0]
                            · rcases p23778_3 (m.d 1 2) (by simp) with h23810 | h23810
                              · rcases p23778_3 (m.d 1 3) (by simp) with h23811 | h23811
                                · rcases p23778_3 (m.d 1 4) (by simp) with h23812 | h23812
                                  · rcases p23778_3 (m.d 1 5) (by simp) with h23813 | h23813
                                    · linarith only [h23674, h23813, hlam]
                                    · linarith only [h17994, h23813, hlam]
                                  · linarith only [h23812, hlam, p23778_0]
                                · linarith only [h14799, h23811, hlam]
                              · linarith only [h0, h23810, hlam]
                          · have p23778_0 := h23778c.1
                            have p23778_1 := h23778c.2.1
                            have p23778_2 := h23778c.2.2.1
                            have p23778_3 := h23778c.2.2.2
                            linarith only [h23670, hlam, p23778_1]
                          · have p23778_0 := h23778c.1
                            have p23778_1 := h23778c.2.1
                            have p23778_2 := h23778c.2.2.1
                            have p23778_3 := h23778c.2.2.2
                            linarith only [h23672, hlam, p23778_0]
                          · have p23778_0 := h23778c.1
                            have p23778_1 := h23778c.2.1
                            have p23778_2 := h23778c.2.2.1
                            have p23778_3 := h23778c.2.2.2
                            linarith only [hlam, p23778_0]
                          · have p23778_0 := h23778c.1
                            have p23778_1 := h23778c.2.1
                            have p23778_2 := h23778c.2.2.1
                            have p23778_3 := h23778c.2.2.2
                            linarith only [h0, h23332, h23671, hc01, hc14, hlam, hphi, p23778_1]
                          · have p23778_0 := h23778c.1
                            have p23778_1 := h23778c.2.1
                            have p23778_2 := h23778c.2.2.1
                            have p23778_3 := h23778c.2.2.2
                            rcases p23778_3 (m.d 0 1) (by simp) with h23823 | h23823
                            · linarith only [h23823, hlam, p23778_0]
                            · rcases p23778_3 (m.d 1 2) (by simp) with h23825 | h23825
                              · rcases p23778_3 (m.d 1 3) (by simp) with h23826 | h23826
                                · rcases p23778_3 (m.d 1 4) (by simp) with h23827 | h23827
                                  · rcases p23778_3 (m.d 1 5) (by simp) with h23828 | h23828
                                    · rcases h3bigk with h23829c | h23829c | h23829c | h23829c | h23829c | h23829c | h23829c | h23829c | h23829c | h23829c | h23829c | h23829c | h23829c | h23829c | h23829c | h23829c | h23829c | h23829c | h23829c | h23829c | h23829c | h23829c | h23829c | h23829c | h23829c
                                      · have p23829_0 := h23829c.1
                                        have p23829_1 := h23829c.2.1
                                        have p23829_2 := h23829c.2.2.1
                                        have p23829_3 := h23829c.2.2.2
                                        linarith only [hlam, p23829_0]
                                      · have p23829_0 := h23829c.1
                                        have p23829_1 := h23829c.2.1
                                        have p23829_2 := h23829c.2.2.1
                                        have p23829_3 := h23829c.2.2.2
                                        linarith only [h14799, hlam, p23829_1]
                                      · have p23829_0 := h23829c.1
                                        have p23829_1 := h23829c.2.1
                                        have p23829_2 := h23829c.2.2.1
                                        have p23829_3 := h23829c.2.2.2
                                        linarith only [h19110, hlam, p23829_1]
                                      · have p23829_0 := h23829c.1
                                        have p23829_1 := h23829c.2.1
                                        have p23829_2 := h23829c.2.2.1
                                        have p23829_3 := h23829c.2.2.2
                                        rcases p23829_3 (m.d 0 3) (by simp) with h23833 | h23833
                                        · rcases p23829_3 (m.d 1 3) (by simp) with h23834 | h23834
                                          · rcases p23829_3 (m.d 2 3) (by simp) with h23835 | h23835
                                            · rcases p23829_3 (m.d 3 4) (by simp) with h23836 | h23836
                                              · linarith only [h23836, hlam, p23829_0]
                                              · rcases p23829_3 (m.d 3 5) (by simp) with h23838 | h23838
                                                · linarith only [h23667, h23838, hlam]
                                                · linarith only [h23678, h23838, hlam]
                                            · linarith only [h23675, h23835, hlam]
                                          · linarith only [h23672, h23834, hlam]
                                        · linarith only [h23833, hlam, p23829_0]
                                      · have p23829_0 := h23829c.1
                                        have p23829_1 := h23829c.2.1
                                        have p23829_2 := h23829c.2.2.1
                                        have p23829_3 := h23829c.2.2.2
                                        rcases p23829_3 (m.d 0 3) (by simp) with h23844 | h23844
                                        · rcases p23829_3 (m.d 1 3) (by simp) with h23845 | h23845
                                          · rcases p23829_3 (m.d 2 3) (by simp) with h23846 | h23846
                                            · rcases p23829_3 (m.d 3 4) (by simp) with h23847 | h23847
                                              · linarith only [h23666, h23847, hlam]
                                              · rcases p23829_3 (m.d 3 5) (by simp) with h23849 | h23849
                                                · linarith only [h23849, hlam, p23829_0]
                                                · rcases h5bigk with h23851c | h23851c | h23851c | h23851c | h23851c | h23851c | h23851c | h23851c | h23851c | h23851c | h23851c | h23851c | h23851c | h23851c | h23851c | h23851c | h23851c | h23851c | h23851c | h23851c | h23851c | h23851c | h23851c | h23851c | h23851c
                                                  · have p23851_0 := h23851c.1
                                                    have p23851_1 := h23851c.2.1
                                                    have p23851_2 := h23851c.2.2.1
                                                    have p23851_3 := h23851c.2.2.2
                                                    linarith only [hlam, p23851_0]
                                                  · have p23851_0 := h23851c.1
                                                    have p23851_1 := h23851c.2.1
                                                    have p23851_2 := h23851c.2.2.1
                                                    have p23851_3 := h23851c.2.2.2
                                                    linarith only [h17994, hlam, p23851_1]
                                                  · have p23851_0 := h23851c.1
                                                    have p23851_1 := h23851c.2.1
                                                    have p23851_2 := h23851c.2.2.1
                                                    have p23851_3 := h23851c.2.2.2
                                                    linarith only [h23332, hlam, p23851_0]
                                                  · have p23851_0 := h23851c.1
                                                    have p23851_1 := h23851c.2.1
                                                    have p23851_2 := h23851c.2.2.1
                                                    have p23851_3 := h23851c.2.2.2
                                                    linarith only [h19110, h23667, h23669, h23678, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23851_1]
                                                  · have p23851_0 := h23851c.1
                                                    have p23851_1 := h23851c.2.1
                                                    have p23851_2 := h23851c.2.2.1
                                                    have p23851_3 := h23851c.2.2.2
                                                    linarith only [h19110, h23666, h23668, h23669, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p23851_1]
                                                  · have p23851_0 := h23851c.1
                                                    have p23851_1 := h23851c.2.1
                                                    have p23851_2 := h23851c.2.2.1
                                                    have p23851_3 := h23851c.2.2.2
                                                    linarith only [h17994, hc01, hc15, hlam, hphi, p23851_1]
                                                  · have p23851_0 := h23851c.1
                                                    have p23851_1 := h23851c.2.1
                                                    have p23851_2 := h23851c.2.2.1
                                                    have p23851_3 := h23851c.2.2.2
                                                    linarith only [hlam, p23851_0]
                                                  · have p23851_0 := h23851c.1
                                                    have p23851_1 := h23851c.2.1
                                                    have p23851_2 := h23851c.2.2.1
                                                    have p23851_3 := h23851c.2.2.2
                                                    linarith only [h0, h23332, h23671, hc01, hc12, hlam, hphi, p23851_1]
                                                  · have p23851_0 := h23851c.1
                                                    have p23851_1 := h23851c.2.1
                                                    have p23851_2 := h23851c.2.2.1
                                                    have p23851_3 := h23851c.2.2.2
                                                    rcases p23851_3 (m.d 0 5) (by simp) with h23860 | h23860
                                                    · linarith only [h17994, h23860, hlam]
                                                    · linarith only [h23667, h23860, hlam]
                                                  · have p23851_0 := h23851c.1
                                                    have p23851_1 := h23851c.2.1
                                                    have p23851_2 := h23851c.2.2.1
                                                    have p23851_3 := h23851c.2.2.2
                                                    linarith only [h23669, h23672, h23674, h23678, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23851_1]
                                                  · have p23851_0 := h23851c.1
                                                    have p23851_1 := h23851c.2.1
                                                    have p23851_2 := h23851c.2.2.1
                                                    have p23851_3 := h23851c.2.2.2
                                                    linarith only [h23668, h23678, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p23851_1]
                                                  · have p23851_0 := h23851c.1
                                                    have p23851_1 := h23851c.2.1
                                                    have p23851_2 := h23851c.2.2.1
                                                    have p23851_3 := h23851c.2.2.2
                                                    linarith only [h23671, hlam, p23851_1]
                                                  · have p23851_0 := h23851c.1
                                                    have p23851_1 := h23851c.2.1
                                                    have p23851_2 := h23851c.2.2.1
                                                    have p23851_3 := h23851c.2.2.2
                                                    linarith only [hlam, p23851_0]
                                                  · have p23851_0 := h23851c.1
                                                    have p23851_1 := h23851c.2.1
                                                    have p23851_2 := h23851c.2.2.1
                                                    have p23851_3 := h23851c.2.2.2
                                                    linarith only [h23669, h23676, h23678, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23851_1]
                                                  · have p23851_0 := h23851c.1
                                                    have p23851_1 := h23851c.2.1
                                                    have p23851_2 := h23851c.2.2.1
                                                    have p23851_3 := h23851c.2.2.2
                                                    linarith only [h23669, h23675, h23677, h23678, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23851_1]
                                                  · have p23851_0 := h23851c.1
                                                    have p23851_1 := h23851c.2.1
                                                    have p23851_2 := h23851c.2.2.1
                                                    have p23851_3 := h23851c.2.2.2
                                                    linarith only [h23667, hlam, p23851_0]
                                                  · have p23851_0 := h23851c.1
                                                    have p23851_1 := h23851c.2.1
                                                    have p23851_2 := h23851c.2.2.1
                                                    have p23851_3 := h23851c.2.2.2
                                                    linarith only [h23673, hlam, p23851_0]
                                                  · have p23851_0 := h23851c.1
                                                    have p23851_1 := h23851c.2.1
                                                    have p23851_2 := h23851c.2.2.1
                                                    have p23851_3 := h23851c.2.2.2
                                                    linarith only [h23676, hlam, p23851_0]
                                                  · have p23851_0 := h23851c.1
                                                    have p23851_1 := h23851c.2.1
                                                    have p23851_2 := h23851c.2.2.1
                                                    have p23851_3 := h23851c.2.2.2
                                                    linarith only [hlam, p23851_0]
                                                  · have p23851_0 := h23851c.1
                                                    have p23851_1 := h23851c.2.1
                                                    have p23851_2 := h23851c.2.2.1
                                                    have p23851_3 := h23851c.2.2.2
                                                    linarith only [h23678, hlam, p23851_1]
                                                  · have p23851_0 := h23851c.1
                                                    have p23851_1 := h23851c.2.1
                                                    have p23851_2 := h23851c.2.2.1
                                                    have p23851_3 := h23851c.2.2.2
                                                    linarith only [h23668, hlam, p23851_0]
                                                  · have p23851_0 := h23851c.1
                                                    have p23851_1 := h23851c.2.1
                                                    have p23851_2 := h23851c.2.2.1
                                                    have p23851_3 := h23851c.2.2.2
                                                    linarith only [h23674, hlam, p23851_0]
                                                  · have p23851_0 := h23851c.1
                                                    have p23851_1 := h23851c.2.1
                                                    have p23851_2 := h23851c.2.2.1
                                                    have p23851_3 := h23851c.2.2.2
                                                    linarith only [h23677, hlam, p23851_0]
                                                  · have p23851_0 := h23851c.1
                                                    have p23851_1 := h23851c.2.1
                                                    have p23851_2 := h23851c.2.2.1
                                                    have p23851_3 := h23851c.2.2.2
                                                    linarith only [h23678, hc34, hc45, hlam, hphi, p23851_1]
                                                  · have p23851_0 := h23851c.1
                                                    have p23851_1 := h23851c.2.1
                                                    have p23851_2 := h23851c.2.2.1
                                                    have p23851_3 := h23851c.2.2.2
                                                    linarith only [hlam, p23851_0]
                                            · linarith only [h23676, h23846, hlam]
                                          · linarith only [h23673, h23845, hlam]
                                        · linarith only [h23844, hlam, p23829_0]
                                      · have p23829_0 := h23829c.1
                                        have p23829_1 := h23829c.2.1
                                        have p23829_2 := h23829c.2.2.1
                                        have p23829_3 := h23829c.2.2.2
                                        linarith only [h23666, h23668, h23669, h23678, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23829_1]
                                      · have p23829_0 := h23829c.1
                                        have p23829_1 := h23829c.2.1
                                        have p23829_2 := h23829c.2.2.1
                                        have p23829_3 := h23829c.2.2.2
                                        linarith only [hlam, p23829_0]
                                      · have p23829_0 := h23829c.1
                                        have p23829_1 := h23829c.2.1
                                        have p23829_2 := h23829c.2.2.1
                                        have p23829_3 := h23829c.2.2.2
                                        linarith only [h0, h19110, h23669, hc01, hc12, hlam, hphi, p23829_1]
                                      · have p23829_0 := h23829c.1
                                        have p23829_1 := h23829c.2.1
                                        have p23829_2 := h23829c.2.2.1
                                        have p23829_3 := h23829c.2.2.2
                                        rcases p23829_3 (m.d 0 3) (by simp) with h23885 | h23885
                                        · linarith only [h14799, h23885, hlam]
                                        · linarith only [h23666, h23885, hlam]
                                      · have p23829_0 := h23829c.1
                                        have p23829_1 := h23829c.2.1
                                        have p23829_2 := h23829c.2.2.1
                                        have p23829_3 := h23829c.2.2.2
                                        rcases p23829_3 (m.d 0 3) (by simp) with h23888 | h23888
                                        · linarith only [h14799, h23888, hlam]
                                        · linarith only [h23667, h23888, hlam]
                                      · have p23829_0 := h23829c.1
                                        have p23829_1 := h23829c.2.1
                                        have p23829_2 := h23829c.2.2.1
                                        have p23829_3 := h23829c.2.2.2
                                        linarith only [h23666, h23668, h23669, h23678, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23829_1]
                                      · have p23829_0 := h23829c.1
                                        have p23829_1 := h23829c.2.1
                                        have p23829_2 := h23829c.2.2.1
                                        have p23829_3 := h23829c.2.2.2
                                        linarith only [h23669, hlam, p23829_0]
                                      · have p23829_0 := h23829c.1
                                        have p23829_1 := h23829c.2.1
                                        have p23829_2 := h23829c.2.2.1
                                        have p23829_3 := h23829c.2.2.2
                                        linarith only [hlam, p23829_0]
                                      · have p23829_0 := h23829c.1
                                        have p23829_1 := h23829c.2.1
                                        have p23829_2 := h23829c.2.2.1
                                        have p23829_3 := h23829c.2.2.2
                                        rcases p23829_3 (m.d 0 3) (by simp) with h23894 | h23894
                                        · linarith only [h19110, h23894, hlam]
                                        · linarith only [h23666, h23894, hlam]
                                      · have p23829_0 := h23829c.1
                                        have p23829_1 := h23829c.2.1
                                        have p23829_2 := h23829c.2.2.1
                                        have p23829_3 := h23829c.2.2.2
                                        rcases p23829_3 (m.d 0 3) (by simp) with h23897 | h23897
                                        · linarith only [h19110, h23897, hlam]
                                        · linarith only [h23667, h23897, hlam]
                                      · have p23829_0 := h23829c.1
                                        have p23829_1 := h23829c.2.1
                                        have p23829_2 := h23829c.2.2.1
                                        have p23829_3 := h23829c.2.2.2
                                        linarith only [h23666, hlam, p23829_0]
                                      · have p23829_0 := h23829c.1
                                        have p23829_1 := h23829c.2.1
                                        have p23829_2 := h23829c.2.2.1
                                        have p23829_3 := h23829c.2.2.2
                                        linarith only [h23672, hlam, p23829_0]
                                      · have p23829_0 := h23829c.1
                                        have p23829_1 := h23829c.2.1
                                        have p23829_2 := h23829c.2.2.1
                                        have p23829_3 := h23829c.2.2.2
                                        linarith only [h23675, hlam, p23829_0]
                                      · have p23829_0 := h23829c.1
                                        have p23829_1 := h23829c.2.1
                                        have p23829_2 := h23829c.2.2.1
                                        have p23829_3 := h23829c.2.2.2
                                        linarith only [hlam, p23829_0]
                                      · have p23829_0 := h23829c.1
                                        have p23829_1 := h23829c.2.1
                                        have p23829_2 := h23829c.2.2.1
                                        have p23829_3 := h23829c.2.2.2
                                        linarith only [h23678, hlam, p23829_1]
                                      · have p23829_0 := h23829c.1
                                        have p23829_1 := h23829c.2.1
                                        have p23829_2 := h23829c.2.2.1
                                        have p23829_3 := h23829c.2.2.2
                                        linarith only [h23667, hlam, p23829_0]
                                      · have p23829_0 := h23829c.1
                                        have p23829_1 := h23829c.2.1
                                        have p23829_2 := h23829c.2.2.1
                                        have p23829_3 := h23829c.2.2.2
                                        linarith only [h23673, hlam, p23829_0]
                                      · have p23829_0 := h23829c.1
                                        have p23829_1 := h23829c.2.1
                                        have p23829_2 := h23829c.2.2.1
                                        have p23829_3 := h23829c.2.2.2
                                        linarith only [h23676, hlam, p23829_0]
                                      · have p23829_0 := h23829c.1
                                        have p23829_1 := h23829c.2.1
                                        have p23829_2 := h23829c.2.2.1
                                        have p23829_3 := h23829c.2.2.2
                                        linarith only [h19110, h23667, h23669, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23829_1]
                                      · have p23829_0 := h23829c.1
                                        have p23829_1 := h23829c.2.1
                                        have p23829_2 := h23829c.2.2.1
                                        have p23829_3 := h23829c.2.2.2
                                        linarith only [hlam, p23829_0]
                                    · linarith only [h23828, hlam, p23778_0]
                                  · linarith only [h16563, h23827, hlam]
                                · linarith only [h14799, h23826, hlam]
                              · linarith only [h0, h23825, hlam]
                          · have p23778_0 := h23778c.1
                            have p23778_1 := h23778c.2.1
                            have p23778_2 := h23778c.2.2.1
                            have p23778_3 := h23778c.2.2.2
                            linarith only [h23671, hlam, p23778_1]
                          · have p23778_0 := h23778c.1
                            have p23778_1 := h23778c.2.1
                            have p23778_2 := h23778c.2.2.1
                            have p23778_3 := h23778c.2.2.2
                            linarith only [h23673, hlam, p23778_0]
                          · have p23778_0 := h23778c.1
                            have p23778_1 := h23778c.2.1
                            have p23778_2 := h23778c.2.2.1
                            have p23778_3 := h23778c.2.2.2
                            linarith only [h23674, hlam, p23778_0]
                          · have p23778_0 := h23778c.1
                            have p23778_1 := h23778c.2.1
                            have p23778_2 := h23778c.2.2.1
                            have p23778_3 := h23778c.2.2.2
                            linarith only [hlam, p23778_0]
                      · linarith only [h0, h16563, h22593, h23668, h23672, h23677, hc01, hc13, hlam, hphi]
                    · linarith only [h19110, h23667, h23676, hlam]
                  · linarith only [h19110, h23666, h23675, hlam]
                · linarith only [h22593, h23668, h23670, h23674, hlam]
              · linarith only [h19110, h23667, h23669, h23673, hlam]
            · linarith only [h19110, h23666, h23669, h23672, hlam]
          · linarith only [h0, h19110, h23669, h23671, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h19110, h23669, h23670, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h23926 | h23926
        · linarith only [h0, h22593, h23669, h23926, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h23928 | h23928
          · linarith only [h0, h23332, h23669, h23928, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h23930 | h23930
            · rcases m.htr 1 3 5 (by decide) (by decide) with h23931 | h23931
              · rcases m.htr 1 4 5 (by decide) (by decide) with h23932 | h23932
                · rcases m.htr 2 3 4 (by decide) (by decide) with h23933 | h23933
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h23934 | h23934
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h23935 | h23935
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h23936 | h23936
                        · rcases h1bigk with h23937c | h23937c | h23937c | h23937c | h23937c | h23937c | h23937c | h23937c | h23937c | h23937c | h23937c | h23937c | h23937c | h23937c | h23937c | h23937c | h23937c | h23937c | h23937c | h23937c | h23937c | h23937c | h23937c | h23937c | h23937c
                          · have p23937_0 := h23937c.1
                            have p23937_1 := h23937c.2.1
                            have p23937_2 := h23937c.2.2.1
                            have p23937_3 := h23937c.2.2.2
                            linarith only [hlam, p23937_0]
                          · have p23937_0 := h23937c.1
                            have p23937_1 := h23937c.2.1
                            have p23937_2 := h23937c.2.2.1
                            have p23937_3 := h23937c.2.2.2
                            linarith only [h0, hlam, p23937_0]
                          · have p23937_0 := h23937c.1
                            have p23937_1 := h23937c.2.1
                            have p23937_2 := h23937c.2.2.1
                            have p23937_3 := h23937c.2.2.2
                            linarith only [h14799, hlam, p23937_0]
                          · have p23937_0 := h23937c.1
                            have p23937_1 := h23937c.2.1
                            have p23937_2 := h23937c.2.2.1
                            have p23937_3 := h23937c.2.2.2
                            linarith only [h16563, hlam, p23937_0]
                          · have p23937_0 := h23937c.1
                            have p23937_1 := h23937c.2.1
                            have p23937_2 := h23937c.2.2.1
                            have p23937_3 := h23937c.2.2.2
                            linarith only [h17994, hlam, p23937_0]
                          · have p23937_0 := h23937c.1
                            have p23937_1 := h23937c.2.1
                            have p23937_2 := h23937c.2.2.1
                            have p23937_3 := h23937c.2.2.2
                            linarith only [h23928, h23933, h23935, hc01, hc23, hlam, hphi, ht12, p23937_1]
                          · have p23937_0 := h23937c.1
                            have p23937_1 := h23937c.2.1
                            have p23937_2 := h23937c.2.2.1
                            have p23937_3 := h23937c.2.2.2
                            linarith only [hlam, p23937_0]
                          · have p23937_0 := h23937c.1
                            have p23937_1 := h23937c.2.1
                            have p23937_2 := h23937c.2.2.1
                            have p23937_3 := h23937c.2.2.2
                            linarith only [h23669, hlam, p23937_0]
                          · have p23937_0 := h23937c.1
                            have p23937_1 := h23937c.2.1
                            have p23937_2 := h23937c.2.2.1
                            have p23937_3 := h23937c.2.2.2
                            linarith only [h23926, hlam, p23937_0]
                          · have p23937_0 := h23937c.1
                            have p23937_1 := h23937c.2.1
                            have p23937_2 := h23937c.2.2.1
                            have p23937_3 := h23937c.2.2.2
                            linarith only [h23928, hlam, p23937_0]
                          · have p23937_0 := h23937c.1
                            have p23937_1 := h23937c.2.1
                            have p23937_2 := h23937c.2.2.1
                            have p23937_3 := h23937c.2.2.2
                            rcases p23937_3 (m.d 0 1) (by simp) with h23948 | h23948
                            · linarith only [h23948, hlam, p23937_0]
                            · rcases p23937_3 (m.d 1 2) (by simp) with h23950 | h23950
                              · linarith only [h23669, h23950, hlam]
                              · linarith only [h0, h23950, hlam]
                          · have p23937_0 := h23937c.1
                            have p23937_1 := h23937c.2.1
                            have p23937_2 := h23937c.2.2.1
                            have p23937_3 := h23937c.2.2.2
                            linarith only [h0, hc01, hc13, hlam, hphi, p23937_1]
                          · have p23937_0 := h23937c.1
                            have p23937_1 := h23937c.2.1
                            have p23937_2 := h23937c.2.2.1
                            have p23937_3 := h23937c.2.2.2
                            linarith only [hlam, p23937_0]
                          · have p23937_0 := h23937c.1
                            have p23937_1 := h23937c.2.1
                            have p23937_2 := h23937c.2.2.1
                            have p23937_3 := h23937c.2.2.2
                            linarith only [h0, h23669, h23928, h23932, hc01, hc23, hlam, hphi, ht12, p23937_1]
                          · have p23937_0 := h23937c.1
                            have p23937_1 := h23937c.2.1
                            have p23937_2 := h23937c.2.2.1
                            have p23937_3 := h23937c.2.2.2
                            linarith only [h0, h23669, h23928, hc01, hc23, hlam, hphi, ht12, p23937_1]
                          · have p23937_0 := h23937c.1
                            have p23937_1 := h23937c.2.1
                            have p23937_2 := h23937c.2.2.1
                            have p23937_3 := h23937c.2.2.2
                            rcases p23937_3 (m.d 0 1) (by simp) with h23957 | h23957
                            · linarith only [h23957, hlam, p23937_0]
                            · rcases p23937_3 (m.d 1 2) (by simp) with h23959 | h23959
                              · linarith only [h23926, h23959, hlam]
                              · linarith only [h0, h23959, hlam]
                          · have p23937_0 := h23937c.1
                            have p23937_1 := h23937c.2.1
                            have p23937_2 := h23937c.2.2.1
                            have p23937_3 := h23937c.2.2.2
                            linarith only [h0, hc01, hc14, hlam, hphi, p23937_1]
                          · have p23937_0 := h23937c.1
                            have p23937_1 := h23937c.2.1
                            have p23937_2 := h23937c.2.2.1
                            have p23937_3 := h23937c.2.2.2
                            linarith only [h23930, hlam, p23937_0]
                          · have p23937_0 := h23937c.1
                            have p23937_1 := h23937c.2.1
                            have p23937_2 := h23937c.2.2.1
                            have p23937_3 := h23937c.2.2.2
                            linarith only [hlam, p23937_0]
                          · have p23937_0 := h23937c.1
                            have p23937_1 := h23937c.2.1
                            have p23937_2 := h23937c.2.2.1
                            have p23937_3 := h23937c.2.2.2
                            linarith only [h0, h23926, h23928, h23933, hc01, hc23, hlam, hphi, ht12, p23937_1]
                          · have p23937_0 := h23937c.1
                            have p23937_1 := h23937c.2.1
                            have p23937_2 := h23937c.2.2.1
                            have p23937_3 := h23937c.2.2.2
                            rcases p23937_3 (m.d 0 1) (by simp) with h23966 | h23966
                            · linarith only [h23966, hlam, p23937_0]
                            · rcases p23937_3 (m.d 1 2) (by simp) with h23968 | h23968
                              · linarith only [h23928, h23968, hlam]
                              · linarith only [h0, h23968, hlam]
                          · have p23937_0 := h23937c.1
                            have p23937_1 := h23937c.2.1
                            have p23937_2 := h23937c.2.2.1
                            have p23937_3 := h23937c.2.2.2
                            linarith only [h0, hc01, hc15, hlam, hphi, p23937_1]
                          · have p23937_0 := h23937c.1
                            have p23937_1 := h23937c.2.1
                            have p23937_2 := h23937c.2.2.1
                            have p23937_3 := h23937c.2.2.2
                            linarith only [h23931, hlam, p23937_0]
                          · have p23937_0 := h23937c.1
                            have p23937_1 := h23937c.2.1
                            have p23937_2 := h23937c.2.2.1
                            have p23937_3 := h23937c.2.2.2
                            linarith only [h23932, hlam, p23937_0]
                          · have p23937_0 := h23937c.1
                            have p23937_1 := h23937c.2.1
                            have p23937_2 := h23937c.2.2.1
                            have p23937_3 := h23937c.2.2.2
                            linarith only [hlam, p23937_0]
                        · rcases h1bigk with h23975c | h23975c | h23975c | h23975c | h23975c | h23975c | h23975c | h23975c | h23975c | h23975c | h23975c | h23975c | h23975c | h23975c | h23975c | h23975c | h23975c | h23975c | h23975c | h23975c | h23975c | h23975c | h23975c | h23975c | h23975c
                          · have p23975_0 := h23975c.1
                            have p23975_1 := h23975c.2.1
                            have p23975_2 := h23975c.2.2.1
                            have p23975_3 := h23975c.2.2.2
                            linarith only [hlam, p23975_0]
                          · have p23975_0 := h23975c.1
                            have p23975_1 := h23975c.2.1
                            have p23975_2 := h23975c.2.2.1
                            have p23975_3 := h23975c.2.2.2
                            linarith only [h0, hlam, p23975_0]
                          · have p23975_0 := h23975c.1
                            have p23975_1 := h23975c.2.1
                            have p23975_2 := h23975c.2.2.1
                            have p23975_3 := h23975c.2.2.2
                            linarith only [h14799, hlam, p23975_0]
                          · have p23975_0 := h23975c.1
                            have p23975_1 := h23975c.2.1
                            have p23975_2 := h23975c.2.2.1
                            have p23975_3 := h23975c.2.2.2
                            linarith only [h16563, hlam, p23975_0]
                          · have p23975_0 := h23975c.1
                            have p23975_1 := h23975c.2.1
                            have p23975_2 := h23975c.2.2.1
                            have p23975_3 := h23975c.2.2.2
                            linarith only [h17994, hlam, p23975_0]
                          · have p23975_0 := h23975c.1
                            have p23975_1 := h23975c.2.1
                            have p23975_2 := h23975c.2.2.1
                            have p23975_3 := h23975c.2.2.2
                            linarith only [h23669, hc01, hc23, hlam, hphi, ht12, p23975_1]
                          · have p23975_0 := h23975c.1
                            have p23975_1 := h23975c.2.1
                            have p23975_2 := h23975c.2.2.1
                            have p23975_3 := h23975c.2.2.2
                            linarith only [hlam, p23975_0]
                          · have p23975_0 := h23975c.1
                            have p23975_1 := h23975c.2.1
                            have p23975_2 := h23975c.2.2.1
                            have p23975_3 := h23975c.2.2.2
                            linarith only [h23669, hlam, p23975_0]
                          · have p23975_0 := h23975c.1
                            have p23975_1 := h23975c.2.1
                            have p23975_2 := h23975c.2.2.1
                            have p23975_3 := h23975c.2.2.2
                            linarith only [h23926, hlam, p23975_0]
                          · have p23975_0 := h23975c.1
                            have p23975_1 := h23975c.2.1
                            have p23975_2 := h23975c.2.2.1
                            have p23975_3 := h23975c.2.2.2
                            linarith only [h23928, hlam, p23975_0]
                          · have p23975_0 := h23975c.1
                            have p23975_1 := h23975c.2.1
                            have p23975_2 := h23975c.2.2.1
                            have p23975_3 := h23975c.2.2.2
                            rcases p23975_3 (m.d 0 1) (by simp) with h23986 | h23986
                            · linarith only [h23986, hlam, p23975_0]
                            · rcases p23975_3 (m.d 1 2) (by simp) with h23988 | h23988
                              · linarith only [h23669, h23988, hlam]
                              · linarith only [h0, h23988, hlam]
                          · have p23975_0 := h23975c.1
                            have p23975_1 := h23975c.2.1
                            have p23975_2 := h23975c.2.2.1
                            have p23975_3 := h23975c.2.2.2
                            linarith only [h0, h23669, hc01, hc23, hlam, hphi, ht12, p23975_1]
                          · have p23975_0 := h23975c.1
                            have p23975_1 := h23975c.2.1
                            have p23975_2 := h23975c.2.2.1
                            have p23975_3 := h23975c.2.2.2
                            linarith only [hlam, p23975_0]
                          · have p23975_0 := h23975c.1
                            have p23975_1 := h23975c.2.1
                            have p23975_2 := h23975c.2.2.1
                            have p23975_3 := h23975c.2.2.2
                            linarith only [h16563, h23669, hc01, hc23, hlam, hphi, ht12, p23975_1]
                          · have p23975_0 := h23975c.1
                            have p23975_1 := h23975c.2.1
                            have p23975_2 := h23975c.2.2.1
                            have p23975_3 := h23975c.2.2.2
                            linarith only [h17994, h23669, hc01, hc23, hlam, hphi, ht12, p23975_1]
                          · have p23975_0 := h23975c.1
                            have p23975_1 := h23975c.2.1
                            have p23975_2 := h23975c.2.2.1
                            have p23975_3 := h23975c.2.2.2
                            rcases p23975_3 (m.d 0 1) (by simp) with h23995 | h23995
                            · linarith only [h23995, hlam, p23975_0]
                            · rcases p23975_3 (m.d 1 2) (by simp) with h23997 | h23997
                              · linarith only [h23926, h23997, hlam]
                              · linarith only [h0, h23997, hlam]
                          · have p23975_0 := h23975c.1
                            have p23975_1 := h23975c.2.1
                            have p23975_2 := h23975c.2.2.1
                            have p23975_3 := h23975c.2.2.2
                            linarith only [h0, hc01, hc14, hlam, hphi, p23975_1]
                          · have p23975_0 := h23975c.1
                            have p23975_1 := h23975c.2.1
                            have p23975_2 := h23975c.2.2.1
                            have p23975_3 := h23975c.2.2.2
                            linarith only [h23930, hlam, p23975_0]
                          · have p23975_0 := h23975c.1
                            have p23975_1 := h23975c.2.1
                            have p23975_2 := h23975c.2.2.1
                            have p23975_3 := h23975c.2.2.2
                            linarith only [hlam, p23975_0]
                          · have p23975_0 := h23975c.1
                            have p23975_1 := h23975c.2.1
                            have p23975_2 := h23975c.2.2.1
                            have p23975_3 := h23975c.2.2.2
                            linarith only [h17994, h23926, h23933, hc01, hc23, hlam, hphi, ht12, p23975_1]
                          · have p23975_0 := h23975c.1
                            have p23975_1 := h23975c.2.1
                            have p23975_2 := h23975c.2.2.1
                            have p23975_3 := h23975c.2.2.2
                            rcases p23975_3 (m.d 0 1) (by simp) with h24004 | h24004
                            · linarith only [h24004, hlam, p23975_0]
                            · rcases p23975_3 (m.d 1 2) (by simp) with h24006 | h24006
                              · linarith only [h23928, h24006, hlam]
                              · linarith only [h0, h24006, hlam]
                          · have p23975_0 := h23975c.1
                            have p23975_1 := h23975c.2.1
                            have p23975_2 := h23975c.2.2.1
                            have p23975_3 := h23975c.2.2.2
                            linarith only [h0, hc01, hc15, hlam, hphi, p23975_1]
                          · have p23975_0 := h23975c.1
                            have p23975_1 := h23975c.2.1
                            have p23975_2 := h23975c.2.2.1
                            have p23975_3 := h23975c.2.2.2
                            linarith only [h23931, hlam, p23975_0]
                          · have p23975_0 := h23975c.1
                            have p23975_1 := h23975c.2.1
                            have p23975_2 := h23975c.2.2.1
                            have p23975_3 := h23975c.2.2.2
                            linarith only [h23932, hlam, p23975_0]
                          · have p23975_0 := h23975c.1
                            have p23975_1 := h23975c.2.1
                            have p23975_2 := h23975c.2.2.1
                            have p23975_3 := h23975c.2.2.2
                            linarith only [hlam, p23975_0]
                      · linarith only [h14799, h16563, h23666, h23668, h23669, h23926, h23935, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h14799, h23667, h23669, h23934, hlam]
                  · linarith only [h14799, h23666, h23669, h23933, hlam]
                · linarith only [h16563, h23668, h23932, hlam]
              · linarith only [h14799, h23667, h23931, hlam]
            · linarith only [h14799, h23666, h23930, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h24019 | h24019
      · rcases m.htr 1 2 4 (by decide) (by decide) with h24020 | h24020
        · rcases m.htr 1 2 5 (by decide) (by decide) with h24021 | h24021
          · rcases m.htr 1 3 4 (by decide) (by decide) with h24022 | h24022
            · rcases m.htr 1 3 5 (by decide) (by decide) with h24023 | h24023
              · rcases m.htr 1 4 5 (by decide) (by decide) with h24024 | h24024
                · rcases m.htr 2 3 4 (by decide) (by decide) with h24025 | h24025
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h24026 | h24026
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h24027 | h24027
                      · linarith only [h16563, h23668, h24020, h24027, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h22593, h24019, h24022, h24024, h24027, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h14799, h19110, h23667, h24019, h24026, hc01, hc12, hlam, hphi]
                  · linarith only [h19110, h23666, h24025, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h24032 | h24032
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h24033 | h24033
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h24034 | h24034
                      · linarith only [h16563, h24024, h24034, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h24036 | h24036
                        · linarith only [h0, h22593, h24020, h24024, h24036, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases h1bigk with h24038c | h24038c | h24038c | h24038c | h24038c | h24038c | h24038c | h24038c | h24038c | h24038c | h24038c | h24038c | h24038c | h24038c | h24038c | h24038c | h24038c | h24038c | h24038c | h24038c | h24038c | h24038c | h24038c | h24038c | h24038c
                          · have p24038_0 := h24038c.1
                            have p24038_1 := h24038c.2.1
                            have p24038_2 := h24038c.2.2.1
                            have p24038_3 := h24038c.2.2.2
                            linarith only [hlam, p24038_0]
                          · have p24038_0 := h24038c.1
                            have p24038_1 := h24038c.2.1
                            have p24038_2 := h24038c.2.2.1
                            have p24038_3 := h24038c.2.2.2
                            linarith only [h0, hlam, p24038_0]
                          · have p24038_0 := h24038c.1
                            have p24038_1 := h24038c.2.1
                            have p24038_2 := h24038c.2.2.1
                            have p24038_3 := h24038c.2.2.2
                            linarith only [h14799, hlam, p24038_0]
                          · have p24038_0 := h24038c.1
                            have p24038_1 := h24038c.2.1
                            have p24038_2 := h24038c.2.2.1
                            have p24038_3 := h24038c.2.2.2
                            linarith only [h16563, hlam, p24038_0]
                          · have p24038_0 := h24038c.1
                            have p24038_1 := h24038c.2.1
                            have p24038_2 := h24038c.2.2.1
                            have p24038_3 := h24038c.2.2.2
                            linarith only [h17994, hlam, p24038_0]
                          · have p24038_0 := h24038c.1
                            have p24038_1 := h24038c.2.1
                            have p24038_2 := h24038c.2.2.1
                            have p24038_3 := h24038c.2.2.2
                            rcases p24038_3 (m.d 0 1) (by simp) with h24044 | h24044
                            · linarith only [h24044, hlam, p24038_0]
                            · rcases p24038_3 (m.d 1 2) (by simp) with h24046 | h24046
                              · rcases p24038_3 (m.d 1 3) (by simp) with h24047 | h24047
                                · linarith only [h24019, h24047, hlam]
                                · linarith only [h14799, h24047, hlam]
                              · linarith only [h24046, hlam, p24038_0]
                          · have p24038_0 := h24038c.1
                            have p24038_1 := h24038c.2.1
                            have p24038_2 := h24038c.2.2.1
                            have p24038_3 := h24038c.2.2.2
                            linarith only [hlam, p24038_0]
                          · have p24038_0 := h24038c.1
                            have p24038_1 := h24038c.2.1
                            have p24038_2 := h24038c.2.2.1
                            have p24038_3 := h24038c.2.2.2
                            linarith only [h14799, hc01, hc12, hlam, hphi, p24038_1]
                          · have p24038_0 := h24038c.1
                            have p24038_1 := h24038c.2.1
                            have p24038_2 := h24038c.2.2.1
                            have p24038_3 := h24038c.2.2.2
                            linarith only [h16563, hc01, hc12, hlam, hphi, p24038_1]
                          · have p24038_0 := h24038c.1
                            have p24038_1 := h24038c.2.1
                            have p24038_2 := h24038c.2.2.1
                            have p24038_3 := h24038c.2.2.2
                            linarith only [h17994, hc01, hc12, hlam, hphi, p24038_1]
                          · have p24038_0 := h24038c.1
                            have p24038_1 := h24038c.2.1
                            have p24038_2 := h24038c.2.2.1
                            have p24038_3 := h24038c.2.2.2
                            rcases p24038_3 (m.d 0 1) (by simp) with h24055 | h24055
                            · linarith only [h24055, hlam, p24038_0]
                            · rcases p24038_3 (m.d 1 2) (by simp) with h24057 | h24057
                              · rcases p24038_3 (m.d 1 3) (by simp) with h24058 | h24058
                                · rcases p24038_3 (m.d 1 4) (by simp) with h24059 | h24059
                                  · linarith only [h24022, h24059, hlam]
                                  · linarith only [h16563, h24059, hlam]
                                · linarith only [h24058, hlam, p24038_0]
                              · linarith only [h0, h24057, hlam]
                          · have p24038_0 := h24038c.1
                            have p24038_1 := h24038c.2.1
                            have p24038_2 := h24038c.2.2.1
                            have p24038_3 := h24038c.2.2.2
                            linarith only [h24019, hlam, p24038_1]
                          · have p24038_0 := h24038c.1
                            have p24038_1 := h24038c.2.1
                            have p24038_2 := h24038c.2.2.1
                            have p24038_3 := h24038c.2.2.2
                            linarith only [hlam, p24038_0]
                          · have p24038_0 := h24038c.1
                            have p24038_1 := h24038c.2.1
                            have p24038_2 := h24038c.2.2.1
                            have p24038_3 := h24038c.2.2.2
                            linarith only [h16563, hc01, hc13, hlam, hphi, p24038_1]
                          · have p24038_0 := h24038c.1
                            have p24038_1 := h24038c.2.1
                            have p24038_2 := h24038c.2.2.1
                            have p24038_3 := h24038c.2.2.2
                            linarith only [h17994, h24019, hc01, hc12, hlam, hphi, p24038_1]
                          · have p24038_0 := h24038c.1
                            have p24038_1 := h24038c.2.1
                            have p24038_2 := h24038c.2.2.1
                            have p24038_3 := h24038c.2.2.2
                            linarith only [h24024, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p24038_1]
                          · have p24038_0 := h24038c.1
                            have p24038_1 := h24038c.2.1
                            have p24038_2 := h24038c.2.2.1
                            have p24038_3 := h24038c.2.2.2
                            linarith only [h24020, hlam, p24038_1]
                          · have p24038_0 := h24038c.1
                            have p24038_1 := h24038c.2.1
                            have p24038_2 := h24038c.2.2.1
                            have p24038_3 := h24038c.2.2.2
                            linarith only [h24022, hlam, p24038_0]
                          · have p24038_0 := h24038c.1
                            have p24038_1 := h24038c.2.1
                            have p24038_2 := h24038c.2.2.1
                            have p24038_3 := h24038c.2.2.2
                            linarith only [hlam, p24038_0]
                          · have p24038_0 := h24038c.1
                            have p24038_1 := h24038c.2.1
                            have p24038_2 := h24038c.2.2.1
                            have p24038_3 := h24038c.2.2.2
                            linarith only [h24024, hlam, p24038_1]
                          · have p24038_0 := h24038c.1
                            have p24038_1 := h24038c.2.1
                            have p24038_2 := h24038c.2.2.1
                            have p24038_3 := h24038c.2.2.2
                            rcases p24038_3 (m.d 0 1) (by simp) with h24073 | h24073
                            · linarith only [h24073, hlam, p24038_0]
                            · rcases p24038_3 (m.d 1 2) (by simp) with h24075 | h24075
                              · rcases p24038_3 (m.d 1 3) (by simp) with h24076 | h24076
                                · rcases p24038_3 (m.d 1 4) (by simp) with h24077 | h24077
                                  · linarith only [h24024, h24077, hlam]
                                  · linarith only [h16563, h24077, hlam]
                                · linarith only [h14799, h24076, hlam]
                              · linarith only [h0, h24075, hlam]
                          · have p24038_0 := h24038c.1
                            have p24038_1 := h24038c.2.1
                            have p24038_2 := h24038c.2.2.1
                            have p24038_3 := h24038c.2.2.2
                            linarith only [h24021, hlam, p24038_1]
                          · have p24038_0 := h24038c.1
                            have p24038_1 := h24038c.2.1
                            have p24038_2 := h24038c.2.2.1
                            have p24038_3 := h24038c.2.2.2
                            linarith only [h24023, hlam, p24038_0]
                          · have p24038_0 := h24038c.1
                            have p24038_1 := h24038c.2.1
                            have p24038_2 := h24038c.2.2.1
                            have p24038_3 := h24038c.2.2.2
                            linarith only [h16563, hc01, hc15, hlam, hphi, p24038_1]
                          · have p24038_0 := h24038c.1
                            have p24038_1 := h24038c.2.1
                            have p24038_2 := h24038c.2.2.1
                            have p24038_3 := h24038c.2.2.2
                            linarith only [hlam, p24038_0]
                    · linarith only [h19110, h23667, h24033, hlam]
                  · linarith only [h19110, h23666, h24032, hlam]
              · linarith only [h14799, h19110, h23667, h24023, hc01, hc23, hlam, hphi, ht12]
            · linarith only [h19110, h23666, h24019, h24022, hlam]
          · linarith only [h0, h19110, h24019, h24021, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h19110, h24019, h24020, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h24092 | h24092
        · linarith only [h0, h22593, h24019, h24092, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h24094 | h24094
          · linarith only [h0, h23332, h24019, h24094, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h24096 | h24096
            · rcases m.htr 1 3 5 (by decide) (by decide) with h24097 | h24097
              · rcases m.htr 1 4 5 (by decide) (by decide) with h24098 | h24098
                · rcases m.htr 2 3 4 (by decide) (by decide) with h24099 | h24099
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h24100 | h24100
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h24101 | h24101
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h24102 | h24102
                        · linarith only [h23666, h23668, h24102, hlam]
                        · rcases h1bigk with h24104c | h24104c | h24104c | h24104c | h24104c | h24104c | h24104c | h24104c | h24104c | h24104c | h24104c | h24104c | h24104c | h24104c | h24104c | h24104c | h24104c | h24104c | h24104c | h24104c | h24104c | h24104c | h24104c | h24104c | h24104c
                          · have p24104_0 := h24104c.1
                            have p24104_1 := h24104c.2.1
                            have p24104_2 := h24104c.2.2.1
                            have p24104_3 := h24104c.2.2.2
                            linarith only [hlam, p24104_0]
                          · have p24104_0 := h24104c.1
                            have p24104_1 := h24104c.2.1
                            have p24104_2 := h24104c.2.2.1
                            have p24104_3 := h24104c.2.2.2
                            linarith only [h0, hlam, p24104_0]
                          · have p24104_0 := h24104c.1
                            have p24104_1 := h24104c.2.1
                            have p24104_2 := h24104c.2.2.1
                            have p24104_3 := h24104c.2.2.2
                            linarith only [h14799, hlam, p24104_0]
                          · have p24104_0 := h24104c.1
                            have p24104_1 := h24104c.2.1
                            have p24104_2 := h24104c.2.2.1
                            have p24104_3 := h24104c.2.2.2
                            linarith only [h16563, hlam, p24104_0]
                          · have p24104_0 := h24104c.1
                            have p24104_1 := h24104c.2.1
                            have p24104_2 := h24104c.2.2.1
                            have p24104_3 := h24104c.2.2.2
                            linarith only [h17994, hlam, p24104_0]
                          · have p24104_0 := h24104c.1
                            have p24104_1 := h24104c.2.1
                            have p24104_2 := h24104c.2.2.1
                            have p24104_3 := h24104c.2.2.2
                            linarith only [h24094, h24099, h24101, hc01, hc23, hlam, hphi, ht12, p24104_1]
                          · have p24104_0 := h24104c.1
                            have p24104_1 := h24104c.2.1
                            have p24104_2 := h24104c.2.2.1
                            have p24104_3 := h24104c.2.2.2
                            linarith only [hlam, p24104_0]
                          · have p24104_0 := h24104c.1
                            have p24104_1 := h24104c.2.1
                            have p24104_2 := h24104c.2.2.1
                            have p24104_3 := h24104c.2.2.2
                            linarith only [h24019, hlam, p24104_0]
                          · have p24104_0 := h24104c.1
                            have p24104_1 := h24104c.2.1
                            have p24104_2 := h24104c.2.2.1
                            have p24104_3 := h24104c.2.2.2
                            linarith only [h24092, hlam, p24104_0]
                          · have p24104_0 := h24104c.1
                            have p24104_1 := h24104c.2.1
                            have p24104_2 := h24104c.2.2.1
                            have p24104_3 := h24104c.2.2.2
                            linarith only [h24094, hlam, p24104_0]
                          · have p24104_0 := h24104c.1
                            have p24104_1 := h24104c.2.1
                            have p24104_2 := h24104c.2.2.1
                            have p24104_3 := h24104c.2.2.2
                            rcases p24104_3 (m.d 0 1) (by simp) with h24115 | h24115
                            · linarith only [h24115, hlam, p24104_0]
                            · rcases p24104_3 (m.d 1 2) (by simp) with h24117 | h24117
                              · linarith only [h24019, h24117, hlam]
                              · linarith only [h0, h24117, hlam]
                          · have p24104_0 := h24104c.1
                            have p24104_1 := h24104c.2.1
                            have p24104_2 := h24104c.2.2.1
                            have p24104_3 := h24104c.2.2.2
                            linarith only [h0, h24019, hc01, hc23, hlam, hphi, ht12, p24104_1]
                          · have p24104_0 := h24104c.1
                            have p24104_1 := h24104c.2.1
                            have p24104_2 := h24104c.2.2.1
                            have p24104_3 := h24104c.2.2.2
                            linarith only [hlam, p24104_0]
                          · have p24104_0 := h24104c.1
                            have p24104_1 := h24104c.2.1
                            have p24104_2 := h24104c.2.2.1
                            have p24104_3 := h24104c.2.2.2
                            linarith only [h23668, h24019, h24098, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p24104_1]
                          · have p24104_0 := h24104c.1
                            have p24104_1 := h24104c.2.1
                            have p24104_2 := h24104c.2.2.1
                            have p24104_3 := h24104c.2.2.2
                            linarith only [h17994, h24019, hc01, hc23, hlam, hphi, ht12, p24104_1]
                          · have p24104_0 := h24104c.1
                            have p24104_1 := h24104c.2.1
                            have p24104_2 := h24104c.2.2.1
                            have p24104_3 := h24104c.2.2.2
                            rcases p24104_3 (m.d 0 1) (by simp) with h24124 | h24124
                            · linarith only [h24124, hlam, p24104_0]
                            · rcases p24104_3 (m.d 1 2) (by simp) with h24126 | h24126
                              · linarith only [h24092, h24126, hlam]
                              · linarith only [h0, h24126, hlam]
                          · have p24104_0 := h24104c.1
                            have p24104_1 := h24104c.2.1
                            have p24104_2 := h24104c.2.2.1
                            have p24104_3 := h24104c.2.2.2
                            linarith only [h0, hc01, hc14, hlam, hphi, p24104_1]
                          · have p24104_0 := h24104c.1
                            have p24104_1 := h24104c.2.1
                            have p24104_2 := h24104c.2.2.1
                            have p24104_3 := h24104c.2.2.2
                            linarith only [h24096, hlam, p24104_0]
                          · have p24104_0 := h24104c.1
                            have p24104_1 := h24104c.2.1
                            have p24104_2 := h24104c.2.2.1
                            have p24104_3 := h24104c.2.2.2
                            linarith only [hlam, p24104_0]
                          · have p24104_0 := h24104c.1
                            have p24104_1 := h24104c.2.1
                            have p24104_2 := h24104c.2.2.1
                            have p24104_3 := h24104c.2.2.2
                            linarith only [h0, h22593, h23668, h24092, h24098, h24099, hc01, hc23, hlam, hphi, ht12, p24104_1]
                          · have p24104_0 := h24104c.1
                            have p24104_1 := h24104c.2.1
                            have p24104_2 := h24104c.2.2.1
                            have p24104_3 := h24104c.2.2.2
                            rcases p24104_3 (m.d 0 1) (by simp) with h24133 | h24133
                            · linarith only [h24133, hlam, p24104_0]
                            · rcases p24104_3 (m.d 1 2) (by simp) with h24135 | h24135
                              · linarith only [h24094, h24135, hlam]
                              · linarith only [h0, h24135, hlam]
                          · have p24104_0 := h24104c.1
                            have p24104_1 := h24104c.2.1
                            have p24104_2 := h24104c.2.2.1
                            have p24104_3 := h24104c.2.2.2
                            linarith only [h0, hc01, hc15, hlam, hphi, p24104_1]
                          · have p24104_0 := h24104c.1
                            have p24104_1 := h24104c.2.1
                            have p24104_2 := h24104c.2.2.1
                            have p24104_3 := h24104c.2.2.2
                            linarith only [h24097, hlam, p24104_0]
                          · have p24104_0 := h24104c.1
                            have p24104_1 := h24104c.2.1
                            have p24104_2 := h24104c.2.2.1
                            have p24104_3 := h24104c.2.2.2
                            linarith only [h24098, hlam, p24104_0]
                          · have p24104_0 := h24104c.1
                            have p24104_1 := h24104c.2.1
                            have p24104_2 := h24104c.2.2.1
                            have p24104_3 := h24104c.2.2.2
                            linarith only [hlam, p24104_0]
                      · linarith only [h0, h24092, h24101, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h14799, h23667, h23668, h24019, h24098, h24100, hc01, hc14, hlam, hphi]
                  · linarith only [h23666, h23668, h24019, h24096, h24098, h24099, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h24145 | h24145
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h24146 | h24146
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h24147 | h24147
                      · linarith only [h0, h24092, h24098, h24145, h24147, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h24092, h24147, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h14799, h19110, h23667, h24146, hc01, hc13, hlam, hphi]
                  · linarith only [h14799, h23666, h24019, h24145, hlam]
              · linarith only [h14799, h23667, h24097, hlam]
            · linarith only [h14799, h23666, h24096, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h24154 | h24154
    · linarith only [h23666, h23667, h24154, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h24156 | h24156
      · rcases m.htr 1 2 4 (by decide) (by decide) with h24157 | h24157
        · rcases m.htr 1 2 5 (by decide) (by decide) with h24158 | h24158
          · rcases m.htr 1 3 4 (by decide) (by decide) with h24159 | h24159
            · rcases m.htr 1 3 5 (by decide) (by decide) with h24160 | h24160
              · rcases m.htr 1 4 5 (by decide) (by decide) with h24161 | h24161
                · rcases m.htr 2 3 4 (by decide) (by decide) with h24162 | h24162
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h24163 | h24163
                    · linarith only [h23666, h23667, h24156, h24163, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h19110, h24160, h24163, hc01, hc13, hlam, hphi]
                  · linarith only [h0, h14799, h19110, h23666, h24156, h24162, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h24167 | h24167
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h24168 | h24168
                    · linarith only [h23666, h23667, h24156, h24168, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h19110, h24156, h24160, h24168, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h14799, h19110, h23666, h24156, h24167, hc01, hc12, hlam, hphi]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h24172 | h24172
                · linarith only [h16563, h24154, h24159, h24160, h24172, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h24174 | h24174
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h24175 | h24175
                    · linarith only [h24156, h24160, h24175, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h24177 | h24177
                      · linarith only [h16563, h24172, h24177, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h24179 | h24179
                        · linarith only [h17994, h23666, h23667, h24172, h24179, hlam]
                        · rcases h1bigk with h24181c | h24181c | h24181c | h24181c | h24181c | h24181c | h24181c | h24181c | h24181c | h24181c | h24181c | h24181c | h24181c | h24181c | h24181c | h24181c | h24181c | h24181c | h24181c | h24181c | h24181c | h24181c | h24181c | h24181c | h24181c
                          · have p24181_0 := h24181c.1
                            have p24181_1 := h24181c.2.1
                            have p24181_2 := h24181c.2.2.1
                            have p24181_3 := h24181c.2.2.2
                            linarith only [hlam, p24181_0]
                          · have p24181_0 := h24181c.1
                            have p24181_1 := h24181c.2.1
                            have p24181_2 := h24181c.2.2.1
                            have p24181_3 := h24181c.2.2.2
                            linarith only [h0, hlam, p24181_0]
                          · have p24181_0 := h24181c.1
                            have p24181_1 := h24181c.2.1
                            have p24181_2 := h24181c.2.2.1
                            have p24181_3 := h24181c.2.2.2
                            linarith only [h14799, hlam, p24181_0]
                          · have p24181_0 := h24181c.1
                            have p24181_1 := h24181c.2.1
                            have p24181_2 := h24181c.2.2.1
                            have p24181_3 := h24181c.2.2.2
                            linarith only [h16563, hlam, p24181_0]
                          · have p24181_0 := h24181c.1
                            have p24181_1 := h24181c.2.1
                            have p24181_2 := h24181c.2.2.1
                            have p24181_3 := h24181c.2.2.2
                            linarith only [h17994, hlam, p24181_0]
                          · have p24181_0 := h24181c.1
                            have p24181_1 := h24181c.2.1
                            have p24181_2 := h24181c.2.2.1
                            have p24181_3 := h24181c.2.2.2
                            rcases p24181_3 (m.d 0 1) (by simp) with h24187 | h24187
                            · linarith only [h24187, hlam, p24181_0]
                            · rcases p24181_3 (m.d 1 2) (by simp) with h24189 | h24189
                              · rcases p24181_3 (m.d 1 3) (by simp) with h24190 | h24190
                                · linarith only [h24156, h24190, hlam]
                                · linarith only [h14799, h24190, hlam]
                              · linarith only [h24189, hlam, p24181_0]
                          · have p24181_0 := h24181c.1
                            have p24181_1 := h24181c.2.1
                            have p24181_2 := h24181c.2.2.1
                            have p24181_3 := h24181c.2.2.2
                            linarith only [hlam, p24181_0]
                          · have p24181_0 := h24181c.1
                            have p24181_1 := h24181c.2.1
                            have p24181_2 := h24181c.2.2.1
                            have p24181_3 := h24181c.2.2.2
                            linarith only [h14799, hc01, hc12, hlam, hphi, p24181_1]
                          · have p24181_0 := h24181c.1
                            have p24181_1 := h24181c.2.1
                            have p24181_2 := h24181c.2.2.1
                            have p24181_3 := h24181c.2.2.2
                            linarith only [h16563, hc01, hc12, hlam, hphi, p24181_1]
                          · have p24181_0 := h24181c.1
                            have p24181_1 := h24181c.2.1
                            have p24181_2 := h24181c.2.2.1
                            have p24181_3 := h24181c.2.2.2
                            linarith only [h17994, hc01, hc12, hlam, hphi, p24181_1]
                          · have p24181_0 := h24181c.1
                            have p24181_1 := h24181c.2.1
                            have p24181_2 := h24181c.2.2.1
                            have p24181_3 := h24181c.2.2.2
                            linarith only [h24160, h24179, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p24181_1]
                          · have p24181_0 := h24181c.1
                            have p24181_1 := h24181c.2.1
                            have p24181_2 := h24181c.2.2.1
                            have p24181_3 := h24181c.2.2.2
                            linarith only [h24156, hlam, p24181_1]
                          · have p24181_0 := h24181c.1
                            have p24181_1 := h24181c.2.1
                            have p24181_2 := h24181c.2.2.1
                            have p24181_3 := h24181c.2.2.2
                            linarith only [hlam, p24181_0]
                          · have p24181_0 := h24181c.1
                            have p24181_1 := h24181c.2.1
                            have p24181_2 := h24181c.2.2.1
                            have p24181_3 := h24181c.2.2.2
                            linarith only [h0, h22593, h24157, h24160, h24179, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p24181_1]
                          · have p24181_0 := h24181c.1
                            have p24181_1 := h24181c.2.1
                            have p24181_2 := h24181c.2.2.1
                            have p24181_3 := h24181c.2.2.2
                            linarith only [h24160, hlam, p24181_1]
                          · have p24181_0 := h24181c.1
                            have p24181_1 := h24181c.2.1
                            have p24181_2 := h24181c.2.2.1
                            have p24181_3 := h24181c.2.2.2
                            linarith only [h24159, h24160, h24179, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p24181_1]
                          · have p24181_0 := h24181c.1
                            have p24181_1 := h24181c.2.1
                            have p24181_2 := h24181c.2.2.1
                            have p24181_3 := h24181c.2.2.2
                            linarith only [h24157, hlam, p24181_1]
                          · have p24181_0 := h24181c.1
                            have p24181_1 := h24181c.2.1
                            have p24181_2 := h24181c.2.2.1
                            have p24181_3 := h24181c.2.2.2
                            linarith only [h24159, hlam, p24181_0]
                          · have p24181_0 := h24181c.1
                            have p24181_1 := h24181c.2.1
                            have p24181_2 := h24181c.2.2.1
                            have p24181_3 := h24181c.2.2.2
                            linarith only [hlam, p24181_0]
                          · have p24181_0 := h24181c.1
                            have p24181_1 := h24181c.2.1
                            have p24181_2 := h24181c.2.2.1
                            have p24181_3 := h24181c.2.2.2
                            linarith only [h24172, hlam, p24181_1]
                          · have p24181_0 := h24181c.1
                            have p24181_1 := h24181c.2.1
                            have p24181_2 := h24181c.2.2.1
                            have p24181_3 := h24181c.2.2.2
                            rcases p24181_3 (m.d 0 1) (by simp) with h24208 | h24208
                            · linarith only [h24208, hlam, p24181_0]
                            · rcases p24181_3 (m.d 1 2) (by simp) with h24210 | h24210
                              · rcases p24181_3 (m.d 1 3) (by simp) with h24211 | h24211
                                · linarith only [h24160, h24211, hlam]
                                · linarith only [h14799, h24211, hlam]
                              · linarith only [h0, h24210, hlam]
                          · have p24181_0 := h24181c.1
                            have p24181_1 := h24181c.2.1
                            have p24181_2 := h24181c.2.2.1
                            have p24181_3 := h24181c.2.2.2
                            linarith only [h24158, hlam, p24181_1]
                          · have p24181_0 := h24181c.1
                            have p24181_1 := h24181c.2.1
                            have p24181_2 := h24181c.2.2.1
                            have p24181_3 := h24181c.2.2.2
                            linarith only [h14799, hc01, hc15, hlam, hphi, p24181_1]
                          · have p24181_0 := h24181c.1
                            have p24181_1 := h24181c.2.1
                            have p24181_2 := h24181c.2.2.1
                            have p24181_3 := h24181c.2.2.2
                            linarith only [h16563, h24160, h24179, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p24181_1]
                          · have p24181_0 := h24181c.1
                            have p24181_1 := h24181c.2.1
                            have p24181_2 := h24181c.2.2.1
                            have p24181_3 := h24181c.2.2.2
                            linarith only [hlam, p24181_0]
                  · linarith only [h0, h14799, h19110, h23666, h24174, hc01, hc13, hlam, hphi]
            · linarith only [h23666, h23667, h24159, hc13, hc35, hlam, hphi]
          · linarith only [h0, h19110, h24156, h24158, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h19110, h24156, h24157, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h24223 | h24223
        · linarith only [h0, h22593, h24156, h24223, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h24225 | h24225
          · linarith only [h0, h23332, h24156, h24225, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h24227 | h24227
            · rcases m.htr 1 3 5 (by decide) (by decide) with h24228 | h24228
              · rcases m.htr 1 4 5 (by decide) (by decide) with h24229 | h24229
                · rcases m.htr 2 3 4 (by decide) (by decide) with h24230 | h24230
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h24231 | h24231
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h24232 | h24232
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h24233 | h24233
                        · linarith only [h0, h22593, h23666, h23667, h24154, h24156, h24228, h24233, hc01, hc23, hlam, hphi, ht12]
                        · rcases h1bigk with h24235c | h24235c | h24235c | h24235c | h24235c | h24235c | h24235c | h24235c | h24235c | h24235c | h24235c | h24235c | h24235c | h24235c | h24235c | h24235c | h24235c | h24235c | h24235c | h24235c | h24235c | h24235c | h24235c | h24235c | h24235c
                          · have p24235_0 := h24235c.1
                            have p24235_1 := h24235c.2.1
                            have p24235_2 := h24235c.2.2.1
                            have p24235_3 := h24235c.2.2.2
                            linarith only [hlam, p24235_0]
                          · have p24235_0 := h24235c.1
                            have p24235_1 := h24235c.2.1
                            have p24235_2 := h24235c.2.2.1
                            have p24235_3 := h24235c.2.2.2
                            linarith only [h0, hlam, p24235_0]
                          · have p24235_0 := h24235c.1
                            have p24235_1 := h24235c.2.1
                            have p24235_2 := h24235c.2.2.1
                            have p24235_3 := h24235c.2.2.2
                            linarith only [h14799, hlam, p24235_0]
                          · have p24235_0 := h24235c.1
                            have p24235_1 := h24235c.2.1
                            have p24235_2 := h24235c.2.2.1
                            have p24235_3 := h24235c.2.2.2
                            linarith only [h16563, hlam, p24235_0]
                          · have p24235_0 := h24235c.1
                            have p24235_1 := h24235c.2.1
                            have p24235_2 := h24235c.2.2.1
                            have p24235_3 := h24235c.2.2.2
                            linarith only [h17994, hlam, p24235_0]
                          · have p24235_0 := h24235c.1
                            have p24235_1 := h24235c.2.1
                            have p24235_2 := h24235c.2.2.1
                            have p24235_3 := h24235c.2.2.2
                            linarith only [h24225, h24230, h24232, hc01, hc23, hlam, hphi, ht12, p24235_1]
                          · have p24235_0 := h24235c.1
                            have p24235_1 := h24235c.2.1
                            have p24235_2 := h24235c.2.2.1
                            have p24235_3 := h24235c.2.2.2
                            linarith only [hlam, p24235_0]
                          · have p24235_0 := h24235c.1
                            have p24235_1 := h24235c.2.1
                            have p24235_2 := h24235c.2.2.1
                            have p24235_3 := h24235c.2.2.2
                            linarith only [h24156, hlam, p24235_0]
                          · have p24235_0 := h24235c.1
                            have p24235_1 := h24235c.2.1
                            have p24235_2 := h24235c.2.2.1
                            have p24235_3 := h24235c.2.2.2
                            linarith only [h24223, hlam, p24235_0]
                          · have p24235_0 := h24235c.1
                            have p24235_1 := h24235c.2.1
                            have p24235_2 := h24235c.2.2.1
                            have p24235_3 := h24235c.2.2.2
                            linarith only [h24225, hlam, p24235_0]
                          · have p24235_0 := h24235c.1
                            have p24235_1 := h24235c.2.1
                            have p24235_2 := h24235c.2.2.1
                            have p24235_3 := h24235c.2.2.2
                            rcases p24235_3 (m.d 0 1) (by simp) with h24246 | h24246
                            · linarith only [h24246, hlam, p24235_0]
                            · rcases p24235_3 (m.d 1 2) (by simp) with h24248 | h24248
                              · linarith only [h24156, h24248, hlam]
                              · linarith only [h0, h24248, hlam]
                          · have p24235_0 := h24235c.1
                            have p24235_1 := h24235c.2.1
                            have p24235_2 := h24235c.2.2.1
                            have p24235_3 := h24235c.2.2.2
                            linarith only [h0, h24156, hc01, hc23, hlam, hphi, ht12, p24235_1]
                          · have p24235_0 := h24235c.1
                            have p24235_1 := h24235c.2.1
                            have p24235_2 := h24235c.2.2.1
                            have p24235_3 := h24235c.2.2.2
                            linarith only [hlam, p24235_0]
                          · have p24235_0 := h24235c.1
                            have p24235_1 := h24235c.2.1
                            have p24235_2 := h24235c.2.2.1
                            have p24235_3 := h24235c.2.2.2
                            linarith only [h23666, h23667, h24156, h24229, h24233, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p24235_1]
                          · have p24235_0 := h24235c.1
                            have p24235_1 := h24235c.2.1
                            have p24235_2 := h24235c.2.2.1
                            have p24235_3 := h24235c.2.2.2
                            linarith only [h17994, h24156, hc01, hc23, hlam, hphi, ht12, p24235_1]
                          · have p24235_0 := h24235c.1
                            have p24235_1 := h24235c.2.1
                            have p24235_2 := h24235c.2.2.1
                            have p24235_3 := h24235c.2.2.2
                            rcases p24235_3 (m.d 0 1) (by simp) with h24255 | h24255
                            · linarith only [h24255, hlam, p24235_0]
                            · rcases p24235_3 (m.d 1 2) (by simp) with h24257 | h24257
                              · linarith only [h24223, h24257, hlam]
                              · linarith only [h0, h24257, hlam]
                          · have p24235_0 := h24235c.1
                            have p24235_1 := h24235c.2.1
                            have p24235_2 := h24235c.2.2.1
                            have p24235_3 := h24235c.2.2.2
                            linarith only [h0, hc01, hc14, hlam, hphi, p24235_1]
                          · have p24235_0 := h24235c.1
                            have p24235_1 := h24235c.2.1
                            have p24235_2 := h24235c.2.2.1
                            have p24235_3 := h24235c.2.2.2
                            linarith only [h24227, hlam, p24235_0]
                          · have p24235_0 := h24235c.1
                            have p24235_1 := h24235c.2.1
                            have p24235_2 := h24235c.2.2.1
                            have p24235_3 := h24235c.2.2.2
                            linarith only [hlam, p24235_0]
                          · have p24235_0 := h24235c.1
                            have p24235_1 := h24235c.2.1
                            have p24235_2 := h24235c.2.2.1
                            have p24235_3 := h24235c.2.2.2
                            linarith only [h23666, h23667, h24223, h24229, h24230, h24233, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p24235_1]
                          · have p24235_0 := h24235c.1
                            have p24235_1 := h24235c.2.1
                            have p24235_2 := h24235c.2.2.1
                            have p24235_3 := h24235c.2.2.2
                            rcases p24235_3 (m.d 0 1) (by simp) with h24264 | h24264
                            · linarith only [h24264, hlam, p24235_0]
                            · rcases p24235_3 (m.d 1 2) (by simp) with h24266 | h24266
                              · linarith only [h24225, h24266, hlam]
                              · linarith only [h0, h24266, hlam]
                          · have p24235_0 := h24235c.1
                            have p24235_1 := h24235c.2.1
                            have p24235_2 := h24235c.2.2.1
                            have p24235_3 := h24235c.2.2.2
                            linarith only [h0, hc01, hc15, hlam, hphi, p24235_1]
                          · have p24235_0 := h24235c.1
                            have p24235_1 := h24235c.2.1
                            have p24235_2 := h24235c.2.2.1
                            have p24235_3 := h24235c.2.2.2
                            linarith only [h24228, hlam, p24235_0]
                          · have p24235_0 := h24235c.1
                            have p24235_1 := h24235c.2.1
                            have p24235_2 := h24235c.2.2.1
                            have p24235_3 := h24235c.2.2.2
                            linarith only [h24229, hlam, p24235_0]
                          · have p24235_0 := h24235c.1
                            have p24235_1 := h24235c.2.1
                            have p24235_2 := h24235c.2.2.1
                            have p24235_3 := h24235c.2.2.2
                            linarith only [hlam, p24235_0]
                      · linarith only [h0, h24223, h24232, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h24156, h24231, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h23666, h23667, h24156, h24228, h24230, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h24276 | h24276
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h24277 | h24277
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h24278 | h24278
                      · linarith only [h16563, h24229, h24278, hc01, hc24, hlam, hphi, ht12]
                      · linarith only [h0, h24223, h24278, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h24156, h24228, h24277, hlam]
                  · linarith only [h23666, h23667, h24156, h24228, h24276, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h24283 | h24283
                · linarith only [h0, h22593, h24154, h24227, h24228, h24283, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h24285 | h24285
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h24286 | h24286
                    · linarith only [h14799, h24228, h24286, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h24156, h24286, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h23666, h24156, h24285, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
            · linarith only [h14799, h23666, h24227, hlam]

end R2N4
