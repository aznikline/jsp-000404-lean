import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S27
import Jsp000404.R1LeavesN7_0S28

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5618000 in
set_option maxHeartbeats 5618000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x1_x1_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (hg14159 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14160 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h15885 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h15893 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h15899 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h15901 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h15903 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have h14159 := hg14159
  rcases m.htr 2 3 4 (by decide) (by decide) with h16708 | h16708
  · linarith only [h16708, h4, h7, hlam]
  · rcases m.htr 2 3 5 (by decide) (by decide) with h16710 | h16710
    · linarith only [h13284, h16710, h4, hlam]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h16712 | h16712
      · rcases m.htr 3 4 5 (by decide) (by decide) with h16713 | h16713
        · rcases h1bigk with h16714c | h16714c | h16714c | h16714c | h16714c | h16714c | h16714c | h16714c | h16714c | h16714c | h16714c | h16714c | h16714c | h16714c | h16714c | h16714c | h16714c | h16714c | h16714c | h16714c | h16714c | h16714c | h16714c | h16714c | h16714c
          · have p16714_0 := h16714c.1
            have p16714_1 := h16714c.2.1
            have p16714_2 := h16714c.2.2.1
            have p16714_3 := h16714c.2.2.2
            linarith only [hlam, p16714_0]
          · have p16714_0 := h16714c.1
            have p16714_1 := h16714c.2.1
            have p16714_2 := h16714c.2.2.1
            have p16714_3 := h16714c.2.2.2
            linarith only [h0, h14160, h15899, h15903, h16712, h5, hlam, p16714_2]
          · have p16714_0 := h16714c.1
            have p16714_1 := h16714c.2.1
            have p16714_2 := h16714c.2.2.1
            have p16714_3 := h16714c.2.2.2
            linarith only [h0, h15899, h15903, h16712, h5, hlam, p16714_2]
          · have p16714_0 := h16714c.1
            have p16714_1 := h16714c.2.1
            have p16714_2 := h16714c.2.2.1
            have p16714_3 := h16714c.2.2.2
            linarith only [h0, h15903, h16712, h5, hlam, p16714_2]
          · have p16714_0 := h16714c.1
            have p16714_1 := h16714c.2.1
            have p16714_2 := h16714c.2.2.1
            have p16714_3 := h16714c.2.2.2
            rcases p16714_3 (m.d 0 1) (by simp) with h16719 | h16719
            · rcases p16714_3 (m.d 1 2) (by simp) with h16720 | h16720
              · linarith only [h0, h16720, hlam]
              · rcases p16714_3 (m.d 1 3) (by simp) with h16722 | h16722
                · linarith only [h1, h16722, hlam]
                · rcases p16714_3 (m.d 1 4) (by simp) with h16724 | h16724
                  · linarith only [h16724, h2, hlam]
                  · rcases p16714_3 (m.d 1 5) (by simp) with h16726 | h16726
                    · linarith only [h16726, hlam, p16714_0]
                    · rcases h1emax with h16728 | h16728 | h16728 | h16728 | h16728
                      · linarith only [h0, h14160, h15899, h15903, h16712, h16728, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases h2bigk with h16730c | h16730c | h16730c | h16730c | h16730c | h16730c | h16730c | h16730c | h16730c | h16730c | h16730c | h16730c | h16730c | h16730c | h16730c | h16730c | h16730c | h16730c | h16730c | h16730c | h16730c | h16730c | h16730c | h16730c | h16730c
                        · have p16730_0 := h16730c.1
                          have p16730_1 := h16730c.2.1
                          have p16730_2 := h16730c.2.2.1
                          have p16730_3 := h16730c.2.2.2
                          linarith only [hlam, p16730_0]
                        · have p16730_0 := h16730c.1
                          have p16730_1 := h16730c.2.1
                          have p16730_2 := h16730c.2.2.1
                          have p16730_3 := h16730c.2.2.2
                          linarith only [h14160, h15899, h15903, h16712, h5, hlam, p16730_2]
                        · have p16730_0 := h16730c.1
                          have p16730_1 := h16730c.2.1
                          have p16730_2 := h16730c.2.2.1
                          have p16730_3 := h16730c.2.2.2
                          rcases p16730_3 (m.d 0 2) (by simp) with h16733 | h16733
                          · rcases p16730_3 (m.d 1 2) (by simp) with h16734 | h16734
                            · linarith only [h0, h16734, hlam]
                            · rcases p16730_3 (m.d 2 3) (by simp) with h16736 | h16736
                              · linarith only [h16736, hlam, p16730_0]
                              · rcases p16730_3 (m.d 2 4) (by simp) with h16738 | h16738
                                · linarith only [h16738, h5, hlam]
                                · linarith only [h16708, h16738, hlam]
                          · linarith only [h16733, hlam, p16730_0]
                        · have p16730_0 := h16730c.1
                          have p16730_1 := h16730c.2.1
                          have p16730_2 := h16730c.2.2.1
                          have p16730_3 := h16730c.2.2.2
                          linarith only [h0, h14160, h15899, h15903, h16712, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p16730_1]
                        · have p16730_0 := h16730c.1
                          have p16730_1 := h16730c.2.1
                          have p16730_2 := h16730c.2.2.1
                          have p16730_3 := h16730c.2.2.2
                          rcases p16730_3 (m.d 0 2) (by simp) with h16743 | h16743
                          · rcases p16730_3 (m.d 1 2) (by simp) with h16744 | h16744
                            · linarith only [h0, h16744, hlam]
                            · rcases p16730_3 (m.d 2 3) (by simp) with h16746 | h16746
                              · linarith only [h16746, h4, hlam]
                              · rcases p16730_3 (m.d 2 4) (by simp) with h16748 | h16748
                                · linarith only [h16748, h5, hlam]
                                · linarith only [h16712, h16748, hlam]
                          · linarith only [h16743, hlam, p16730_0]
                        · have p16730_0 := h16730c.1
                          have p16730_1 := h16730c.2.1
                          have p16730_2 := h16730c.2.2.1
                          have p16730_3 := h16730c.2.2.2
                          linarith only [h0, hlam, p16730_1]
                        · have p16730_0 := h16730c.1
                          have p16730_1 := h16730c.2.1
                          have p16730_2 := h16730c.2.2.1
                          have p16730_3 := h16730c.2.2.2
                          linarith only [hlam, p16730_0]
                        · have p16730_0 := h16730c.1
                          have p16730_1 := h16730c.2.1
                          have p16730_2 := h16730c.2.2.1
                          have p16730_3 := h16730c.2.2.2
                          linarith only [h14160, hlam, p16730_0]
                        · have p16730_0 := h16730c.1
                          have p16730_1 := h16730c.2.1
                          have p16730_2 := h16730c.2.2.1
                          have p16730_3 := h16730c.2.2.2
                          linarith only [h15885, hlam, p16730_0]
                        · have p16730_0 := h16730c.1
                          have p16730_1 := h16730c.2.1
                          have p16730_2 := h16730c.2.2.1
                          have p16730_3 := h16730c.2.2.2
                          linarith only [h15893, hlam, p16730_0]
                        · have p16730_0 := h16730c.1
                          have p16730_1 := h16730c.2.1
                          have p16730_2 := h16730c.2.2.1
                          have p16730_3 := h16730c.2.2.2
                          linarith only [h4, hlam, p16730_0]
                        · have p16730_0 := h16730c.1
                          have p16730_1 := h16730c.2.1
                          have p16730_2 := h16730c.2.2.1
                          have p16730_3 := h16730c.2.2.2
                          linarith only [h13284, h4, hc12, hc35, hlam, hphi, ht23, p16730_1]
                        · have p16730_0 := h16730c.1
                          have p16730_1 := h16730c.2.1
                          have p16730_2 := h16730c.2.2.1
                          have p16730_3 := h16730c.2.2.2
                          linarith only [hlam, p16730_0]
                        · have p16730_0 := h16730c.1
                          have p16730_1 := h16730c.2.1
                          have p16730_2 := h16730c.2.2.1
                          have p16730_3 := h16730c.2.2.2
                          linarith only [h16708, hlam, p16730_1]
                        · have p16730_0 := h16730c.1
                          have p16730_1 := h16730c.2.1
                          have p16730_2 := h16730c.2.2.1
                          have p16730_3 := h16730c.2.2.2
                          linarith only [h16710, hlam, p16730_1]
                        · have p16730_0 := h16730c.1
                          have p16730_1 := h16730c.2.1
                          have p16730_2 := h16730c.2.2.1
                          have p16730_3 := h16730c.2.2.2
                          linarith only [h5, hlam, p16730_0]
                        · have p16730_0 := h16730c.1
                          have p16730_1 := h16730c.2.1
                          have p16730_2 := h16730c.2.2.1
                          have p16730_3 := h16730c.2.2.2
                          rcases p16730_3 (m.d 0 2) (by simp) with h16763 | h16763
                          · rcases p16730_3 (m.d 1 2) (by simp) with h16764 | h16764
                            · linarith only [h16764, hlam, p16730_0]
                            · rcases p16730_3 (m.d 2 3) (by simp) with h16766 | h16766
                              · linarith only [h16708, h16766, hlam]
                              · linarith only [h14160, h16766, hlam]
                          · linarith only [h0, h16763, hlam]
                        · have p16730_0 := h16730c.1
                          have p16730_1 := h16730c.2.1
                          have p16730_2 := h16730c.2.2.1
                          have p16730_3 := h16730c.2.2.2
                          linarith only [h0, h14160, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p16730_1]
                        · have p16730_0 := h16730c.1
                          have p16730_1 := h16730c.2.1
                          have p16730_2 := h16730c.2.2.1
                          have p16730_3 := h16730c.2.2.2
                          linarith only [hlam, p16730_0]
                        · have p16730_0 := h16730c.1
                          have p16730_1 := h16730c.2.1
                          have p16730_2 := h16730c.2.2.1
                          have p16730_3 := h16730c.2.2.2
                          linarith only [h0, h14160, h16710, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p16730_1]
                        · have p16730_0 := h16730c.1
                          have p16730_1 := h16730c.2.1
                          have p16730_2 := h16730c.2.2.1
                          have p16730_3 := h16730c.2.2.2
                          linarith only [h6, hlam, p16730_0]
                        · have p16730_0 := h16730c.1
                          have p16730_1 := h16730c.2.1
                          have p16730_2 := h16730c.2.2.1
                          have p16730_3 := h16730c.2.2.2
                          rcases p16730_3 (m.d 0 2) (by simp) with h16774 | h16774
                          · rcases p16730_3 (m.d 1 2) (by simp) with h16775 | h16775
                            · linarith only [h16775, hlam, p16730_0]
                            · rcases p16730_3 (m.d 2 3) (by simp) with h16777 | h16777
                              · linarith only [h16710, h16777, hlam]
                              · linarith only [h14160, h16777, hlam]
                          · linarith only [h0, h16774, hlam]
                        · have p16730_0 := h16730c.1
                          have p16730_1 := h16730c.2.1
                          have p16730_2 := h16730c.2.2.1
                          have p16730_3 := h16730c.2.2.2
                          linarith only [h14160, hc12, hc25, hlam, hphi, p16730_1]
                        · have p16730_0 := h16730c.1
                          have p16730_1 := h16730c.2.1
                          have p16730_2 := h16730c.2.2.1
                          have p16730_3 := h16730c.2.2.2
                          linarith only [h16712, hlam, p16730_1]
                        · have p16730_0 := h16730c.1
                          have p16730_1 := h16730c.2.1
                          have p16730_2 := h16730c.2.2.1
                          have p16730_3 := h16730c.2.2.2
                          linarith only [hlam, p16730_0]
                      · rcases h2bigk with h16784c | h16784c | h16784c | h16784c | h16784c | h16784c | h16784c | h16784c | h16784c | h16784c | h16784c | h16784c | h16784c | h16784c | h16784c | h16784c | h16784c | h16784c | h16784c | h16784c | h16784c | h16784c | h16784c | h16784c | h16784c
                        · have p16784_0 := h16784c.1
                          have p16784_1 := h16784c.2.1
                          have p16784_2 := h16784c.2.2.1
                          have p16784_3 := h16784c.2.2.2
                          linarith only [hlam, p16784_0]
                        · have p16784_0 := h16784c.1
                          have p16784_1 := h16784c.2.1
                          have p16784_2 := h16784c.2.2.1
                          have p16784_3 := h16784c.2.2.2
                          linarith only [h14160, h15899, h15903, h16712, h5, hlam, p16784_2]
                        · have p16784_0 := h16784c.1
                          have p16784_1 := h16784c.2.1
                          have p16784_2 := h16784c.2.2.1
                          have p16784_3 := h16784c.2.2.2
                          rcases p16784_3 (m.d 0 2) (by simp) with h16787 | h16787
                          · rcases p16784_3 (m.d 1 2) (by simp) with h16788 | h16788
                            · linarith only [h0, h16788, hlam]
                            · rcases p16784_3 (m.d 2 3) (by simp) with h16790 | h16790
                              · linarith only [h16790, hlam, p16784_0]
                              · rcases p16784_3 (m.d 2 4) (by simp) with h16792 | h16792
                                · linarith only [h16792, h5, hlam]
                                · linarith only [h16708, h16792, hlam]
                          · linarith only [h16787, hlam, p16784_0]
                        · have p16784_0 := h16784c.1
                          have p16784_1 := h16784c.2.1
                          have p16784_2 := h16784c.2.2.1
                          have p16784_3 := h16784c.2.2.2
                          linarith only [h14160, h15899, h15903, h16712, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p16784_1]
                        · have p16784_0 := h16784c.1
                          have p16784_1 := h16784c.2.1
                          have p16784_2 := h16784c.2.2.1
                          have p16784_3 := h16784c.2.2.2
                          rcases p16784_3 (m.d 0 2) (by simp) with h16797 | h16797
                          · rcases p16784_3 (m.d 1 2) (by simp) with h16798 | h16798
                            · linarith only [h0, h16798, hlam]
                            · rcases p16784_3 (m.d 2 3) (by simp) with h16800 | h16800
                              · linarith only [h16800, h4, hlam]
                              · rcases p16784_3 (m.d 2 4) (by simp) with h16802 | h16802
                                · linarith only [h16802, h5, hlam]
                                · linarith only [h16712, h16802, hlam]
                          · linarith only [h16797, hlam, p16784_0]
                        · have p16784_0 := h16784c.1
                          have p16784_1 := h16784c.2.1
                          have p16784_2 := h16784c.2.2.1
                          have p16784_3 := h16784c.2.2.2
                          linarith only [h0, hlam, p16784_1]
                        · have p16784_0 := h16784c.1
                          have p16784_1 := h16784c.2.1
                          have p16784_2 := h16784c.2.2.1
                          have p16784_3 := h16784c.2.2.2
                          linarith only [hlam, p16784_0]
                        · have p16784_0 := h16784c.1
                          have p16784_1 := h16784c.2.1
                          have p16784_2 := h16784c.2.2.1
                          have p16784_3 := h16784c.2.2.2
                          linarith only [h14160, hlam, p16784_0]
                        · have p16784_0 := h16784c.1
                          have p16784_1 := h16784c.2.1
                          have p16784_2 := h16784c.2.2.1
                          have p16784_3 := h16784c.2.2.2
                          linarith only [h15885, hlam, p16784_0]
                        · have p16784_0 := h16784c.1
                          have p16784_1 := h16784c.2.1
                          have p16784_2 := h16784c.2.2.1
                          have p16784_3 := h16784c.2.2.2
                          linarith only [h15893, hlam, p16784_0]
                        · have p16784_0 := h16784c.1
                          have p16784_1 := h16784c.2.1
                          have p16784_2 := h16784c.2.2.1
                          have p16784_3 := h16784c.2.2.2
                          linarith only [h4, hlam, p16784_0]
                        · have p16784_0 := h16784c.1
                          have p16784_1 := h16784c.2.1
                          have p16784_2 := h16784c.2.2.1
                          have p16784_3 := h16784c.2.2.2
                          linarith only [h13284, h16713, h4, hc12, hc34, hlam, hphi, ht23, p16784_1]
                        · have p16784_0 := h16784c.1
                          have p16784_1 := h16784c.2.1
                          have p16784_2 := h16784c.2.2.1
                          have p16784_3 := h16784c.2.2.2
                          linarith only [hlam, p16784_0]
                        · have p16784_0 := h16784c.1
                          have p16784_1 := h16784c.2.1
                          have p16784_2 := h16784c.2.2.1
                          have p16784_3 := h16784c.2.2.2
                          linarith only [h16708, hlam, p16784_1]
                        · have p16784_0 := h16784c.1
                          have p16784_1 := h16784c.2.1
                          have p16784_2 := h16784c.2.2.1
                          have p16784_3 := h16784c.2.2.2
                          linarith only [h16710, hlam, p16784_1]
                        · have p16784_0 := h16784c.1
                          have p16784_1 := h16784c.2.1
                          have p16784_2 := h16784c.2.2.1
                          have p16784_3 := h16784c.2.2.2
                          linarith only [h5, hlam, p16784_0]
                        · have p16784_0 := h16784c.1
                          have p16784_1 := h16784c.2.1
                          have p16784_2 := h16784c.2.2.1
                          have p16784_3 := h16784c.2.2.2
                          rcases p16784_3 (m.d 0 2) (by simp) with h16817 | h16817
                          · rcases p16784_3 (m.d 1 2) (by simp) with h16818 | h16818
                            · linarith only [h16818, hlam, p16784_0]
                            · rcases p16784_3 (m.d 2 3) (by simp) with h16820 | h16820
                              · linarith only [h16708, h16820, hlam]
                              · linarith only [h14160, h16820, hlam]
                          · linarith only [h0, h16817, hlam]
                        · have p16784_0 := h16784c.1
                          have p16784_1 := h16784c.2.1
                          have p16784_2 := h16784c.2.2.1
                          have p16784_3 := h16784c.2.2.2
                          linarith only [h0, h14160, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p16784_1]
                        · have p16784_0 := h16784c.1
                          have p16784_1 := h16784c.2.1
                          have p16784_2 := h16784c.2.2.1
                          have p16784_3 := h16784c.2.2.2
                          linarith only [hlam, p16784_0]
                        · have p16784_0 := h16784c.1
                          have p16784_1 := h16784c.2.1
                          have p16784_2 := h16784c.2.2.1
                          have p16784_3 := h16784c.2.2.2
                          linarith only [h0, h14160, h16710, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p16784_1]
                        · have p16784_0 := h16784c.1
                          have p16784_1 := h16784c.2.1
                          have p16784_2 := h16784c.2.2.1
                          have p16784_3 := h16784c.2.2.2
                          linarith only [h6, hlam, p16784_0]
                        · have p16784_0 := h16784c.1
                          have p16784_1 := h16784c.2.1
                          have p16784_2 := h16784c.2.2.1
                          have p16784_3 := h16784c.2.2.2
                          rcases p16784_3 (m.d 0 2) (by simp) with h16828 | h16828
                          · rcases p16784_3 (m.d 1 2) (by simp) with h16829 | h16829
                            · linarith only [h16829, hlam, p16784_0]
                            · rcases p16784_3 (m.d 2 3) (by simp) with h16831 | h16831
                              · linarith only [h16710, h16831, hlam]
                              · linarith only [h14160, h16831, hlam]
                          · linarith only [h0, h16828, hlam]
                        · have p16784_0 := h16784c.1
                          have p16784_1 := h16784c.2.1
                          have p16784_2 := h16784c.2.2.1
                          have p16784_3 := h16784c.2.2.2
                          linarith only [h14160, hc12, hc25, hlam, hphi, p16784_1]
                        · have p16784_0 := h16784c.1
                          have p16784_1 := h16784c.2.1
                          have p16784_2 := h16784c.2.2.1
                          have p16784_3 := h16784c.2.2.2
                          linarith only [h16712, hlam, p16784_1]
                        · have p16784_0 := h16784c.1
                          have p16784_1 := h16784c.2.1
                          have p16784_2 := h16784c.2.2.1
                          have p16784_3 := h16784c.2.2.2
                          linarith only [hlam, p16784_0]
                      · rcases h2bigk with h16838c | h16838c | h16838c | h16838c | h16838c | h16838c | h16838c | h16838c | h16838c | h16838c | h16838c | h16838c | h16838c | h16838c | h16838c | h16838c | h16838c | h16838c | h16838c | h16838c | h16838c | h16838c | h16838c | h16838c | h16838c
                        · have p16838_0 := h16838c.1
                          have p16838_1 := h16838c.2.1
                          have p16838_2 := h16838c.2.2.1
                          have p16838_3 := h16838c.2.2.2
                          linarith only [hlam, p16838_0]
                        · have p16838_0 := h16838c.1
                          have p16838_1 := h16838c.2.1
                          have p16838_2 := h16838c.2.2.1
                          have p16838_3 := h16838c.2.2.2
                          linarith only [h14160, h15899, h15903, h16712, h5, hlam, p16838_2]
                        · have p16838_0 := h16838c.1
                          have p16838_1 := h16838c.2.1
                          have p16838_2 := h16838c.2.2.1
                          have p16838_3 := h16838c.2.2.2
                          rcases p16838_3 (m.d 0 2) (by simp) with h16841 | h16841
                          · rcases p16838_3 (m.d 1 2) (by simp) with h16842 | h16842
                            · linarith only [h0, h16842, hlam]
                            · rcases p16838_3 (m.d 2 3) (by simp) with h16844 | h16844
                              · linarith only [h16844, hlam, p16838_0]
                              · rcases p16838_3 (m.d 2 4) (by simp) with h16846 | h16846
                                · linarith only [h16846, h5, hlam]
                                · linarith only [h16708, h16846, hlam]
                          · linarith only [h16841, hlam, p16838_0]
                        · have p16838_0 := h16838c.1
                          have p16838_1 := h16838c.2.1
                          have p16838_2 := h16838c.2.2.1
                          have p16838_3 := h16838c.2.2.2
                          linarith only [h14160, h15899, h15903, h16712, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p16838_1]
                        · have p16838_0 := h16838c.1
                          have p16838_1 := h16838c.2.1
                          have p16838_2 := h16838c.2.2.1
                          have p16838_3 := h16838c.2.2.2
                          rcases p16838_3 (m.d 0 2) (by simp) with h16851 | h16851
                          · rcases p16838_3 (m.d 1 2) (by simp) with h16852 | h16852
                            · linarith only [h0, h16852, hlam]
                            · rcases p16838_3 (m.d 2 3) (by simp) with h16854 | h16854
                              · linarith only [h16854, h4, hlam]
                              · rcases p16838_3 (m.d 2 4) (by simp) with h16856 | h16856
                                · linarith only [h16856, h5, hlam]
                                · linarith only [h16712, h16856, hlam]
                          · linarith only [h16851, hlam, p16838_0]
                        · have p16838_0 := h16838c.1
                          have p16838_1 := h16838c.2.1
                          have p16838_2 := h16838c.2.2.1
                          have p16838_3 := h16838c.2.2.2
                          linarith only [h0, hlam, p16838_1]
                        · have p16838_0 := h16838c.1
                          have p16838_1 := h16838c.2.1
                          have p16838_2 := h16838c.2.2.1
                          have p16838_3 := h16838c.2.2.2
                          linarith only [hlam, p16838_0]
                        · have p16838_0 := h16838c.1
                          have p16838_1 := h16838c.2.1
                          have p16838_2 := h16838c.2.2.1
                          have p16838_3 := h16838c.2.2.2
                          linarith only [h14160, hlam, p16838_0]
                        · have p16838_0 := h16838c.1
                          have p16838_1 := h16838c.2.1
                          have p16838_2 := h16838c.2.2.1
                          have p16838_3 := h16838c.2.2.2
                          linarith only [h15885, hlam, p16838_0]
                        · have p16838_0 := h16838c.1
                          have p16838_1 := h16838c.2.1
                          have p16838_2 := h16838c.2.2.1
                          have p16838_3 := h16838c.2.2.2
                          linarith only [h15893, hlam, p16838_0]
                        · have p16838_0 := h16838c.1
                          have p16838_1 := h16838c.2.1
                          have p16838_2 := h16838c.2.2.1
                          have p16838_3 := h16838c.2.2.2
                          linarith only [h4, hlam, p16838_0]
                        · have p16838_0 := h16838c.1
                          have p16838_1 := h16838c.2.1
                          have p16838_2 := h16838c.2.2.1
                          have p16838_3 := h16838c.2.2.2
                          linarith only [h13284, h16713, h4, hc12, hc34, hlam, hphi, ht23, p16838_1]
                        · have p16838_0 := h16838c.1
                          have p16838_1 := h16838c.2.1
                          have p16838_2 := h16838c.2.2.1
                          have p16838_3 := h16838c.2.2.2
                          linarith only [hlam, p16838_0]
                        · have p16838_0 := h16838c.1
                          have p16838_1 := h16838c.2.1
                          have p16838_2 := h16838c.2.2.1
                          have p16838_3 := h16838c.2.2.2
                          linarith only [h16708, hlam, p16838_1]
                        · have p16838_0 := h16838c.1
                          have p16838_1 := h16838c.2.1
                          have p16838_2 := h16838c.2.2.1
                          have p16838_3 := h16838c.2.2.2
                          linarith only [h16710, hlam, p16838_1]
                        · have p16838_0 := h16838c.1
                          have p16838_1 := h16838c.2.1
                          have p16838_2 := h16838c.2.2.1
                          have p16838_3 := h16838c.2.2.2
                          linarith only [h5, hlam, p16838_0]
                        · have p16838_0 := h16838c.1
                          have p16838_1 := h16838c.2.1
                          have p16838_2 := h16838c.2.2.1
                          have p16838_3 := h16838c.2.2.2
                          rcases p16838_3 (m.d 0 2) (by simp) with h16871 | h16871
                          · rcases p16838_3 (m.d 1 2) (by simp) with h16872 | h16872
                            · linarith only [h16872, hlam, p16838_0]
                            · rcases p16838_3 (m.d 2 3) (by simp) with h16874 | h16874
                              · linarith only [h16708, h16874, hlam]
                              · linarith only [h14160, h16874, hlam]
                          · linarith only [h0, h16871, hlam]
                        · have p16838_0 := h16838c.1
                          have p16838_1 := h16838c.2.1
                          have p16838_2 := h16838c.2.2.1
                          have p16838_3 := h16838c.2.2.2
                          linarith only [h0, h14160, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p16838_1]
                        · have p16838_0 := h16838c.1
                          have p16838_1 := h16838c.2.1
                          have p16838_2 := h16838c.2.2.1
                          have p16838_3 := h16838c.2.2.2
                          linarith only [hlam, p16838_0]
                        · have p16838_0 := h16838c.1
                          have p16838_1 := h16838c.2.1
                          have p16838_2 := h16838c.2.2.1
                          have p16838_3 := h16838c.2.2.2
                          linarith only [h0, h15893, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p16838_1]
                        · have p16838_0 := h16838c.1
                          have p16838_1 := h16838c.2.1
                          have p16838_2 := h16838c.2.2.1
                          have p16838_3 := h16838c.2.2.2
                          linarith only [h6, hlam, p16838_0]
                        · have p16838_0 := h16838c.1
                          have p16838_1 := h16838c.2.1
                          have p16838_2 := h16838c.2.2.1
                          have p16838_3 := h16838c.2.2.2
                          rcases p16838_3 (m.d 0 2) (by simp) with h16882 | h16882
                          · rcases p16838_3 (m.d 1 2) (by simp) with h16883 | h16883
                            · linarith only [h16883, hlam, p16838_0]
                            · rcases p16838_3 (m.d 2 3) (by simp) with h16885 | h16885
                              · linarith only [h16710, h16885, hlam]
                              · linarith only [h14160, h16885, hlam]
                          · linarith only [h0, h16882, hlam]
                        · have p16838_0 := h16838c.1
                          have p16838_1 := h16838c.2.1
                          have p16838_2 := h16838c.2.2.1
                          have p16838_3 := h16838c.2.2.2
                          linarith only [h14160, hc12, hc25, hlam, hphi, p16838_1]
                        · have p16838_0 := h16838c.1
                          have p16838_1 := h16838c.2.1
                          have p16838_2 := h16838c.2.2.1
                          have p16838_3 := h16838c.2.2.2
                          linarith only [h16712, hlam, p16838_1]
                        · have p16838_0 := h16838c.1
                          have p16838_1 := h16838c.2.1
                          have p16838_2 := h16838c.2.2.1
                          have p16838_3 := h16838c.2.2.2
                          linarith only [hlam, p16838_0]
                      · rcases h2bigk with h16892c | h16892c | h16892c | h16892c | h16892c | h16892c | h16892c | h16892c | h16892c | h16892c | h16892c | h16892c | h16892c | h16892c | h16892c | h16892c | h16892c | h16892c | h16892c | h16892c | h16892c | h16892c | h16892c | h16892c | h16892c
                        · have p16892_0 := h16892c.1
                          have p16892_1 := h16892c.2.1
                          have p16892_2 := h16892c.2.2.1
                          have p16892_3 := h16892c.2.2.2
                          linarith only [hlam, p16892_0]
                        · have p16892_0 := h16892c.1
                          have p16892_1 := h16892c.2.1
                          have p16892_2 := h16892c.2.2.1
                          have p16892_3 := h16892c.2.2.2
                          linarith only [h14160, h15899, h15903, h16712, h5, hlam, p16892_2]
                        · have p16892_0 := h16892c.1
                          have p16892_1 := h16892c.2.1
                          have p16892_2 := h16892c.2.2.1
                          have p16892_3 := h16892c.2.2.2
                          rcases p16892_3 (m.d 0 2) (by simp) with h16895 | h16895
                          · rcases p16892_3 (m.d 1 2) (by simp) with h16896 | h16896
                            · linarith only [h0, h16896, hlam]
                            · rcases p16892_3 (m.d 2 3) (by simp) with h16898 | h16898
                              · linarith only [h16898, hlam, p16892_0]
                              · rcases p16892_3 (m.d 2 4) (by simp) with h16900 | h16900
                                · linarith only [h16900, h5, hlam]
                                · linarith only [h16708, h16900, hlam]
                          · linarith only [h16895, hlam, p16892_0]
                        · have p16892_0 := h16892c.1
                          have p16892_1 := h16892c.2.1
                          have p16892_2 := h16892c.2.2.1
                          have p16892_3 := h16892c.2.2.2
                          linarith only [h14160, h15899, h15903, h16712, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p16892_1]
                        · have p16892_0 := h16892c.1
                          have p16892_1 := h16892c.2.1
                          have p16892_2 := h16892c.2.2.1
                          have p16892_3 := h16892c.2.2.2
                          rcases p16892_3 (m.d 0 2) (by simp) with h16905 | h16905
                          · rcases p16892_3 (m.d 1 2) (by simp) with h16906 | h16906
                            · linarith only [h0, h16906, hlam]
                            · rcases p16892_3 (m.d 2 3) (by simp) with h16908 | h16908
                              · linarith only [h16908, h4, hlam]
                              · rcases p16892_3 (m.d 2 4) (by simp) with h16910 | h16910
                                · linarith only [h16910, h5, hlam]
                                · linarith only [h16712, h16910, hlam]
                          · linarith only [h16905, hlam, p16892_0]
                        · have p16892_0 := h16892c.1
                          have p16892_1 := h16892c.2.1
                          have p16892_2 := h16892c.2.2.1
                          have p16892_3 := h16892c.2.2.2
                          linarith only [h0, hlam, p16892_1]
                        · have p16892_0 := h16892c.1
                          have p16892_1 := h16892c.2.1
                          have p16892_2 := h16892c.2.2.1
                          have p16892_3 := h16892c.2.2.2
                          linarith only [hlam, p16892_0]
                        · have p16892_0 := h16892c.1
                          have p16892_1 := h16892c.2.1
                          have p16892_2 := h16892c.2.2.1
                          have p16892_3 := h16892c.2.2.2
                          linarith only [h14160, hlam, p16892_0]
                        · have p16892_0 := h16892c.1
                          have p16892_1 := h16892c.2.1
                          have p16892_2 := h16892c.2.2.1
                          have p16892_3 := h16892c.2.2.2
                          linarith only [h15885, hlam, p16892_0]
                        · have p16892_0 := h16892c.1
                          have p16892_1 := h16892c.2.1
                          have p16892_2 := h16892c.2.2.1
                          have p16892_3 := h16892c.2.2.2
                          linarith only [h15893, hlam, p16892_0]
                        · have p16892_0 := h16892c.1
                          have p16892_1 := h16892c.2.1
                          have p16892_2 := h16892c.2.2.1
                          have p16892_3 := h16892c.2.2.2
                          linarith only [h4, hlam, p16892_0]
                        · have p16892_0 := h16892c.1
                          have p16892_1 := h16892c.2.1
                          have p16892_2 := h16892c.2.2.1
                          have p16892_3 := h16892c.2.2.2
                          linarith only [h13284, h16713, h4, hc12, hc34, hlam, hphi, ht23, p16892_1]
                        · have p16892_0 := h16892c.1
                          have p16892_1 := h16892c.2.1
                          have p16892_2 := h16892c.2.2.1
                          have p16892_3 := h16892c.2.2.2
                          linarith only [hlam, p16892_0]
                        · have p16892_0 := h16892c.1
                          have p16892_1 := h16892c.2.1
                          have p16892_2 := h16892c.2.2.1
                          have p16892_3 := h16892c.2.2.2
                          linarith only [h16708, hlam, p16892_1]
                        · have p16892_0 := h16892c.1
                          have p16892_1 := h16892c.2.1
                          have p16892_2 := h16892c.2.2.1
                          have p16892_3 := h16892c.2.2.2
                          linarith only [h16710, hlam, p16892_1]
                        · have p16892_0 := h16892c.1
                          have p16892_1 := h16892c.2.1
                          have p16892_2 := h16892c.2.2.1
                          have p16892_3 := h16892c.2.2.2
                          linarith only [h5, hlam, p16892_0]
                        · have p16892_0 := h16892c.1
                          have p16892_1 := h16892c.2.1
                          have p16892_2 := h16892c.2.2.1
                          have p16892_3 := h16892c.2.2.2
                          rcases p16892_3 (m.d 0 2) (by simp) with h16925 | h16925
                          · rcases p16892_3 (m.d 1 2) (by simp) with h16926 | h16926
                            · linarith only [h16926, hlam, p16892_0]
                            · rcases p16892_3 (m.d 2 3) (by simp) with h16928 | h16928
                              · linarith only [h16708, h16928, hlam]
                              · linarith only [h14160, h16928, hlam]
                          · linarith only [h0, h16925, hlam]
                        · have p16892_0 := h16892c.1
                          have p16892_1 := h16892c.2.1
                          have p16892_2 := h16892c.2.2.1
                          have p16892_3 := h16892c.2.2.2
                          linarith only [h14160, hc12, hc24, hlam, hphi, p16892_1]
                        · have p16892_0 := h16892c.1
                          have p16892_1 := h16892c.2.1
                          have p16892_2 := h16892c.2.2.1
                          have p16892_3 := h16892c.2.2.2
                          linarith only [hlam, p16892_0]
                        · have p16892_0 := h16892c.1
                          have p16892_1 := h16892c.2.1
                          have p16892_2 := h16892c.2.2.1
                          have p16892_3 := h16892c.2.2.2
                          linarith only [h0, h15893, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p16892_1]
                        · have p16892_0 := h16892c.1
                          have p16892_1 := h16892c.2.1
                          have p16892_2 := h16892c.2.2.1
                          have p16892_3 := h16892c.2.2.2
                          linarith only [h6, hlam, p16892_0]
                        · have p16892_0 := h16892c.1
                          have p16892_1 := h16892c.2.1
                          have p16892_2 := h16892c.2.2.1
                          have p16892_3 := h16892c.2.2.2
                          rcases p16892_3 (m.d 0 2) (by simp) with h16936 | h16936
                          · rcases p16892_3 (m.d 1 2) (by simp) with h16937 | h16937
                            · linarith only [h16937, hlam, p16892_0]
                            · rcases p16892_3 (m.d 2 3) (by simp) with h16939 | h16939
                              · linarith only [h16710, h16939, hlam]
                              · linarith only [h14160, h16939, hlam]
                          · linarith only [h0, h16936, hlam]
                        · have p16892_0 := h16892c.1
                          have p16892_1 := h16892c.2.1
                          have p16892_2 := h16892c.2.2.1
                          have p16892_3 := h16892c.2.2.2
                          linarith only [h14160, hc12, hc25, hlam, hphi, p16892_1]
                        · have p16892_0 := h16892c.1
                          have p16892_1 := h16892c.2.1
                          have p16892_2 := h16892c.2.2.1
                          have p16892_3 := h16892c.2.2.2
                          linarith only [h16712, hlam, p16892_1]
                        · have p16892_0 := h16892c.1
                          have p16892_1 := h16892c.2.1
                          have p16892_2 := h16892c.2.2.1
                          have p16892_3 := h16892c.2.2.2
                          linarith only [hlam, p16892_0]
            · linarith only [h16719, hlam, p16714_0]
          · have p16714_0 := h16714c.1
            have p16714_1 := h16714c.2.1
            have p16714_2 := h16714c.2.2.1
            have p16714_3 := h16714c.2.2.2
            linarith only [h0, hlam, p16714_0]
          · have p16714_0 := h16714c.1
            have p16714_1 := h16714c.2.1
            have p16714_2 := h16714c.2.2.1
            have p16714_3 := h16714c.2.2.2
            linarith only [hlam, p16714_0]
          · have p16714_0 := h16714c.1
            have p16714_1 := h16714c.2.1
            have p16714_2 := h16714c.2.2.1
            have p16714_3 := h16714c.2.2.2
            linarith only [h14160, hlam, p16714_1]
          · have p16714_0 := h16714c.1
            have p16714_1 := h16714c.2.1
            have p16714_2 := h16714c.2.2.1
            have p16714_3 := h16714c.2.2.2
            linarith only [h15885, hlam, p16714_1]
          · have p16714_0 := h16714c.1
            have p16714_1 := h16714c.2.1
            have p16714_2 := h16714c.2.2.1
            have p16714_3 := h16714c.2.2.2
            linarith only [h15893, hlam, p16714_1]
          · have p16714_0 := h16714c.1
            have p16714_1 := h16714c.2.1
            have p16714_2 := h16714c.2.2.1
            have p16714_3 := h16714c.2.2.2
            linarith only [h1, hlam, p16714_0]
          · have p16714_0 := h16714c.1
            have p16714_1 := h16714c.2.1
            have p16714_2 := h16714c.2.2.1
            have p16714_3 := h16714c.2.2.2
            linarith only [h15899, h15903, hc12, hc45, hlam, hphi, ht23, ht34, p16714_1]
          · have p16714_0 := h16714c.1
            have p16714_1 := h16714c.2.1
            have p16714_2 := h16714c.2.2.1
            have p16714_3 := h16714c.2.2.2
            linarith only [hlam, p16714_0]
          · have p16714_0 := h16714c.1
            have p16714_1 := h16714c.2.1
            have p16714_2 := h16714c.2.2.1
            have p16714_3 := h16714c.2.2.2
            linarith only [h15899, hlam, p16714_0]
          · have p16714_0 := h16714c.1
            have p16714_1 := h16714c.2.1
            have p16714_2 := h16714c.2.2.1
            have p16714_3 := h16714c.2.2.2
            linarith only [h15901, hlam, p16714_1]
          · have p16714_0 := h16714c.1
            have p16714_1 := h16714c.2.1
            have p16714_2 := h16714c.2.2.1
            have p16714_3 := h16714c.2.2.2
            linarith only [h2, hlam, p16714_0]
          · have p16714_0 := h16714c.1
            have p16714_1 := h16714c.2.1
            have p16714_2 := h16714c.2.2.1
            have p16714_3 := h16714c.2.2.2
            linarith only [h14159, h15903, h7, hc12, hc34, hlam, hphi, ht23, p16714_1]
          · have p16714_0 := h16714c.1
            have p16714_1 := h16714c.2.1
            have p16714_2 := h16714c.2.2.1
            have p16714_3 := h16714c.2.2.2
            linarith only [h14159, h15903, h7, hc13, hc34, hlam, hphi, p16714_1]
          · have p16714_0 := h16714c.1
            have p16714_1 := h16714c.2.1
            have p16714_2 := h16714c.2.2.1
            have p16714_3 := h16714c.2.2.2
            linarith only [hlam, p16714_0]
          · have p16714_0 := h16714c.1
            have p16714_1 := h16714c.2.1
            have p16714_2 := h16714c.2.2.1
            have p16714_3 := h16714c.2.2.2
            linarith only [h15903, hlam, p16714_1]
          · have p16714_0 := h16714c.1
            have p16714_1 := h16714c.2.1
            have p16714_2 := h16714c.2.2.1
            have p16714_3 := h16714c.2.2.2
            linarith only [h3, hlam, p16714_0]
          · have p16714_0 := h16714c.1
            have p16714_1 := h16714c.2.1
            have p16714_2 := h16714c.2.2.1
            have p16714_3 := h16714c.2.2.2
            linarith only [h14159, h15903, h7, hc12, hc34, hlam, hphi, ht23, p16714_1]
          · have p16714_0 := h16714c.1
            have p16714_1 := h16714c.2.1
            have p16714_2 := h16714c.2.2.1
            have p16714_3 := h16714c.2.2.2
            linarith only [h14159, h14160, h15903, h7, hc12, hc34, hlam, hphi, ht23, p16714_1]
          · have p16714_0 := h16714c.1
            have p16714_1 := h16714c.2.1
            have p16714_2 := h16714c.2.2.1
            have p16714_3 := h16714c.2.2.2
            linarith only [h14159, h15885, h15903, h7, hc12, hc34, hlam, hphi, ht23, p16714_1]
          · have p16714_0 := h16714c.1
            have p16714_1 := h16714c.2.1
            have p16714_2 := h16714c.2.2.1
            have p16714_3 := h16714c.2.2.2
            linarith only [hlam, p16714_0]
        · linarith only [h16712, h16713, h5, h7, hlam]
      · linarith only [h14159, h15885, h16712, h7, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 5618000 in
set_option maxHeartbeats 5618000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x1_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (hg14159 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14160 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h15885 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h15893 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h15899 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h15901 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have h14159 := hg14159
  rcases m.htr 1 4 5 (by decide) (by decide) with h15903 | h15903
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x1_x1_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 hg14159 h14160 h15885 h15893 h15899 h15901 h15903
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x1_x1_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 hg14159 h14160 h15885 h15893 h15899 h15901 h15903

set_option maxHeartbeats 5618000 in
set_option maxHeartbeats 5618000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (hg14159 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14160 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h15885 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h15893 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h15899 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have h14159 := hg14159
  rcases m.htr 1 3 5 (by decide) (by decide) with h15901 | h15901
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x1_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 hg14159 h14160 h15885 h15893 h15899 h15901
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x1_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 hg14159 h14160 h15885 h15893 h15899 h15901

set_option maxHeartbeats 5618000 in
set_option maxHeartbeats 5618000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (hg14159 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14160 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h15885 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h15893 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have h14159 := hg14159
  rcases m.htr 1 3 4 (by decide) (by decide) with h15899 | h15899
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 hg14159 h14160 h15885 h15893 h15899
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 hg14159 h14160 h15885 h15893 h15899

set_option maxHeartbeats 5618000 in
set_option maxHeartbeats 5618000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (hg14159 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14160 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h15885 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have h14159 := hg14159
  rcases m.htr 1 2 5 (by decide) (by decide) with h15893 | h15893
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 hg14159 h14160 h15885 h15893
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 hg14159 h14160 h15885 h15893

set_option maxHeartbeats 5618000 in
set_option maxHeartbeats 5618000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (hg14159 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14160 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have h14159 := hg14159
  rcases m.htr 1 2 4 (by decide) (by decide) with h15885 | h15885
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 hg14159 h14160 h15885
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 hg14159 h14160 h15885

set_option maxHeartbeats 5618000 in
set_option maxHeartbeats 5618000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (hg14159 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have h14159 := hg14159
  rcases m.htr 1 2 3 (by decide) (by decide) with h14160 | h14160
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 hg14159 h14160
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 hg14159 h14160

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4 h5 h6 h7 h13284 h14159

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  linarith only [h1, h16972, h7, hlam]

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  linarith only [h1, h13284, h16974, hlam]

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h16976 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  linarith only [h14159, h16976, h2, hlam]

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h16976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h16978 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  linarith only [h1, h16969, h16978, h7, hlam]

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h16976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h16978 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h16980 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  linarith only [h13284, h16980, h4, hlam]

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h16976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h16978 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h16980 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h16982 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  linarith only [h14159, h16970, h16982, h2, hlam]

end R2N4
