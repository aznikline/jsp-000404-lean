import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_4S29

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 15022000 in
set_option maxHeartbeats 15022000 in
theorem r1l7_11_23_L_I_H_I_s11_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h11385 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h11386 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h11387 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h11388 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h11389 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h11390 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h0 := hg0
  rcases m.htr 0 3 5 (by decide) (by decide) with h11746 | h11746
  · rcases m.htr 0 4 5 (by decide) (by decide) with h11747 | h11747
    · rcases m.htr 1 2 3 (by decide) (by decide) with h11748 | h11748
      · rcases m.htr 1 2 4 (by decide) (by decide) with h11749 | h11749
        · rcases m.htr 1 2 5 (by decide) (by decide) with h11750 | h11750
          · rcases m.htr 1 3 4 (by decide) (by decide) with h11751 | h11751
            · linarith only [h0, h11385, h11390, h11751, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11753 | h11753
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11754 | h11754
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11755 | h11755
                  · linarith only [h11385, h11390, h11748, h11755, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11757 | h11757
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11758 | h11758
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11759 | h11759
                        · rcases h1bigk with h11760c | h11760c | h11760c | h11760c | h11760c | h11760c | h11760c | h11760c | h11760c | h11760c | h11760c | h11760c | h11760c | h11760c | h11760c | h11760c | h11760c | h11760c | h11760c | h11760c | h11760c | h11760c | h11760c | h11760c | h11760c
                          · have p11760_0 := h11760c.1
                            have p11760_1 := h11760c.2.1
                            have p11760_2 := h11760c.2.2.1
                            have p11760_3 := h11760c.2.2.2
                            linarith only [hlam, p11760_0]
                          · have p11760_0 := h11760c.1
                            have p11760_1 := h11760c.2.1
                            have p11760_2 := h11760c.2.2.1
                            have p11760_3 := h11760c.2.2.2
                            linarith only [h0, hlam, p11760_0]
                          · have p11760_0 := h11760c.1
                            have p11760_1 := h11760c.2.1
                            have p11760_2 := h11760c.2.2.1
                            have p11760_3 := h11760c.2.2.2
                            linarith only [h0, h11748, h11757, h11759, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11760_1]
                          · have p11760_0 := h11760c.1
                            have p11760_1 := h11760c.2.1
                            have p11760_2 := h11760c.2.2.1
                            have p11760_3 := h11760c.2.2.2
                            linarith only [h0, h11748, h11751, h11757, h11759, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11760_1]
                          · have p11760_0 := h11760c.1
                            have p11760_1 := h11760c.2.1
                            have p11760_2 := h11760c.2.2.1
                            have p11760_3 := h11760c.2.2.2
                            rcases p11760_3 (m.d 0 1) (by simp) with h11765 | h11765
                            · rcases p11760_3 (m.d 1 2) (by simp) with h11766 | h11766
                              · rcases p11760_3 (m.d 1 3) (by simp) with h11767 | h11767
                                · linarith only [h11385, h11767, hlam]
                                · linarith only [h11753, h11767, hlam]
                              · linarith only [h11750, h11766, hlam]
                            · linarith only [h11765, hlam, p11760_0]
                          · have p11760_0 := h11760c.1
                            have p11760_1 := h11760c.2.1
                            have p11760_2 := h11760c.2.2.1
                            have p11760_3 := h11760c.2.2.2
                            linarith only [h11385, h11748, h11757, h11759, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11760_1]
                          · have p11760_0 := h11760c.1
                            have p11760_1 := h11760c.2.1
                            have p11760_2 := h11760c.2.2.1
                            have p11760_3 := h11760c.2.2.2
                            linarith only [hlam, p11760_0]
                          · have p11760_0 := h11760c.1
                            have p11760_1 := h11760c.2.1
                            have p11760_2 := h11760c.2.2.1
                            have p11760_3 := h11760c.2.2.2
                            rcases p11760_3 (m.d 0 1) (by simp) with h11774 | h11774
                            · linarith only [h0, h11774, hlam]
                            · linarith only [h11385, h11774, hlam]
                          · have p11760_0 := h11760c.1
                            have p11760_1 := h11760c.2.1
                            have p11760_2 := h11760c.2.2.1
                            have p11760_3 := h11760c.2.2.2
                            rcases p11760_3 (m.d 0 1) (by simp) with h11777 | h11777
                            · linarith only [h0, h11777, hlam]
                            · linarith only [h11386, h11777, hlam]
                          · have p11760_0 := h11760c.1
                            have p11760_1 := h11760c.2.1
                            have p11760_2 := h11760c.2.2.1
                            have p11760_3 := h11760c.2.2.2
                            rcases p11760_3 (m.d 0 1) (by simp) with h11780 | h11780
                            · linarith only [h0, h11780, hlam]
                            · linarith only [h11387, h11780, hlam]
                          · have p11760_0 := h11760c.1
                            have p11760_1 := h11760c.2.1
                            have p11760_2 := h11760c.2.2.1
                            have p11760_3 := h11760c.2.2.2
                            linarith only [h11385, hlam, p11760_0]
                          · have p11760_0 := h11760c.1
                            have p11760_1 := h11760c.2.1
                            have p11760_2 := h11760c.2.2.1
                            have p11760_3 := h11760c.2.2.2
                            linarith only [h11748, hlam, p11760_1]
                          · have p11760_0 := h11760c.1
                            have p11760_1 := h11760c.2.1
                            have p11760_2 := h11760c.2.2.1
                            have p11760_3 := h11760c.2.2.2
                            linarith only [hlam, p11760_0]
                          · have p11760_0 := h11760c.1
                            have p11760_1 := h11760c.2.1
                            have p11760_2 := h11760c.2.2.1
                            have p11760_3 := h11760c.2.2.2
                            linarith only [h11751, hlam, p11760_1]
                          · have p11760_0 := h11760c.1
                            have p11760_1 := h11760c.2.1
                            have p11760_2 := h11760c.2.2.1
                            have p11760_3 := h11760c.2.2.2
                            linarith only [h0, h11386, h11751, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p11760_1]
                          · have p11760_0 := h11760c.1
                            have p11760_1 := h11760c.2.1
                            have p11760_2 := h11760c.2.2.1
                            have p11760_3 := h11760c.2.2.2
                            linarith only [h11386, hlam, p11760_0]
                          · have p11760_0 := h11760c.1
                            have p11760_1 := h11760c.2.1
                            have p11760_2 := h11760c.2.2.1
                            have p11760_3 := h11760c.2.2.2
                            linarith only [h11749, hlam, p11760_1]
                          · have p11760_0 := h11760c.1
                            have p11760_1 := h11760c.2.1
                            have p11760_2 := h11760c.2.2.1
                            have p11760_3 := h11760c.2.2.2
                            linarith only [h11386, h11748, h11757, hc01, hc35, hlam, hphi, ht0b, ht5b, p11760_1]
                          · have p11760_0 := h11760c.1
                            have p11760_1 := h11760c.2.1
                            have p11760_2 := h11760c.2.2.1
                            have p11760_3 := h11760c.2.2.2
                            linarith only [hlam, p11760_0]
                          · have p11760_0 := h11760c.1
                            have p11760_1 := h11760c.2.1
                            have p11760_2 := h11760c.2.2.1
                            have p11760_3 := h11760c.2.2.2
                            linarith only [h0, h11386, h11753, h11759, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11760_1]
                          · have p11760_0 := h11760c.1
                            have p11760_1 := h11760c.2.1
                            have p11760_2 := h11760c.2.2.1
                            have p11760_3 := h11760c.2.2.2
                            linarith only [h11387, hlam, p11760_0]
                          · have p11760_0 := h11760c.1
                            have p11760_1 := h11760c.2.1
                            have p11760_2 := h11760c.2.2.1
                            have p11760_3 := h11760c.2.2.2
                            linarith only [h11750, hlam, p11760_1]
                          · have p11760_0 := h11760c.1
                            have p11760_1 := h11760c.2.1
                            have p11760_2 := h11760c.2.2.1
                            have p11760_3 := h11760c.2.2.2
                            linarith only [h11753, hlam, p11760_0]
                          · have p11760_0 := h11760c.1
                            have p11760_1 := h11760c.2.1
                            have p11760_2 := h11760c.2.2.1
                            have p11760_3 := h11760c.2.2.2
                            linarith only [h11754, hlam, p11760_0]
                          · have p11760_0 := h11760c.1
                            have p11760_1 := h11760c.2.1
                            have p11760_2 := h11760c.2.2.1
                            have p11760_3 := h11760c.2.2.2
                            linarith only [hlam, p11760_0]
                        · linarith only [h11385, h11390, h11747, h11748, h11757, h11759, hc04, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h0, h11386, h11754, h11758, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h11390, h11746, h11757, hc23, hc34, hlam, hphi]
                · linarith only [h0, h11386, h11747, h11751, h11753, h11754, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · linarith only [h11390, h11746, h11748, h11753, hc23, hc34, hlam, hphi]
          · linarith only [h0, h11387, h11750, hlam]
        · linarith only [h0, h11389, h11749, hlam]
      · linarith only [h0, h11388, h11748, hlam]
    · linarith only [h11390, h11746, h11747, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h11807 | h11807
    · rcases m.htr 1 2 3 (by decide) (by decide) with h11808 | h11808
      · rcases m.htr 1 2 4 (by decide) (by decide) with h11809 | h11809
        · rcases m.htr 1 2 5 (by decide) (by decide) with h11810 | h11810
          · rcases m.htr 1 3 4 (by decide) (by decide) with h11811 | h11811
            · linarith only [h0, h11385, h11390, h11811, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11813 | h11813
              · linarith only [h11385, h11746, h11813, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11815 | h11815
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11816 | h11816
                  · linarith only [h11388, h11390, h11816, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11818 | h11818
                    · linarith only [h0, h11385, h11746, h11808, h11818, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11820 | h11820
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11821 | h11821
                        · rcases h1bigk with h11822c | h11822c | h11822c | h11822c | h11822c | h11822c | h11822c | h11822c | h11822c | h11822c | h11822c | h11822c | h11822c | h11822c | h11822c | h11822c | h11822c | h11822c | h11822c | h11822c | h11822c | h11822c | h11822c | h11822c | h11822c
                          · have p11822_0 := h11822c.1
                            have p11822_1 := h11822c.2.1
                            have p11822_2 := h11822c.2.2.1
                            have p11822_3 := h11822c.2.2.2
                            linarith only [hlam, p11822_0]
                          · have p11822_0 := h11822c.1
                            have p11822_1 := h11822c.2.1
                            have p11822_2 := h11822c.2.2.1
                            have p11822_3 := h11822c.2.2.2
                            linarith only [h0, hlam, p11822_0]
                          · have p11822_0 := h11822c.1
                            have p11822_1 := h11822c.2.1
                            have p11822_2 := h11822c.2.2.1
                            have p11822_3 := h11822c.2.2.2
                            rcases p11822_3 (m.d 0 1) (by simp) with h11825 | h11825
                            · rcases p11822_3 (m.d 1 2) (by simp) with h11826 | h11826
                              · rcases p11822_3 (m.d 1 3) (by simp) with h11827 | h11827
                                · linarith only [h11827, hlam, p11822_0]
                                · rcases p11822_3 (m.d 1 4) (by simp) with h11829 | h11829
                                  · linarith only [h11386, h11829, hlam]
                                  · linarith only [h11811, h11829, hlam]
                              · linarith only [h11808, h11826, hlam]
                            · linarith only [h11825, hlam, p11822_0]
                          · have p11822_0 := h11822c.1
                            have p11822_1 := h11822c.2.1
                            have p11822_2 := h11822c.2.2.1
                            have p11822_3 := h11822c.2.2.2
                            linarith only [h0, h11809, h11820, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11822_1]
                          · have p11822_0 := h11822c.1
                            have p11822_1 := h11822c.2.1
                            have p11822_2 := h11822c.2.2.1
                            have p11822_3 := h11822c.2.2.2
                            rcases p11822_3 (m.d 0 1) (by simp) with h11835 | h11835
                            · rcases p11822_3 (m.d 1 2) (by simp) with h11836 | h11836
                              · rcases p11822_3 (m.d 1 3) (by simp) with h11837 | h11837
                                · linarith only [h11385, h11837, hlam]
                                · rcases p11822_3 (m.d 1 4) (by simp) with h11839 | h11839
                                  · linarith only [h11386, h11839, hlam]
                                  · linarith only [h11815, h11839, hlam]
                              · linarith only [h11810, h11836, hlam]
                            · linarith only [h11835, hlam, p11822_0]
                          · have p11822_0 := h11822c.1
                            have p11822_1 := h11822c.2.1
                            have p11822_2 := h11822c.2.2.1
                            have p11822_3 := h11822c.2.2.2
                            linarith only [h11386, h11809, h11820, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11822_1]
                          · have p11822_0 := h11822c.1
                            have p11822_1 := h11822c.2.1
                            have p11822_2 := h11822c.2.2.1
                            have p11822_3 := h11822c.2.2.2
                            linarith only [hlam, p11822_0]
                          · have p11822_0 := h11822c.1
                            have p11822_1 := h11822c.2.1
                            have p11822_2 := h11822c.2.2.1
                            have p11822_3 := h11822c.2.2.2
                            rcases p11822_3 (m.d 0 1) (by simp) with h11846 | h11846
                            · linarith only [h0, h11846, hlam]
                            · linarith only [h11385, h11846, hlam]
                          · have p11822_0 := h11822c.1
                            have p11822_1 := h11822c.2.1
                            have p11822_2 := h11822c.2.2.1
                            have p11822_3 := h11822c.2.2.2
                            rcases p11822_3 (m.d 0 1) (by simp) with h11849 | h11849
                            · linarith only [h0, h11849, hlam]
                            · linarith only [h11386, h11849, hlam]
                          · have p11822_0 := h11822c.1
                            have p11822_1 := h11822c.2.1
                            have p11822_2 := h11822c.2.2.1
                            have p11822_3 := h11822c.2.2.2
                            rcases p11822_3 (m.d 0 1) (by simp) with h11852 | h11852
                            · linarith only [h0, h11852, hlam]
                            · linarith only [h11387, h11852, hlam]
                          · have p11822_0 := h11822c.1
                            have p11822_1 := h11822c.2.1
                            have p11822_2 := h11822c.2.2.1
                            have p11822_3 := h11822c.2.2.2
                            linarith only [h11385, hlam, p11822_0]
                          · have p11822_0 := h11822c.1
                            have p11822_1 := h11822c.2.1
                            have p11822_2 := h11822c.2.2.1
                            have p11822_3 := h11822c.2.2.2
                            linarith only [h11808, hlam, p11822_1]
                          · have p11822_0 := h11822c.1
                            have p11822_1 := h11822c.2.1
                            have p11822_2 := h11822c.2.2.1
                            have p11822_3 := h11822c.2.2.2
                            linarith only [hlam, p11822_0]
                          · have p11822_0 := h11822c.1
                            have p11822_1 := h11822c.2.1
                            have p11822_2 := h11822c.2.2.1
                            have p11822_3 := h11822c.2.2.2
                            linarith only [h11811, hlam, p11822_1]
                          · have p11822_0 := h11822c.1
                            have p11822_1 := h11822c.2.1
                            have p11822_2 := h11822c.2.2.1
                            have p11822_3 := h11822c.2.2.2
                            linarith only [h11813, hlam, p11822_1]
                          · have p11822_0 := h11822c.1
                            have p11822_1 := h11822c.2.1
                            have p11822_2 := h11822c.2.2.1
                            have p11822_3 := h11822c.2.2.2
                            linarith only [h11386, hlam, p11822_0]
                          · have p11822_0 := h11822c.1
                            have p11822_1 := h11822c.2.1
                            have p11822_2 := h11822c.2.2.1
                            have p11822_3 := h11822c.2.2.2
                            linarith only [h11809, hlam, p11822_1]
                          · have p11822_0 := h11822c.1
                            have p11822_1 := h11822c.2.1
                            have p11822_2 := h11822c.2.2.1
                            have p11822_3 := h11822c.2.2.2
                            linarith only [h0, h11386, h11808, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11822_1]
                          · have p11822_0 := h11822c.1
                            have p11822_1 := h11822c.2.1
                            have p11822_2 := h11822c.2.2.1
                            have p11822_3 := h11822c.2.2.2
                            linarith only [hlam, p11822_0]
                          · have p11822_0 := h11822c.1
                            have p11822_1 := h11822c.2.1
                            have p11822_2 := h11822c.2.2.1
                            have p11822_3 := h11822c.2.2.2
                            linarith only [h0, h11386, h11810, h11818, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11822_1]
                          · have p11822_0 := h11822c.1
                            have p11822_1 := h11822c.2.1
                            have p11822_2 := h11822c.2.2.1
                            have p11822_3 := h11822c.2.2.2
                            linarith only [h11387, hlam, p11822_0]
                          · have p11822_0 := h11822c.1
                            have p11822_1 := h11822c.2.1
                            have p11822_2 := h11822c.2.2.1
                            have p11822_3 := h11822c.2.2.2
                            linarith only [h11810, hlam, p11822_1]
                          · have p11822_0 := h11822c.1
                            have p11822_1 := h11822c.2.1
                            have p11822_2 := h11822c.2.2.1
                            have p11822_3 := h11822c.2.2.2
                            linarith only [h0, h11387, h11808, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11822_1]
                          · have p11822_0 := h11822c.1
                            have p11822_1 := h11822c.2.1
                            have p11822_2 := h11822c.2.2.1
                            have p11822_3 := h11822c.2.2.2
                            linarith only [h11815, hlam, p11822_0]
                          · have p11822_0 := h11822c.1
                            have p11822_1 := h11822c.2.1
                            have p11822_2 := h11822c.2.2.1
                            have p11822_3 := h11822c.2.2.2
                            linarith only [hlam, p11822_0]
                        · linarith only [h0, h11385, h11389, h11390, h11808, h11820, h11821, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h11386, h11815, h11820, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11872 | h11872
                  · linarith only [h11386, h11390, h11808, h11811, h11872, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11874 | h11874
                    · linarith only [h11746, h11807, h11808, h11811, h11815, h11874, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11876 | h11876
                      · linarith only [h11809, h11815, h11876, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11878 | h11878
                        · rcases h1bigk with h11879c | h11879c | h11879c | h11879c | h11879c | h11879c | h11879c | h11879c | h11879c | h11879c | h11879c | h11879c | h11879c | h11879c | h11879c | h11879c | h11879c | h11879c | h11879c | h11879c | h11879c | h11879c | h11879c | h11879c | h11879c
                          · have p11879_0 := h11879c.1
                            have p11879_1 := h11879c.2.1
                            have p11879_2 := h11879c.2.2.1
                            have p11879_3 := h11879c.2.2.2
                            linarith only [hlam, p11879_0]
                          · have p11879_0 := h11879c.1
                            have p11879_1 := h11879c.2.1
                            have p11879_2 := h11879c.2.2.1
                            have p11879_3 := h11879c.2.2.2
                            linarith only [h0, hlam, p11879_0]
                          · have p11879_0 := h11879c.1
                            have p11879_1 := h11879c.2.1
                            have p11879_2 := h11879c.2.2.1
                            have p11879_3 := h11879c.2.2.2
                            rcases p11879_3 (m.d 0 1) (by simp) with h11882 | h11882
                            · rcases p11879_3 (m.d 1 2) (by simp) with h11883 | h11883
                              · rcases p11879_3 (m.d 1 3) (by simp) with h11884 | h11884
                                · linarith only [h11884, hlam, p11879_0]
                                · rcases p11879_3 (m.d 1 4) (by simp) with h11886 | h11886
                                  · linarith only [h11386, h11886, hlam]
                                  · linarith only [h11811, h11886, hlam]
                              · linarith only [h11808, h11883, hlam]
                            · linarith only [h11882, hlam, p11879_0]
                          · have p11879_0 := h11879c.1
                            have p11879_1 := h11879c.2.1
                            have p11879_2 := h11879c.2.2.1
                            have p11879_3 := h11879c.2.2.2
                            rcases p11879_3 (m.d 0 1) (by simp) with h11891 | h11891
                            · rcases p11879_3 (m.d 1 2) (by simp) with h11892 | h11892
                              · rcases p11879_3 (m.d 1 3) (by simp) with h11893 | h11893
                                · linarith only [h11385, h11893, hlam]
                                · rcases p11879_3 (m.d 1 4) (by simp) with h11895 | h11895
                                  · linarith only [h11895, hlam, p11879_0]
                                  · rcases p11879_3 (m.d 1 5) (by simp) with h11897 | h11897
                                    · linarith only [h11387, h11897, hlam]
                                    · linarith only [h11815, h11897, hlam]
                              · linarith only [h11809, h11892, hlam]
                            · linarith only [h11891, hlam, p11879_0]
                          · have p11879_0 := h11879c.1
                            have p11879_1 := h11879c.2.1
                            have p11879_2 := h11879c.2.2.1
                            have p11879_3 := h11879c.2.2.2
                            rcases p11879_3 (m.d 0 1) (by simp) with h11902 | h11902
                            · rcases p11879_3 (m.d 1 2) (by simp) with h11903 | h11903
                              · rcases p11879_3 (m.d 1 3) (by simp) with h11904 | h11904
                                · linarith only [h11385, h11904, hlam]
                                · rcases p11879_3 (m.d 1 4) (by simp) with h11906 | h11906
                                  · linarith only [h11386, h11906, hlam]
                                  · rcases p11879_3 (m.d 1 5) (by simp) with h11908 | h11908
                                    · linarith only [h11908, hlam, p11879_0]
                                    · rcases h3bigk with h11910c | h11910c | h11910c | h11910c | h11910c | h11910c | h11910c | h11910c | h11910c | h11910c | h11910c | h11910c | h11910c | h11910c | h11910c | h11910c | h11910c | h11910c | h11910c | h11910c | h11910c | h11910c | h11910c | h11910c | h11910c
                                      · have p11910_0 := h11910c.1
                                        have p11910_1 := h11910c.2.1
                                        have p11910_2 := h11910c.2.2.1
                                        have p11910_3 := h11910c.2.2.2
                                        linarith only [hlam, p11910_0]
                                      · have p11910_0 := h11910c.1
                                        have p11910_1 := h11910c.2.1
                                        have p11910_2 := h11910c.2.2.1
                                        have p11910_3 := h11910c.2.2.2
                                        linarith only [h0, h11385, h11808, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11910_1]
                                      · have p11910_0 := h11910c.1
                                        have p11910_1 := h11910c.2.1
                                        have p11910_2 := h11910c.2.2.1
                                        have p11910_3 := h11910c.2.2.2
                                        linarith only [h0, h11385, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11910_1]
                                      · have p11910_0 := h11910c.1
                                        have p11910_1 := h11910c.2.1
                                        have p11910_2 := h11910c.2.2.1
                                        have p11910_3 := h11910c.2.2.2
                                        linarith only [h11390, hlam, p11910_0]
                                      · have p11910_0 := h11910c.1
                                        have p11910_1 := h11910c.2.1
                                        have p11910_2 := h11910c.2.2.1
                                        have p11910_3 := h11910c.2.2.2
                                        linarith only [h11746, hlam, p11910_0]
                                      · have p11910_0 := h11910c.1
                                        have p11910_1 := h11910c.2.1
                                        have p11910_2 := h11910c.2.2.1
                                        have p11910_3 := h11910c.2.2.2
                                        linarith only [h11385, hlam, p11910_0]
                                      · have p11910_0 := h11910c.1
                                        have p11910_1 := h11910c.2.1
                                        have p11910_2 := h11910c.2.2.1
                                        have p11910_3 := h11910c.2.2.2
                                        linarith only [hlam, p11910_0]
                                      · have p11910_0 := h11910c.1
                                        have p11910_1 := h11910c.2.1
                                        have p11910_2 := h11910c.2.2.1
                                        have p11910_3 := h11910c.2.2.2
                                        linarith only [h0, h11385, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11910_1]
                                      · have p11910_0 := h11910c.1
                                        have p11910_1 := h11910c.2.1
                                        have p11910_2 := h11910c.2.2.1
                                        have p11910_3 := h11910c.2.2.2
                                        linarith only [h11811, hlam, p11910_0]
                                      · have p11910_0 := h11910c.1
                                        have p11910_1 := h11910c.2.1
                                        have p11910_2 := h11910c.2.2.1
                                        have p11910_3 := h11910c.2.2.2
                                        linarith only [h11813, hlam, p11910_0]
                                      · have p11910_0 := h11910c.1
                                        have p11910_1 := h11910c.2.1
                                        have p11910_2 := h11910c.2.2.1
                                        have p11910_3 := h11910c.2.2.2
                                        linarith only [h11388, hlam, p11910_0]
                                      · have p11910_0 := h11910c.1
                                        have p11910_1 := h11910c.2.1
                                        have p11910_2 := h11910c.2.2.1
                                        have p11910_3 := h11910c.2.2.2
                                        linarith only [h11808, hlam, p11910_0]
                                      · have p11910_0 := h11910c.1
                                        have p11910_1 := h11910c.2.1
                                        have p11910_2 := h11910c.2.2.1
                                        have p11910_3 := h11910c.2.2.2
                                        linarith only [hlam, p11910_0]
                                      · have p11910_0 := h11910c.1
                                        have p11910_1 := h11910c.2.1
                                        have p11910_2 := h11910c.2.2.1
                                        have p11910_3 := h11910c.2.2.2
                                        linarith only [h11872, hlam, p11910_0]
                                      · have p11910_0 := h11910c.1
                                        have p11910_1 := h11910c.2.1
                                        have p11910_2 := h11910c.2.2.1
                                        have p11910_3 := h11910c.2.2.2
                                        linarith only [h11874, hlam, p11910_0]
                                      · have p11910_0 := h11910c.1
                                        have p11910_1 := h11910c.2.1
                                        have p11910_2 := h11910c.2.2.1
                                        have p11910_3 := h11910c.2.2.2
                                        linarith only [hc03, hc34, hlam, hphi, p11910_1]
                                      · have p11910_0 := h11910c.1
                                        have p11910_1 := h11910c.2.1
                                        have p11910_2 := h11910c.2.2.1
                                        have p11910_3 := h11910c.2.2.2
                                        linarith only [hc13, hc34, hlam, hphi, p11910_1]
                                      · have p11910_0 := h11910c.1
                                        have p11910_1 := h11910c.2.1
                                        have p11910_2 := h11910c.2.2.1
                                        have p11910_3 := h11910c.2.2.2
                                        linarith only [hc23, hc34, hlam, hphi, p11910_1]
                                      · have p11910_0 := h11910c.1
                                        have p11910_1 := h11910c.2.1
                                        have p11910_2 := h11910c.2.2.1
                                        have p11910_3 := h11910c.2.2.2
                                        linarith only [hlam, p11910_0]
                                      · have p11910_0 := h11910c.1
                                        have p11910_1 := h11910c.2.1
                                        have p11910_2 := h11910c.2.2.1
                                        have p11910_3 := h11910c.2.2.2
                                        linarith only [h11385, h11746, h11808, hc23, hc34, hlam, hphi, p11910_1]
                                      · have p11910_0 := h11910c.1
                                        have p11910_1 := h11910c.2.1
                                        have p11910_2 := h11910c.2.2.1
                                        have p11910_3 := h11910c.2.2.2
                                        linarith only [h11385, h11808, hc23, hc35, hlam, hphi, p11910_1]
                                      · have p11910_0 := h11910c.1
                                        have p11910_1 := h11910c.2.1
                                        have p11910_2 := h11910c.2.2.1
                                        have p11910_3 := h11910c.2.2.2
                                        linarith only [h11808, hc23, hc35, hlam, hphi, p11910_1]
                                      · have p11910_0 := h11910c.1
                                        have p11910_1 := h11910c.2.1
                                        have p11910_2 := h11910c.2.2.1
                                        have p11910_3 := h11910c.2.2.2
                                        linarith only [hc23, hc35, hlam, hphi, p11910_1]
                                      · have p11910_0 := h11910c.1
                                        have p11910_1 := h11910c.2.1
                                        have p11910_2 := h11910c.2.2.1
                                        have p11910_3 := h11910c.2.2.2
                                        linarith only [h11878, hlam, p11910_0]
                                      · have p11910_0 := h11910c.1
                                        have p11910_1 := h11910c.2.1
                                        have p11910_2 := h11910c.2.2.1
                                        have p11910_3 := h11910c.2.2.2
                                        linarith only [hlam, p11910_0]
                              · linarith only [h11810, h11903, hlam]
                            · linarith only [h11902, hlam, p11879_0]
                          · have p11879_0 := h11879c.1
                            have p11879_1 := h11879c.2.1
                            have p11879_2 := h11879c.2.2.1
                            have p11879_3 := h11879c.2.2.2
                            linarith only [h11386, h11807, h11815, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p11879_1]
                          · have p11879_0 := h11879c.1
                            have p11879_1 := h11879c.2.1
                            have p11879_2 := h11879c.2.2.1
                            have p11879_3 := h11879c.2.2.2
                            linarith only [hlam, p11879_0]
                          · have p11879_0 := h11879c.1
                            have p11879_1 := h11879c.2.1
                            have p11879_2 := h11879c.2.2.1
                            have p11879_3 := h11879c.2.2.2
                            linarith only [h0, h11386, h11807, h11811, h11815, hlam, p11879_2]
                          · have p11879_0 := h11879c.1
                            have p11879_1 := h11879c.2.1
                            have p11879_2 := h11879c.2.2.1
                            have p11879_3 := h11879c.2.2.2
                            linarith only [h0, h11386, h11807, h11815, hlam, p11879_2]
                          · have p11879_0 := h11879c.1
                            have p11879_1 := h11879c.2.1
                            have p11879_2 := h11879c.2.2.1
                            have p11879_3 := h11879c.2.2.2
                            rcases p11879_3 (m.d 0 1) (by simp) with h11942 | h11942
                            · linarith only [h0, h11942, hlam]
                            · linarith only [h11387, h11942, hlam]
                          · have p11879_0 := h11879c.1
                            have p11879_1 := h11879c.2.1
                            have p11879_2 := h11879c.2.2.1
                            have p11879_3 := h11879c.2.2.2
                            linarith only [h11385, hlam, p11879_0]
                          · have p11879_0 := h11879c.1
                            have p11879_1 := h11879c.2.1
                            have p11879_2 := h11879c.2.2.1
                            have p11879_3 := h11879c.2.2.2
                            linarith only [h11808, hlam, p11879_1]
                          · have p11879_0 := h11879c.1
                            have p11879_1 := h11879c.2.1
                            have p11879_2 := h11879c.2.2.1
                            have p11879_3 := h11879c.2.2.2
                            linarith only [hlam, p11879_0]
                          · have p11879_0 := h11879c.1
                            have p11879_1 := h11879c.2.1
                            have p11879_2 := h11879c.2.2.1
                            have p11879_3 := h11879c.2.2.2
                            linarith only [h11811, hlam, p11879_1]
                          · have p11879_0 := h11879c.1
                            have p11879_1 := h11879c.2.1
                            have p11879_2 := h11879c.2.2.1
                            have p11879_3 := h11879c.2.2.2
                            linarith only [h11813, hlam, p11879_1]
                          · have p11879_0 := h11879c.1
                            have p11879_1 := h11879c.2.1
                            have p11879_2 := h11879c.2.2.1
                            have p11879_3 := h11879c.2.2.2
                            linarith only [h11386, hlam, p11879_0]
                          · have p11879_0 := h11879c.1
                            have p11879_1 := h11879c.2.1
                            have p11879_2 := h11879c.2.2.1
                            have p11879_3 := h11879c.2.2.2
                            linarith only [h11809, hlam, p11879_1]
                          · have p11879_0 := h11879c.1
                            have p11879_1 := h11879c.2.1
                            have p11879_2 := h11879c.2.2.1
                            have p11879_3 := h11879c.2.2.2
                            linarith only [h11386, h11807, h11808, h11815, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11879_1]
                          · have p11879_0 := h11879c.1
                            have p11879_1 := h11879c.2.1
                            have p11879_2 := h11879c.2.2.1
                            have p11879_3 := h11879c.2.2.2
                            linarith only [hlam, p11879_0]
                          · have p11879_0 := h11879c.1
                            have p11879_1 := h11879c.2.1
                            have p11879_2 := h11879c.2.2.1
                            have p11879_3 := h11879c.2.2.2
                            linarith only [h11815, hlam, p11879_1]
                          · have p11879_0 := h11879c.1
                            have p11879_1 := h11879c.2.1
                            have p11879_2 := h11879c.2.2.1
                            have p11879_3 := h11879c.2.2.2
                            linarith only [h11387, hlam, p11879_0]
                          · have p11879_0 := h11879c.1
                            have p11879_1 := h11879c.2.1
                            have p11879_2 := h11879c.2.2.1
                            have p11879_3 := h11879c.2.2.2
                            linarith only [h11810, hlam, p11879_1]
                          · have p11879_0 := h11879c.1
                            have p11879_1 := h11879c.2.1
                            have p11879_2 := h11879c.2.2.1
                            have p11879_3 := h11879c.2.2.2
                            linarith only [h0, h11387, h11808, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11879_1]
                          · have p11879_0 := h11879c.1
                            have p11879_1 := h11879c.2.1
                            have p11879_2 := h11879c.2.2.1
                            have p11879_3 := h11879c.2.2.2
                            linarith only [h0, h11386, h11807, h11815, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p11879_1]
                          · have p11879_0 := h11879c.1
                            have p11879_1 := h11879c.2.1
                            have p11879_2 := h11879c.2.2.1
                            have p11879_3 := h11879c.2.2.2
                            linarith only [hlam, p11879_0]
                        · linarith only [h0, h11385, h11386, h11390, h11807, h11808, h11878, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
          · linarith only [h0, h11387, h11810, hlam]
        · linarith only [h0, h11389, h11809, hlam]
      · linarith only [h0, h11388, h11808, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h11964 | h11964
      · rcases m.htr 1 2 4 (by decide) (by decide) with h11965 | h11965
        · rcases m.htr 1 2 5 (by decide) (by decide) with h11966 | h11966
          · rcases m.htr 1 3 4 (by decide) (by decide) with h11967 | h11967
            · linarith only [h11385, h11390, h11967, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11969 | h11969
              · linarith only [h11385, h11746, h11969, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11971 | h11971
                · linarith only [h0, h11386, h11390, h11807, h11971, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11973 | h11973
                  · linarith only [h11385, h11390, h11964, h11973, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11975 | h11975
                    · linarith only [h11385, h11746, h11964, h11975, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11977 | h11977
                      · linarith only [h11386, h11807, h11965, h11977, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11979 | h11979
                        · rcases h1bigk with h11980c | h11980c | h11980c | h11980c | h11980c | h11980c | h11980c | h11980c | h11980c | h11980c | h11980c | h11980c | h11980c | h11980c | h11980c | h11980c | h11980c | h11980c | h11980c | h11980c | h11980c | h11980c | h11980c | h11980c | h11980c
                          · have p11980_0 := h11980c.1
                            have p11980_1 := h11980c.2.1
                            have p11980_2 := h11980c.2.2.1
                            have p11980_3 := h11980c.2.2.2
                            linarith only [hlam, p11980_0]
                          · have p11980_0 := h11980c.1
                            have p11980_1 := h11980c.2.1
                            have p11980_2 := h11980c.2.2.1
                            have p11980_3 := h11980c.2.2.2
                            linarith only [h0, hlam, p11980_0]
                          · have p11980_0 := h11980c.1
                            have p11980_1 := h11980c.2.1
                            have p11980_2 := h11980c.2.2.1
                            have p11980_3 := h11980c.2.2.2
                            rcases p11980_3 (m.d 0 1) (by simp) with h11983 | h11983
                            · rcases p11980_3 (m.d 1 2) (by simp) with h11984 | h11984
                              · rcases p11980_3 (m.d 1 3) (by simp) with h11985 | h11985
                                · linarith only [h11985, hlam, p11980_0]
                                · rcases p11980_3 (m.d 1 4) (by simp) with h11987 | h11987
                                  · linarith only [h11386, h11987, hlam]
                                  · linarith only [h11967, h11987, hlam]
                              · linarith only [h11964, h11984, hlam]
                            · linarith only [h11983, hlam, p11980_0]
                          · have p11980_0 := h11980c.1
                            have p11980_1 := h11980c.2.1
                            have p11980_2 := h11980c.2.2.1
                            have p11980_3 := h11980c.2.2.2
                            rcases p11980_3 (m.d 0 1) (by simp) with h11992 | h11992
                            · rcases p11980_3 (m.d 1 2) (by simp) with h11993 | h11993
                              · rcases p11980_3 (m.d 1 3) (by simp) with h11994 | h11994
                                · linarith only [h11385, h11994, hlam]
                                · rcases p11980_3 (m.d 1 4) (by simp) with h11996 | h11996
                                  · linarith only [h11996, hlam, p11980_0]
                                  · rcases p11980_3 (m.d 1 5) (by simp) with h11998 | h11998
                                    · linarith only [h11387, h11998, hlam]
                                    · linarith only [h11971, h11998, hlam]
                              · linarith only [h11965, h11993, hlam]
                            · linarith only [h11992, hlam, p11980_0]
                          · have p11980_0 := h11980c.1
                            have p11980_1 := h11980c.2.1
                            have p11980_2 := h11980c.2.2.1
                            have p11980_3 := h11980c.2.2.2
                            rcases p11980_3 (m.d 0 1) (by simp) with h12003 | h12003
                            · rcases p11980_3 (m.d 1 2) (by simp) with h12004 | h12004
                              · rcases p11980_3 (m.d 1 3) (by simp) with h12005 | h12005
                                · linarith only [h11385, h12005, hlam]
                                · rcases p11980_3 (m.d 1 4) (by simp) with h12007 | h12007
                                  · linarith only [h11386, h12007, hlam]
                                  · rcases p11980_3 (m.d 1 5) (by simp) with h12009 | h12009
                                    · linarith only [h12009, hlam, p11980_0]
                                    · rcases h3bigk with h12011c | h12011c | h12011c | h12011c | h12011c | h12011c | h12011c | h12011c | h12011c | h12011c | h12011c | h12011c | h12011c | h12011c | h12011c | h12011c | h12011c | h12011c | h12011c | h12011c | h12011c | h12011c | h12011c | h12011c | h12011c
                                      · have p12011_0 := h12011c.1
                                        have p12011_1 := h12011c.2.1
                                        have p12011_2 := h12011c.2.2.1
                                        have p12011_3 := h12011c.2.2.2
                                        linarith only [hlam, p12011_0]
                                      · have p12011_0 := h12011c.1
                                        have p12011_1 := h12011c.2.1
                                        have p12011_2 := h12011c.2.2.1
                                        have p12011_3 := h12011c.2.2.2
                                        linarith only [h11390, h11807, h11964, h11979, hc23, hc34, hlam, hphi, p12011_1]
                                      · have p12011_0 := h12011c.1
                                        have p12011_1 := h12011c.2.1
                                        have p12011_2 := h12011c.2.2.1
                                        have p12011_3 := h12011c.2.2.2
                                        linarith only [h11390, h11807, h11979, hc23, hc34, hlam, hphi, p12011_1]
                                      · have p12011_0 := h12011c.1
                                        have p12011_1 := h12011c.2.1
                                        have p12011_2 := h12011c.2.2.1
                                        have p12011_3 := h12011c.2.2.2
                                        linarith only [h11390, hlam, p12011_0]
                                      · have p12011_0 := h12011c.1
                                        have p12011_1 := h12011c.2.1
                                        have p12011_2 := h12011c.2.2.1
                                        have p12011_3 := h12011c.2.2.2
                                        linarith only [h11746, hlam, p12011_0]
                                      · have p12011_0 := h12011c.1
                                        have p12011_1 := h12011c.2.1
                                        have p12011_2 := h12011c.2.2.1
                                        have p12011_3 := h12011c.2.2.2
                                        linarith only [h11385, hlam, p12011_0]
                                      · have p12011_0 := h12011c.1
                                        have p12011_1 := h12011c.2.1
                                        have p12011_2 := h12011c.2.2.1
                                        have p12011_3 := h12011c.2.2.2
                                        linarith only [hlam, p12011_0]
                                      · have p12011_0 := h12011c.1
                                        have p12011_1 := h12011c.2.1
                                        have p12011_2 := h12011c.2.2.1
                                        have p12011_3 := h12011c.2.2.2
                                        linarith only [h0, h11385, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12011_1]
                                      · have p12011_0 := h12011c.1
                                        have p12011_1 := h12011c.2.1
                                        have p12011_2 := h12011c.2.2.1
                                        have p12011_3 := h12011c.2.2.2
                                        linarith only [h11967, hlam, p12011_0]
                                      · have p12011_0 := h12011c.1
                                        have p12011_1 := h12011c.2.1
                                        have p12011_2 := h12011c.2.2.1
                                        have p12011_3 := h12011c.2.2.2
                                        linarith only [h11969, hlam, p12011_0]
                                      · have p12011_0 := h12011c.1
                                        have p12011_1 := h12011c.2.1
                                        have p12011_2 := h12011c.2.2.1
                                        have p12011_3 := h12011c.2.2.2
                                        linarith only [h11388, hlam, p12011_0]
                                      · have p12011_0 := h12011c.1
                                        have p12011_1 := h12011c.2.1
                                        have p12011_2 := h12011c.2.2.1
                                        have p12011_3 := h12011c.2.2.2
                                        linarith only [h11964, hlam, p12011_0]
                                      · have p12011_0 := h12011c.1
                                        have p12011_1 := h12011c.2.1
                                        have p12011_2 := h12011c.2.2.1
                                        have p12011_3 := h12011c.2.2.2
                                        linarith only [hlam, p12011_0]
                                      · have p12011_0 := h12011c.1
                                        have p12011_1 := h12011c.2.1
                                        have p12011_2 := h12011c.2.2.1
                                        have p12011_3 := h12011c.2.2.2
                                        linarith only [h11973, hlam, p12011_0]
                                      · have p12011_0 := h12011c.1
                                        have p12011_1 := h12011c.2.1
                                        have p12011_2 := h12011c.2.2.1
                                        have p12011_3 := h12011c.2.2.2
                                        linarith only [h11975, hlam, p12011_0]
                                      · have p12011_0 := h12011c.1
                                        have p12011_1 := h12011c.2.1
                                        have p12011_2 := h12011c.2.2.1
                                        have p12011_3 := h12011c.2.2.2
                                        linarith only [hc03, hc34, hlam, hphi, p12011_1]
                                      · have p12011_0 := h12011c.1
                                        have p12011_1 := h12011c.2.1
                                        have p12011_2 := h12011c.2.2.1
                                        have p12011_3 := h12011c.2.2.2
                                        linarith only [h11964, hc23, hc34, hlam, hphi, p12011_1]
                                      · have p12011_0 := h12011c.1
                                        have p12011_1 := h12011c.2.1
                                        have p12011_2 := h12011c.2.2.1
                                        have p12011_3 := h12011c.2.2.2
                                        linarith only [hc23, hc34, hlam, hphi, p12011_1]
                                      · have p12011_0 := h12011c.1
                                        have p12011_1 := h12011c.2.1
                                        have p12011_2 := h12011c.2.2.1
                                        have p12011_3 := h12011c.2.2.2
                                        linarith only [hlam, p12011_0]
                                      · have p12011_0 := h12011c.1
                                        have p12011_1 := h12011c.2.1
                                        have p12011_2 := h12011c.2.2.1
                                        have p12011_3 := h12011c.2.2.2
                                        linarith only [h11807, h11979, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p12011_1]
                                      · have p12011_0 := h12011c.1
                                        have p12011_1 := h12011c.2.1
                                        have p12011_2 := h12011c.2.2.1
                                        have p12011_3 := h12011c.2.2.2
                                        linarith only [h11385, h11964, hc23, hc35, hlam, hphi, p12011_1]
                                      · have p12011_0 := h12011c.1
                                        have p12011_1 := h12011c.2.1
                                        have p12011_2 := h12011c.2.2.1
                                        have p12011_3 := h12011c.2.2.2
                                        linarith only [h11964, hc23, hc35, hlam, hphi, p12011_1]
                                      · have p12011_0 := h12011c.1
                                        have p12011_1 := h12011c.2.1
                                        have p12011_2 := h12011c.2.2.1
                                        have p12011_3 := h12011c.2.2.2
                                        linarith only [hc23, hc35, hlam, hphi, p12011_1]
                                      · have p12011_0 := h12011c.1
                                        have p12011_1 := h12011c.2.1
                                        have p12011_2 := h12011c.2.2.1
                                        have p12011_3 := h12011c.2.2.2
                                        linarith only [h11979, hlam, p12011_0]
                                      · have p12011_0 := h12011c.1
                                        have p12011_1 := h12011c.2.1
                                        have p12011_2 := h12011c.2.2.1
                                        have p12011_3 := h12011c.2.2.2
                                        linarith only [hlam, p12011_0]
                              · linarith only [h11966, h12004, hlam]
                            · linarith only [h12003, hlam, p11980_0]
                          · have p11980_0 := h11980c.1
                            have p11980_1 := h11980c.2.1
                            have p11980_2 := h11980c.2.2.1
                            have p11980_3 := h11980c.2.2.2
                            rcases p11980_3 (m.d 0 1) (by simp) with h12039 | h12039
                            · linarith only [h12039, hlam, p11980_0]
                            · rcases p11980_3 (m.d 1 2) (by simp) with h12041 | h12041
                              · rcases p11980_3 (m.d 1 3) (by simp) with h12042 | h12042
                                · linarith only [h11964, h12042, hlam]
                                · rcases p11980_3 (m.d 1 4) (by simp) with h12044 | h12044
                                  · linarith only [h11965, h12044, hlam]
                                  · rcases p11980_3 (m.d 1 5) (by simp) with h12046 | h12046
                                    · linarith only [h11966, h12046, hlam]
                                    · rcases h3bigk with h12048c | h12048c | h12048c | h12048c | h12048c | h12048c | h12048c | h12048c | h12048c | h12048c | h12048c | h12048c | h12048c | h12048c | h12048c | h12048c | h12048c | h12048c | h12048c | h12048c | h12048c | h12048c | h12048c | h12048c | h12048c
                                      · have p12048_0 := h12048c.1
                                        have p12048_1 := h12048c.2.1
                                        have p12048_2 := h12048c.2.2.1
                                        have p12048_3 := h12048c.2.2.2
                                        linarith only [hlam, p12048_0]
                                      · have p12048_0 := h12048c.1
                                        have p12048_1 := h12048c.2.1
                                        have p12048_2 := h12048c.2.2.1
                                        have p12048_3 := h12048c.2.2.2
                                        linarith only [h11390, h11807, h11964, hc23, hc45, hlam, hphi, ht34, p12048_1]
                                      · have p12048_0 := h12048c.1
                                        have p12048_1 := h12048c.2.1
                                        have p12048_2 := h12048c.2.2.1
                                        have p12048_3 := h12048c.2.2.2
                                        linarith only [h11385, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11980_1, p12048_1]
                                      · have p12048_0 := h12048c.1
                                        have p12048_1 := h12048c.2.1
                                        have p12048_2 := h12048c.2.2.1
                                        have p12048_3 := h12048c.2.2.2
                                        linarith only [h11390, hlam, p12048_0]
                                      · have p12048_0 := h12048c.1
                                        have p12048_1 := h12048c.2.1
                                        have p12048_2 := h12048c.2.2.1
                                        have p12048_3 := h12048c.2.2.2
                                        linarith only [h11746, hlam, p12048_0]
                                      · have p12048_0 := h12048c.1
                                        have p12048_1 := h12048c.2.1
                                        have p12048_2 := h12048c.2.2.1
                                        have p12048_3 := h12048c.2.2.2
                                        linarith only [h11385, hlam, p12048_0]
                                      · have p12048_0 := h12048c.1
                                        have p12048_1 := h12048c.2.1
                                        have p12048_2 := h12048c.2.2.1
                                        have p12048_3 := h12048c.2.2.2
                                        linarith only [hlam, p12048_0]
                                      · have p12048_0 := h12048c.1
                                        have p12048_1 := h12048c.2.1
                                        have p12048_2 := h12048c.2.2.1
                                        have p12048_3 := h12048c.2.2.2
                                        linarith only [h11385, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11980_1, p12048_1]
                                      · have p12048_0 := h12048c.1
                                        have p12048_1 := h12048c.2.1
                                        have p12048_2 := h12048c.2.2.1
                                        have p12048_3 := h12048c.2.2.2
                                        linarith only [h11967, hlam, p12048_0]
                                      · have p12048_0 := h12048c.1
                                        have p12048_1 := h12048c.2.1
                                        have p12048_2 := h12048c.2.2.1
                                        have p12048_3 := h12048c.2.2.2
                                        linarith only [h11969, hlam, p12048_0]
                                      · have p12048_0 := h12048c.1
                                        have p12048_1 := h12048c.2.1
                                        have p12048_2 := h12048c.2.2.1
                                        have p12048_3 := h12048c.2.2.2
                                        linarith only [h11388, hlam, p12048_0]
                                      · have p12048_0 := h12048c.1
                                        have p12048_1 := h12048c.2.1
                                        have p12048_2 := h12048c.2.2.1
                                        have p12048_3 := h12048c.2.2.2
                                        linarith only [h11964, hlam, p12048_0]
                                      · have p12048_0 := h12048c.1
                                        have p12048_1 := h12048c.2.1
                                        have p12048_2 := h12048c.2.2.1
                                        have p12048_3 := h12048c.2.2.2
                                        linarith only [hlam, p12048_0]
                                      · have p12048_0 := h12048c.1
                                        have p12048_1 := h12048c.2.1
                                        have p12048_2 := h12048c.2.2.1
                                        have p12048_3 := h12048c.2.2.2
                                        linarith only [h11973, hlam, p12048_0]
                                      · have p12048_0 := h12048c.1
                                        have p12048_1 := h12048c.2.1
                                        have p12048_2 := h12048c.2.2.1
                                        have p12048_3 := h12048c.2.2.2
                                        linarith only [h11975, hlam, p12048_0]
                                      · have p12048_0 := h12048c.1
                                        have p12048_1 := h12048c.2.1
                                        have p12048_2 := h12048c.2.2.1
                                        have p12048_3 := h12048c.2.2.2
                                        linarith only [hc03, hc34, hlam, hphi, p12048_1]
                                      · have p12048_0 := h12048c.1
                                        have p12048_1 := h12048c.2.1
                                        have p12048_2 := h12048c.2.2.1
                                        have p12048_3 := h12048c.2.2.2
                                        linarith only [h11964, hc23, hc34, hlam, hphi, p12048_1]
                                      · have p12048_0 := h12048c.1
                                        have p12048_1 := h12048c.2.1
                                        have p12048_2 := h12048c.2.2.1
                                        have p12048_3 := h12048c.2.2.2
                                        linarith only [hc23, hc34, hlam, hphi, p12048_1]
                                      · have p12048_0 := h12048c.1
                                        have p12048_1 := h12048c.2.1
                                        have p12048_2 := h12048c.2.2.1
                                        have p12048_3 := h12048c.2.2.2
                                        linarith only [hlam, p12048_0]
                                      · have p12048_0 := h12048c.1
                                        have p12048_1 := h12048c.2.1
                                        have p12048_2 := h12048c.2.2.1
                                        have p12048_3 := h12048c.2.2.2
                                        linarith only [h11385, h11746, h11964, hc23, hc34, hlam, hphi, p12048_1]
                                      · have p12048_0 := h12048c.1
                                        have p12048_1 := h12048c.2.1
                                        have p12048_2 := h12048c.2.2.1
                                        have p12048_3 := h12048c.2.2.2
                                        linarith only [h11385, h11964, hc23, hc35, hlam, hphi, p12048_1]
                                      · have p12048_0 := h12048c.1
                                        have p12048_1 := h12048c.2.1
                                        have p12048_2 := h12048c.2.2.1
                                        have p12048_3 := h12048c.2.2.2
                                        linarith only [h11964, hc23, hc35, hlam, hphi, p12048_1]
                                      · have p12048_0 := h12048c.1
                                        have p12048_1 := h12048c.2.1
                                        have p12048_2 := h12048c.2.2.1
                                        have p12048_3 := h12048c.2.2.2
                                        linarith only [hc23, hc35, hlam, hphi, p12048_1]
                                      · have p12048_0 := h12048c.1
                                        have p12048_1 := h12048c.2.1
                                        have p12048_2 := h12048c.2.2.1
                                        have p12048_3 := h12048c.2.2.2
                                        linarith only [h11979, hlam, p12048_0]
                                      · have p12048_0 := h12048c.1
                                        have p12048_1 := h12048c.2.1
                                        have p12048_2 := h12048c.2.2.1
                                        have p12048_3 := h12048c.2.2.2
                                        linarith only [hlam, p12048_0]
                              · linarith only [h12041, hlam, p11980_0]
                          · have p11980_0 := h11980c.1
                            have p11980_1 := h11980c.2.1
                            have p11980_2 := h11980c.2.2.1
                            have p11980_3 := h11980c.2.2.2
                            linarith only [hlam, p11980_0]
                          · have p11980_0 := h11980c.1
                            have p11980_1 := h11980c.2.1
                            have p11980_2 := h11980c.2.2.1
                            have p11980_3 := h11980c.2.2.2
                            rcases p11980_3 (m.d 0 1) (by simp) with h12076 | h12076
                            · linarith only [h0, h12076, hlam]
                            · linarith only [h11385, h12076, hlam]
                          · have p11980_0 := h11980c.1
                            have p11980_1 := h11980c.2.1
                            have p11980_2 := h11980c.2.2.1
                            have p11980_3 := h11980c.2.2.2
                            rcases p11980_3 (m.d 0 1) (by simp) with h12079 | h12079
                            · linarith only [h0, h12079, hlam]
                            · linarith only [h11386, h12079, hlam]
                          · have p11980_0 := h11980c.1
                            have p11980_1 := h11980c.2.1
                            have p11980_2 := h11980c.2.2.1
                            have p11980_3 := h11980c.2.2.2
                            rcases p11980_3 (m.d 0 1) (by simp) with h12082 | h12082
                            · linarith only [h0, h12082, hlam]
                            · linarith only [h11387, h12082, hlam]
                          · have p11980_0 := h11980c.1
                            have p11980_1 := h11980c.2.1
                            have p11980_2 := h11980c.2.2.1
                            have p11980_3 := h11980c.2.2.2
                            linarith only [h11385, hlam, p11980_0]
                          · have p11980_0 := h11980c.1
                            have p11980_1 := h11980c.2.1
                            have p11980_2 := h11980c.2.2.1
                            have p11980_3 := h11980c.2.2.2
                            linarith only [h11964, hlam, p11980_1]
                          · have p11980_0 := h11980c.1
                            have p11980_1 := h11980c.2.1
                            have p11980_2 := h11980c.2.2.1
                            have p11980_3 := h11980c.2.2.2
                            linarith only [hlam, p11980_0]
                          · have p11980_0 := h11980c.1
                            have p11980_1 := h11980c.2.1
                            have p11980_2 := h11980c.2.2.1
                            have p11980_3 := h11980c.2.2.2
                            linarith only [h11967, hlam, p11980_1]
                          · have p11980_0 := h11980c.1
                            have p11980_1 := h11980c.2.1
                            have p11980_2 := h11980c.2.2.1
                            have p11980_3 := h11980c.2.2.2
                            linarith only [h11969, hlam, p11980_1]
                          · have p11980_0 := h11980c.1
                            have p11980_1 := h11980c.2.1
                            have p11980_2 := h11980c.2.2.1
                            have p11980_3 := h11980c.2.2.2
                            linarith only [h11386, hlam, p11980_0]
                          · have p11980_0 := h11980c.1
                            have p11980_1 := h11980c.2.1
                            have p11980_2 := h11980c.2.2.1
                            have p11980_3 := h11980c.2.2.2
                            linarith only [h11965, hlam, p11980_1]
                          · have p11980_0 := h11980c.1
                            have p11980_1 := h11980c.2.1
                            have p11980_2 := h11980c.2.2.1
                            have p11980_3 := h11980c.2.2.2
                            linarith only [h0, h11387, h11971, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11980_1]
                          · have p11980_0 := h11980c.1
                            have p11980_1 := h11980c.2.1
                            have p11980_2 := h11980c.2.2.1
                            have p11980_3 := h11980c.2.2.2
                            linarith only [hlam, p11980_0]
                          · have p11980_0 := h11980c.1
                            have p11980_1 := h11980c.2.1
                            have p11980_2 := h11980c.2.2.1
                            have p11980_3 := h11980c.2.2.2
                            linarith only [h11971, hlam, p11980_1]
                          · have p11980_0 := h11980c.1
                            have p11980_1 := h11980c.2.1
                            have p11980_2 := h11980c.2.2.1
                            have p11980_3 := h11980c.2.2.2
                            linarith only [h11387, hlam, p11980_0]
                          · have p11980_0 := h11980c.1
                            have p11980_1 := h11980c.2.1
                            have p11980_2 := h11980c.2.2.1
                            have p11980_3 := h11980c.2.2.2
                            linarith only [h11966, hlam, p11980_1]
                          · have p11980_0 := h11980c.1
                            have p11980_1 := h11980c.2.1
                            have p11980_2 := h11980c.2.2.1
                            have p11980_3 := h11980c.2.2.2
                            linarith only [h0, h11387, h11964, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11980_1]
                          · have p11980_0 := h11980c.1
                            have p11980_1 := h11980c.2.1
                            have p11980_2 := h11980c.2.2.1
                            have p11980_3 := h11980c.2.2.2
                            linarith only [h0, h11387, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p11980_1]
                          · have p11980_0 := h11980c.1
                            have p11980_1 := h11980c.2.1
                            have p11980_2 := h11980c.2.2.1
                            have p11980_3 := h11980c.2.2.2
                            linarith only [hlam, p11980_0]
                        · rcases h1bigk with h12100c | h12100c | h12100c | h12100c | h12100c | h12100c | h12100c | h12100c | h12100c | h12100c | h12100c | h12100c | h12100c | h12100c | h12100c | h12100c | h12100c | h12100c | h12100c | h12100c | h12100c | h12100c | h12100c | h12100c | h12100c
                          · have p12100_0 := h12100c.1
                            have p12100_1 := h12100c.2.1
                            have p12100_2 := h12100c.2.2.1
                            have p12100_3 := h12100c.2.2.2
                            linarith only [hlam, p12100_0]
                          · have p12100_0 := h12100c.1
                            have p12100_1 := h12100c.2.1
                            have p12100_2 := h12100c.2.2.1
                            have p12100_3 := h12100c.2.2.2
                            linarith only [h0, hlam, p12100_0]
                          · have p12100_0 := h12100c.1
                            have p12100_1 := h12100c.2.1
                            have p12100_2 := h12100c.2.2.1
                            have p12100_3 := h12100c.2.2.2
                            rcases p12100_3 (m.d 0 1) (by simp) with h12103 | h12103
                            · rcases p12100_3 (m.d 1 2) (by simp) with h12104 | h12104
                              · rcases p12100_3 (m.d 1 3) (by simp) with h12105 | h12105
                                · linarith only [h12105, hlam, p12100_0]
                                · rcases p12100_3 (m.d 1 4) (by simp) with h12107 | h12107
                                  · linarith only [h11386, h12107, hlam]
                                  · linarith only [h11967, h12107, hlam]
                              · linarith only [h11964, h12104, hlam]
                            · linarith only [h12103, hlam, p12100_0]
                          · have p12100_0 := h12100c.1
                            have p12100_1 := h12100c.2.1
                            have p12100_2 := h12100c.2.2.1
                            have p12100_3 := h12100c.2.2.2
                            rcases p12100_3 (m.d 0 1) (by simp) with h12112 | h12112
                            · rcases p12100_3 (m.d 1 2) (by simp) with h12113 | h12113
                              · rcases p12100_3 (m.d 1 3) (by simp) with h12114 | h12114
                                · linarith only [h11385, h12114, hlam]
                                · rcases p12100_3 (m.d 1 4) (by simp) with h12116 | h12116
                                  · linarith only [h12116, hlam, p12100_0]
                                  · rcases p12100_3 (m.d 1 5) (by simp) with h12118 | h12118
                                    · linarith only [h11387, h12118, hlam]
                                    · linarith only [h11971, h12118, hlam]
                              · linarith only [h11965, h12113, hlam]
                            · linarith only [h12112, hlam, p12100_0]
                          · have p12100_0 := h12100c.1
                            have p12100_1 := h12100c.2.1
                            have p12100_2 := h12100c.2.2.1
                            have p12100_3 := h12100c.2.2.2
                            rcases p12100_3 (m.d 0 1) (by simp) with h12123 | h12123
                            · rcases p12100_3 (m.d 1 2) (by simp) with h12124 | h12124
                              · rcases p12100_3 (m.d 1 3) (by simp) with h12125 | h12125
                                · linarith only [h11385, h12125, hlam]
                                · rcases p12100_3 (m.d 1 4) (by simp) with h12127 | h12127
                                  · linarith only [h11386, h12127, hlam]
                                  · rcases p12100_3 (m.d 1 5) (by simp) with h12129 | h12129
                                    · linarith only [h12129, hlam, p12100_0]
                                    · rcases h3bigk with h12131c | h12131c | h12131c | h12131c | h12131c | h12131c | h12131c | h12131c | h12131c | h12131c | h12131c | h12131c | h12131c | h12131c | h12131c | h12131c | h12131c | h12131c | h12131c | h12131c | h12131c | h12131c | h12131c | h12131c | h12131c
                                      · have p12131_0 := h12131c.1
                                        have p12131_1 := h12131c.2.1
                                        have p12131_2 := h12131c.2.2.1
                                        have p12131_3 := h12131c.2.2.2
                                        linarith only [hlam, p12131_0]
                                      · have p12131_0 := h12131c.1
                                        have p12131_1 := h12131c.2.1
                                        have p12131_2 := h12131c.2.2.1
                                        have p12131_3 := h12131c.2.2.2
                                        linarith only [h0, h11385, h11964, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12131_1]
                                      · have p12131_0 := h12131c.1
                                        have p12131_1 := h12131c.2.1
                                        have p12131_2 := h12131c.2.2.1
                                        have p12131_3 := h12131c.2.2.2
                                        linarith only [h0, h11385, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12131_1]
                                      · have p12131_0 := h12131c.1
                                        have p12131_1 := h12131c.2.1
                                        have p12131_2 := h12131c.2.2.1
                                        have p12131_3 := h12131c.2.2.2
                                        linarith only [h11390, hlam, p12131_0]
                                      · have p12131_0 := h12131c.1
                                        have p12131_1 := h12131c.2.1
                                        have p12131_2 := h12131c.2.2.1
                                        have p12131_3 := h12131c.2.2.2
                                        linarith only [h11746, hlam, p12131_0]
                                      · have p12131_0 := h12131c.1
                                        have p12131_1 := h12131c.2.1
                                        have p12131_2 := h12131c.2.2.1
                                        have p12131_3 := h12131c.2.2.2
                                        linarith only [h11385, hlam, p12131_0]
                                      · have p12131_0 := h12131c.1
                                        have p12131_1 := h12131c.2.1
                                        have p12131_2 := h12131c.2.2.1
                                        have p12131_3 := h12131c.2.2.2
                                        linarith only [hlam, p12131_0]
                                      · have p12131_0 := h12131c.1
                                        have p12131_1 := h12131c.2.1
                                        have p12131_2 := h12131c.2.2.1
                                        have p12131_3 := h12131c.2.2.2
                                        linarith only [h0, h11385, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12131_1]
                                      · have p12131_0 := h12131c.1
                                        have p12131_1 := h12131c.2.1
                                        have p12131_2 := h12131c.2.2.1
                                        have p12131_3 := h12131c.2.2.2
                                        linarith only [h11967, hlam, p12131_0]
                                      · have p12131_0 := h12131c.1
                                        have p12131_1 := h12131c.2.1
                                        have p12131_2 := h12131c.2.2.1
                                        have p12131_3 := h12131c.2.2.2
                                        linarith only [h11969, hlam, p12131_0]
                                      · have p12131_0 := h12131c.1
                                        have p12131_1 := h12131c.2.1
                                        have p12131_2 := h12131c.2.2.1
                                        have p12131_3 := h12131c.2.2.2
                                        linarith only [h11388, hlam, p12131_0]
                                      · have p12131_0 := h12131c.1
                                        have p12131_1 := h12131c.2.1
                                        have p12131_2 := h12131c.2.2.1
                                        have p12131_3 := h12131c.2.2.2
                                        linarith only [h11964, hlam, p12131_0]
                                      · have p12131_0 := h12131c.1
                                        have p12131_1 := h12131c.2.1
                                        have p12131_2 := h12131c.2.2.1
                                        have p12131_3 := h12131c.2.2.2
                                        linarith only [hlam, p12131_0]
                                      · have p12131_0 := h12131c.1
                                        have p12131_1 := h12131c.2.1
                                        have p12131_2 := h12131c.2.2.1
                                        have p12131_3 := h12131c.2.2.2
                                        linarith only [h11973, hlam, p12131_0]
                                      · have p12131_0 := h12131c.1
                                        have p12131_1 := h12131c.2.1
                                        have p12131_2 := h12131c.2.2.1
                                        have p12131_3 := h12131c.2.2.2
                                        linarith only [h11975, hlam, p12131_0]
                                      · have p12131_0 := h12131c.1
                                        have p12131_1 := h12131c.2.1
                                        have p12131_2 := h12131c.2.2.1
                                        have p12131_3 := h12131c.2.2.2
                                        linarith only [hc03, hc34, hlam, hphi, p12131_1]
                                      · have p12131_0 := h12131c.1
                                        have p12131_1 := h12131c.2.1
                                        have p12131_2 := h12131c.2.2.1
                                        have p12131_3 := h12131c.2.2.2
                                        linarith only [h11964, h11979, hc23, hc45, hlam, hphi, ht34, p12131_1]
                                      · have p12131_0 := h12131c.1
                                        have p12131_1 := h12131c.2.1
                                        have p12131_2 := h12131c.2.2.1
                                        have p12131_3 := h12131c.2.2.2
                                        linarith only [h11979, hc23, hc45, hlam, hphi, ht34, p12131_1]
                                      · have p12131_0 := h12131c.1
                                        have p12131_1 := h12131c.2.1
                                        have p12131_2 := h12131c.2.2.1
                                        have p12131_3 := h12131c.2.2.2
                                        linarith only [hlam, p12131_0]
                                      · have p12131_0 := h12131c.1
                                        have p12131_1 := h12131c.2.1
                                        have p12131_2 := h12131c.2.2.1
                                        have p12131_3 := h12131c.2.2.2
                                        linarith only [h11979, hlam, p12131_1]
                                      · have p12131_0 := h12131c.1
                                        have p12131_1 := h12131c.2.1
                                        have p12131_2 := h12131c.2.2.1
                                        have p12131_3 := h12131c.2.2.2
                                        linarith only [h11385, h11964, hc23, hc35, hlam, hphi, p12131_1]
                                      · have p12131_0 := h12131c.1
                                        have p12131_1 := h12131c.2.1
                                        have p12131_2 := h12131c.2.2.1
                                        have p12131_3 := h12131c.2.2.2
                                        linarith only [h11964, hc23, hc35, hlam, hphi, p12131_1]
                                      · have p12131_0 := h12131c.1
                                        have p12131_1 := h12131c.2.1
                                        have p12131_2 := h12131c.2.2.1
                                        have p12131_3 := h12131c.2.2.2
                                        linarith only [hc23, hc35, hlam, hphi, p12131_1]
                                      · have p12131_0 := h12131c.1
                                        have p12131_1 := h12131c.2.1
                                        have p12131_2 := h12131c.2.2.1
                                        have p12131_3 := h12131c.2.2.2
                                        linarith only [h11979, hc34, hc45, hlam, hphi, p12131_1]
                                      · have p12131_0 := h12131c.1
                                        have p12131_1 := h12131c.2.1
                                        have p12131_2 := h12131c.2.2.1
                                        have p12131_3 := h12131c.2.2.2
                                        linarith only [hlam, p12131_0]
                              · linarith only [h11966, h12124, hlam]
                            · linarith only [h12123, hlam, p12100_0]
                          · have p12100_0 := h12100c.1
                            have p12100_1 := h12100c.2.1
                            have p12100_2 := h12100c.2.2.1
                            have p12100_3 := h12100c.2.2.2
                            rcases p12100_3 (m.d 0 1) (by simp) with h12159 | h12159
                            · linarith only [h12159, hlam, p12100_0]
                            · rcases p12100_3 (m.d 1 2) (by simp) with h12161 | h12161
                              · rcases p12100_3 (m.d 1 3) (by simp) with h12162 | h12162
                                · linarith only [h11964, h12162, hlam]
                                · rcases p12100_3 (m.d 1 4) (by simp) with h12164 | h12164
                                  · linarith only [h11965, h12164, hlam]
                                  · rcases p12100_3 (m.d 1 5) (by simp) with h12166 | h12166
                                    · linarith only [h11966, h12166, hlam]
                                    · rcases h3bigk with h12168c | h12168c | h12168c | h12168c | h12168c | h12168c | h12168c | h12168c | h12168c | h12168c | h12168c | h12168c | h12168c | h12168c | h12168c | h12168c | h12168c | h12168c | h12168c | h12168c | h12168c | h12168c | h12168c | h12168c | h12168c
                                      · have p12168_0 := h12168c.1
                                        have p12168_1 := h12168c.2.1
                                        have p12168_2 := h12168c.2.2.1
                                        have p12168_3 := h12168c.2.2.2
                                        linarith only [hlam, p12168_0]
                                      · have p12168_0 := h12168c.1
                                        have p12168_1 := h12168c.2.1
                                        have p12168_2 := h12168c.2.2.1
                                        have p12168_3 := h12168c.2.2.2
                                        linarith only [h11385, h11964, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12100_1, p12168_1]
                                      · have p12168_0 := h12168c.1
                                        have p12168_1 := h12168c.2.1
                                        have p12168_2 := h12168c.2.2.1
                                        have p12168_3 := h12168c.2.2.2
                                        linarith only [h11385, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12100_1, p12168_1]
                                      · have p12168_0 := h12168c.1
                                        have p12168_1 := h12168c.2.1
                                        have p12168_2 := h12168c.2.2.1
                                        have p12168_3 := h12168c.2.2.2
                                        linarith only [h11390, hlam, p12168_0]
                                      · have p12168_0 := h12168c.1
                                        have p12168_1 := h12168c.2.1
                                        have p12168_2 := h12168c.2.2.1
                                        have p12168_3 := h12168c.2.2.2
                                        linarith only [h11746, hlam, p12168_0]
                                      · have p12168_0 := h12168c.1
                                        have p12168_1 := h12168c.2.1
                                        have p12168_2 := h12168c.2.2.1
                                        have p12168_3 := h12168c.2.2.2
                                        linarith only [h11385, hlam, p12168_0]
                                      · have p12168_0 := h12168c.1
                                        have p12168_1 := h12168c.2.1
                                        have p12168_2 := h12168c.2.2.1
                                        have p12168_3 := h12168c.2.2.2
                                        linarith only [hlam, p12168_0]
                                      · have p12168_0 := h12168c.1
                                        have p12168_1 := h12168c.2.1
                                        have p12168_2 := h12168c.2.2.1
                                        have p12168_3 := h12168c.2.2.2
                                        linarith only [h11385, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12100_1, p12168_1]
                                      · have p12168_0 := h12168c.1
                                        have p12168_1 := h12168c.2.1
                                        have p12168_2 := h12168c.2.2.1
                                        have p12168_3 := h12168c.2.2.2
                                        linarith only [h11967, hlam, p12168_0]
                                      · have p12168_0 := h12168c.1
                                        have p12168_1 := h12168c.2.1
                                        have p12168_2 := h12168c.2.2.1
                                        have p12168_3 := h12168c.2.2.2
                                        linarith only [h11969, hlam, p12168_0]
                                      · have p12168_0 := h12168c.1
                                        have p12168_1 := h12168c.2.1
                                        have p12168_2 := h12168c.2.2.1
                                        have p12168_3 := h12168c.2.2.2
                                        linarith only [h11388, hlam, p12168_0]
                                      · have p12168_0 := h12168c.1
                                        have p12168_1 := h12168c.2.1
                                        have p12168_2 := h12168c.2.2.1
                                        have p12168_3 := h12168c.2.2.2
                                        linarith only [h11964, hlam, p12168_0]
                                      · have p12168_0 := h12168c.1
                                        have p12168_1 := h12168c.2.1
                                        have p12168_2 := h12168c.2.2.1
                                        have p12168_3 := h12168c.2.2.2
                                        linarith only [hlam, p12168_0]
                                      · have p12168_0 := h12168c.1
                                        have p12168_1 := h12168c.2.1
                                        have p12168_2 := h12168c.2.2.1
                                        have p12168_3 := h12168c.2.2.2
                                        linarith only [h11973, hlam, p12168_0]
                                      · have p12168_0 := h12168c.1
                                        have p12168_1 := h12168c.2.1
                                        have p12168_2 := h12168c.2.2.1
                                        have p12168_3 := h12168c.2.2.2
                                        linarith only [h11975, hlam, p12168_0]
                                      · have p12168_0 := h12168c.1
                                        have p12168_1 := h12168c.2.1
                                        have p12168_2 := h12168c.2.2.1
                                        have p12168_3 := h12168c.2.2.2
                                        linarith only [hc03, hc34, hlam, hphi, p12168_1]
                                      · have p12168_0 := h12168c.1
                                        have p12168_1 := h12168c.2.1
                                        have p12168_2 := h12168c.2.2.1
                                        have p12168_3 := h12168c.2.2.2
                                        linarith only [h11964, hc23, hc34, hlam, hphi, p12168_1]
                                      · have p12168_0 := h12168c.1
                                        have p12168_1 := h12168c.2.1
                                        have p12168_2 := h12168c.2.2.1
                                        have p12168_3 := h12168c.2.2.2
                                        linarith only [hc23, hc34, hlam, hphi, p12168_1]
                                      · have p12168_0 := h12168c.1
                                        have p12168_1 := h12168c.2.1
                                        have p12168_2 := h12168c.2.2.1
                                        have p12168_3 := h12168c.2.2.2
                                        linarith only [hlam, p12168_0]
                                      · have p12168_0 := h12168c.1
                                        have p12168_1 := h12168c.2.1
                                        have p12168_2 := h12168c.2.2.1
                                        have p12168_3 := h12168c.2.2.2
                                        linarith only [h11979, hlam, p12168_1]
                                      · have p12168_0 := h12168c.1
                                        have p12168_1 := h12168c.2.1
                                        have p12168_2 := h12168c.2.2.1
                                        have p12168_3 := h12168c.2.2.2
                                        linarith only [h11385, h11964, h11979, hc23, hc45, hlam, hphi, ht34, p12168_1]
                                      · have p12168_0 := h12168c.1
                                        have p12168_1 := h12168c.2.1
                                        have p12168_2 := h12168c.2.2.1
                                        have p12168_3 := h12168c.2.2.2
                                        linarith only [h11964, h11979, hc23, hc45, hlam, hphi, ht34, p12168_1]
                                      · have p12168_0 := h12168c.1
                                        have p12168_1 := h12168c.2.1
                                        have p12168_2 := h12168c.2.2.1
                                        have p12168_3 := h12168c.2.2.2
                                        linarith only [h11979, hc23, hc45, hlam, hphi, ht34, p12168_1]
                                      · have p12168_0 := h12168c.1
                                        have p12168_1 := h12168c.2.1
                                        have p12168_2 := h12168c.2.2.1
                                        have p12168_3 := h12168c.2.2.2
                                        linarith only [h11979, hc34, hc45, hlam, hphi, p12168_1]
                                      · have p12168_0 := h12168c.1
                                        have p12168_1 := h12168c.2.1
                                        have p12168_2 := h12168c.2.2.1
                                        have p12168_3 := h12168c.2.2.2
                                        linarith only [hlam, p12168_0]
                              · linarith only [h12161, hlam, p12100_0]
                          · have p12100_0 := h12100c.1
                            have p12100_1 := h12100c.2.1
                            have p12100_2 := h12100c.2.2.1
                            have p12100_3 := h12100c.2.2.2
                            linarith only [hlam, p12100_0]
                          · have p12100_0 := h12100c.1
                            have p12100_1 := h12100c.2.1
                            have p12100_2 := h12100c.2.2.1
                            have p12100_3 := h12100c.2.2.2
                            rcases p12100_3 (m.d 0 1) (by simp) with h12196 | h12196
                            · linarith only [h0, h12196, hlam]
                            · linarith only [h11385, h12196, hlam]
                          · have p12100_0 := h12100c.1
                            have p12100_1 := h12100c.2.1
                            have p12100_2 := h12100c.2.2.1
                            have p12100_3 := h12100c.2.2.2
                            rcases p12100_3 (m.d 0 1) (by simp) with h12199 | h12199
                            · linarith only [h0, h12199, hlam]
                            · linarith only [h11386, h12199, hlam]
                          · have p12100_0 := h12100c.1
                            have p12100_1 := h12100c.2.1
                            have p12100_2 := h12100c.2.2.1
                            have p12100_3 := h12100c.2.2.2
                            rcases p12100_3 (m.d 0 1) (by simp) with h12202 | h12202
                            · linarith only [h0, h12202, hlam]
                            · linarith only [h11387, h12202, hlam]
                          · have p12100_0 := h12100c.1
                            have p12100_1 := h12100c.2.1
                            have p12100_2 := h12100c.2.2.1
                            have p12100_3 := h12100c.2.2.2
                            linarith only [h11385, hlam, p12100_0]
                          · have p12100_0 := h12100c.1
                            have p12100_1 := h12100c.2.1
                            have p12100_2 := h12100c.2.2.1
                            have p12100_3 := h12100c.2.2.2
                            linarith only [h11964, hlam, p12100_1]
                          · have p12100_0 := h12100c.1
                            have p12100_1 := h12100c.2.1
                            have p12100_2 := h12100c.2.2.1
                            have p12100_3 := h12100c.2.2.2
                            linarith only [hlam, p12100_0]
                          · have p12100_0 := h12100c.1
                            have p12100_1 := h12100c.2.1
                            have p12100_2 := h12100c.2.2.1
                            have p12100_3 := h12100c.2.2.2
                            linarith only [h11967, hlam, p12100_1]
                          · have p12100_0 := h12100c.1
                            have p12100_1 := h12100c.2.1
                            have p12100_2 := h12100c.2.2.1
                            have p12100_3 := h12100c.2.2.2
                            linarith only [h11969, hlam, p12100_1]
                          · have p12100_0 := h12100c.1
                            have p12100_1 := h12100c.2.1
                            have p12100_2 := h12100c.2.2.1
                            have p12100_3 := h12100c.2.2.2
                            linarith only [h11386, hlam, p12100_0]
                          · have p12100_0 := h12100c.1
                            have p12100_1 := h12100c.2.1
                            have p12100_2 := h12100c.2.2.1
                            have p12100_3 := h12100c.2.2.2
                            linarith only [h11965, hlam, p12100_1]
                          · have p12100_0 := h12100c.1
                            have p12100_1 := h12100c.2.1
                            have p12100_2 := h12100c.2.2.1
                            have p12100_3 := h12100c.2.2.2
                            linarith only [h0, h11387, h11971, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12100_1]
                          · have p12100_0 := h12100c.1
                            have p12100_1 := h12100c.2.1
                            have p12100_2 := h12100c.2.2.1
                            have p12100_3 := h12100c.2.2.2
                            linarith only [hlam, p12100_0]
                          · have p12100_0 := h12100c.1
                            have p12100_1 := h12100c.2.1
                            have p12100_2 := h12100c.2.2.1
                            have p12100_3 := h12100c.2.2.2
                            linarith only [h11971, hlam, p12100_1]
                          · have p12100_0 := h12100c.1
                            have p12100_1 := h12100c.2.1
                            have p12100_2 := h12100c.2.2.1
                            have p12100_3 := h12100c.2.2.2
                            linarith only [h11387, hlam, p12100_0]
                          · have p12100_0 := h12100c.1
                            have p12100_1 := h12100c.2.1
                            have p12100_2 := h12100c.2.2.1
                            have p12100_3 := h12100c.2.2.2
                            linarith only [h11966, hlam, p12100_1]
                          · have p12100_0 := h12100c.1
                            have p12100_1 := h12100c.2.1
                            have p12100_2 := h12100c.2.2.1
                            have p12100_3 := h12100c.2.2.2
                            linarith only [h0, h11387, h11964, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12100_1]
                          · have p12100_0 := h12100c.1
                            have p12100_1 := h12100c.2.1
                            have p12100_2 := h12100c.2.2.1
                            have p12100_3 := h12100c.2.2.2
                            linarith only [h0, h11387, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p12100_1]
                          · have p12100_0 := h12100c.1
                            have p12100_1 := h12100c.2.1
                            have p12100_2 := h12100c.2.2.1
                            have p12100_3 := h12100c.2.2.2
                            linarith only [hlam, p12100_0]
          · linarith only [h0, h11387, h11966, hlam]
        · linarith only [h0, h11389, h11965, hlam]
      · linarith only [h0, h11388, h11964, hlam]

set_option maxHeartbeats 15022000 in
set_option maxHeartbeats 15022000 in
theorem r1l7_11_23_L_I_H_I_s11_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h11385 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h11386 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h11387 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h11388 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h11389 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h0 := hg0
  rcases m.htr 0 3 4 (by decide) (by decide) with h11390 | h11390
  · exact r1l7_11_23_L_I_H_I_s11_x0_x0_x0_x0_x0_x0 m hb1 hb3 hg0 h11385 h11386 h11387 h11388 h11389 h11390
  · exact r1l7_11_23_L_I_H_I_s11_x0_x0_x0_x0_x0_x1 m hb1 hb3 hg0 h11385 h11386 h11387 h11388 h11389 h11390

set_option maxHeartbeats 15022000 in
set_option maxHeartbeats 15022000 in
theorem r1l7_11_23_L_I_H_I_s11_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h11385 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h11386 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h11387 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h11388 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h11389 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h0 := hg0
  linarith only [h0, h11386, h11389, hlam]

set_option maxHeartbeats 15022000 in
set_option maxHeartbeats 15022000 in
theorem r1l7_11_23_L_I_H_I_s11_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h11385 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h11386 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h11387 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h11388 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0 := hg0
  rcases m.htr 0 2 4 (by decide) (by decide) with h11389 | h11389
  · exact r1l7_11_23_L_I_H_I_s11_x0_x0_x0_x0_x0 m hb1 hb3 hg0 h11385 h11386 h11387 h11388 h11389
  · exact r1l7_11_23_L_I_H_I_s11_x0_x0_x0_x0_x1 m hb1 hb3 hg0 h11385 h11386 h11387 h11388 h11389

set_option maxHeartbeats 15022000 in
set_option maxHeartbeats 15022000 in
theorem r1l7_11_23_L_I_H_I_s11_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h11385 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h11386 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h11387 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h11388 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h0 := hg0
  linarith only [h0, h11385, h11388, hlam]

set_option maxHeartbeats 15022000 in
set_option maxHeartbeats 15022000 in
theorem r1l7_11_23_L_I_H_I_s11_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h11385 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h11386 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h11387 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h11388 | h11388
  · exact r1l7_11_23_L_I_H_I_s11_x0_x0_x0_x0 m hb1 hb3 hg0 h11385 h11386 h11387 h11388
  · exact r1l7_11_23_L_I_H_I_s11_x0_x0_x0_x1 m hb1 hb3 hg0 h11385 h11386 h11387 h11388

set_option maxHeartbeats 15022000 in
set_option maxHeartbeats 15022000 in
theorem r1l7_11_23_L_I_H_I_s11_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h11385 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h11386 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h11387 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h12225 | h12225
  · rcases m.htr 0 2 4 (by decide) (by decide) with h12226 | h12226
    · rcases m.htr 0 3 4 (by decide) (by decide) with h12227 | h12227
      · rcases m.htr 0 3 5 (by decide) (by decide) with h12228 | h12228
        · linarith only [h11385, h11387, h12228, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h12230 | h12230
          · linarith only [h11385, h11387, h12227, h12230, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h12232 | h12232
            · rcases m.htr 1 2 4 (by decide) (by decide) with h12233 | h12233
              · rcases m.htr 1 2 5 (by decide) (by decide) with h12234 | h12234
                · rcases m.htr 1 3 4 (by decide) (by decide) with h12235 | h12235
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h12236 | h12236
                    · linarith only [h11385, h11387, h12228, h12234, h12236, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h12238 | h12238
                      · linarith only [h11385, h11387, h12230, h12235, h12238, hlam]
                      · linarith only [h11385, h11387, h12235, h12238, hc34, hc45, hlam, hphi]
                  · linarith only [h12227, h12228, h12232, h12235, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h12242 | h12242
                  · linarith only [h0, h11385, h12234, h12242, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h11385, h12227, h12234, h12242, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · linarith only [h0, h11385, h12226, h12227, h12233, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h12225, h12232, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h12247 | h12247
        · linarith only [h11385, h11387, h12247, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h12249 | h12249
          · linarith only [h11386, h11387, h12249, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h12251 | h12251
            · rcases m.htr 1 2 4 (by decide) (by decide) with h12252 | h12252
              · rcases m.htr 1 2 5 (by decide) (by decide) with h12253 | h12253
                · rcases m.htr 1 3 4 (by decide) (by decide) with h12254 | h12254
                  · linarith only [h0, h11385, h12227, h12254, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h12256 | h12256
                    · linarith only [h11385, h11387, h12247, h12256, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h12258 | h12258
                      · linarith only [h0, h11386, h12227, h12249, h12258, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h12260 | h12260
                        · linarith only [h11385, h12227, h12251, h12260, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h12262 | h12262
                          · linarith only [h11385, h12247, h12251, h12262, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h12264 | h12264
                            · linarith only [h0, h11386, h11387, h12226, h12251, h12254, h12258, h12264, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h12266 | h12266
                              · linarith only [h11386, h11387, h12251, h12254, h12258, h12266, hc23, hc34, hlam, hphi]
                              · rcases h1bigk with h12268c | h12268c | h12268c | h12268c | h12268c | h12268c | h12268c | h12268c | h12268c | h12268c | h12268c | h12268c | h12268c | h12268c | h12268c | h12268c | h12268c | h12268c | h12268c | h12268c | h12268c | h12268c | h12268c | h12268c | h12268c
                                · have p12268_0 := h12268c.1
                                  have p12268_1 := h12268c.2.1
                                  have p12268_2 := h12268c.2.2.1
                                  have p12268_3 := h12268c.2.2.2
                                  linarith only [hlam, p12268_0]
                                · have p12268_0 := h12268c.1
                                  have p12268_1 := h12268c.2.1
                                  have p12268_2 := h12268c.2.2.1
                                  have p12268_3 := h12268c.2.2.2
                                  linarith only [h0, hlam, p12268_0]
                                · have p12268_0 := h12268c.1
                                  have p12268_1 := h12268c.2.1
                                  have p12268_2 := h12268c.2.2.1
                                  have p12268_3 := h12268c.2.2.2
                                  linarith only [h11387, h12251, h12256, hc23, hc35, hlam, hphi, p12268_1]
                                · have p12268_0 := h12268c.1
                                  have p12268_1 := h12268c.2.1
                                  have p12268_2 := h12268c.2.2.1
                                  have p12268_3 := h12268c.2.2.2
                                  linarith only [h11387, h12251, h12254, h12256, h12266, hc23, hc45, hlam, hphi, ht34, p12268_1]
                                · have p12268_0 := h12268c.1
                                  have p12268_1 := h12268c.2.1
                                  have p12268_2 := h12268c.2.2.1
                                  have p12268_3 := h12268c.2.2.2
                                  linarith only [h11387, hlam, p12268_0]
                                · have p12268_0 := h12268c.1
                                  have p12268_1 := h12268c.2.1
                                  have p12268_2 := h12268c.2.2.1
                                  have p12268_3 := h12268c.2.2.2
                                  rcases p12268_3 (m.d 0 1) (by simp) with h12274 | h12274
                                  · linarith only [h12274, hlam, p12268_0]
                                  · rcases p12268_3 (m.d 1 2) (by simp) with h12276 | h12276
                                    · rcases p12268_3 (m.d 1 3) (by simp) with h12277 | h12277
                                      · linarith only [h12251, h12277, hlam]
                                      · rcases p12268_3 (m.d 1 4) (by simp) with h12279 | h12279
                                        · linarith only [h12252, h12279, hlam]
                                        · rcases p12268_3 (m.d 1 5) (by simp) with h12281 | h12281
                                          · linarith only [h12253, h12281, hlam]
                                          · linarith only [h11387, h12281, hlam]
                                    · linarith only [h12276, hlam, p12268_0]
                                · have p12268_0 := h12268c.1
                                  have p12268_1 := h12268c.2.1
                                  have p12268_2 := h12268c.2.2.1
                                  have p12268_3 := h12268c.2.2.2
                                  linarith only [hlam, p12268_0]
                                · have p12268_0 := h12268c.1
                                  have p12268_1 := h12268c.2.1
                                  have p12268_2 := h12268c.2.2.1
                                  have p12268_3 := h12268c.2.2.2
                                  rcases p12268_3 (m.d 0 1) (by simp) with h12286 | h12286
                                  · linarith only [h0, h12286, hlam]
                                  · linarith only [h11385, h12286, hlam]
                                · have p12268_0 := h12268c.1
                                  have p12268_1 := h12268c.2.1
                                  have p12268_2 := h12268c.2.2.1
                                  have p12268_3 := h12268c.2.2.2
                                  rcases p12268_3 (m.d 0 1) (by simp) with h12289 | h12289
                                  · linarith only [h0, h12289, hlam]
                                  · linarith only [h11386, h12289, hlam]
                                · have p12268_0 := h12268c.1
                                  have p12268_1 := h12268c.2.1
                                  have p12268_2 := h12268c.2.2.1
                                  have p12268_3 := h12268c.2.2.2
                                  linarith only [h11386, h11387, h12251, h12254, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12268_1]
                                · have p12268_0 := h12268c.1
                                  have p12268_1 := h12268c.2.1
                                  have p12268_2 := h12268c.2.2.1
                                  have p12268_3 := h12268c.2.2.2
                                  linarith only [h11385, hlam, p12268_0]
                                · have p12268_0 := h12268c.1
                                  have p12268_1 := h12268c.2.1
                                  have p12268_2 := h12268c.2.2.1
                                  have p12268_3 := h12268c.2.2.2
                                  linarith only [h12251, hlam, p12268_1]
                                · have p12268_0 := h12268c.1
                                  have p12268_1 := h12268c.2.1
                                  have p12268_2 := h12268c.2.2.1
                                  have p12268_3 := h12268c.2.2.2
                                  linarith only [hlam, p12268_0]
                                · have p12268_0 := h12268c.1
                                  have p12268_1 := h12268c.2.1
                                  have p12268_2 := h12268c.2.2.1
                                  have p12268_3 := h12268c.2.2.2
                                  linarith only [h12254, hlam, p12268_1]
                                · have p12268_0 := h12268c.1
                                  have p12268_1 := h12268c.2.1
                                  have p12268_2 := h12268c.2.2.1
                                  have p12268_3 := h12268c.2.2.2
                                  linarith only [h12256, hlam, p12268_1]
                                · have p12268_0 := h12268c.1
                                  have p12268_1 := h12268c.2.1
                                  have p12268_2 := h12268c.2.2.1
                                  have p12268_3 := h12268c.2.2.2
                                  linarith only [h11386, hlam, p12268_0]
                                · have p12268_0 := h12268c.1
                                  have p12268_1 := h12268c.2.1
                                  have p12268_2 := h12268c.2.2.1
                                  have p12268_3 := h12268c.2.2.2
                                  linarith only [h12252, hlam, p12268_1]
                                · have p12268_0 := h12268c.1
                                  have p12268_1 := h12268c.2.1
                                  have p12268_2 := h12268c.2.2.1
                                  have p12268_3 := h12268c.2.2.2
                                  linarith only [h11386, h11387, h12251, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12268_1]
                                · have p12268_0 := h12268c.1
                                  have p12268_1 := h12268c.2.1
                                  have p12268_2 := h12268c.2.2.1
                                  have p12268_3 := h12268c.2.2.2
                                  linarith only [hlam, p12268_0]
                                · have p12268_0 := h12268c.1
                                  have p12268_1 := h12268c.2.1
                                  have p12268_2 := h12268c.2.2.1
                                  have p12268_3 := h12268c.2.2.2
                                  linarith only [h12258, hlam, p12268_1]
                                · have p12268_0 := h12268c.1
                                  have p12268_1 := h12268c.2.1
                                  have p12268_2 := h12268c.2.2.1
                                  have p12268_3 := h12268c.2.2.2
                                  linarith only [h11386, h12256, h12266, hc14, hc45, hlam, hphi, p12268_1]
                                · have p12268_0 := h12268c.1
                                  have p12268_1 := h12268c.2.1
                                  have p12268_2 := h12268c.2.2.1
                                  have p12268_3 := h12268c.2.2.2
                                  linarith only [h12253, hlam, p12268_1]
                                · have p12268_0 := h12268c.1
                                  have p12268_1 := h12268c.2.1
                                  have p12268_2 := h12268c.2.2.1
                                  have p12268_3 := h12268c.2.2.2
                                  rcases p12268_3 (m.d 0 1) (by simp) with h12305 | h12305
                                  · linarith only [h11387, h12305, hlam]
                                  · linarith only [h11385, h12305, hlam]
                                · have p12268_0 := h12268c.1
                                  have p12268_1 := h12268c.2.1
                                  have p12268_2 := h12268c.2.2.1
                                  have p12268_3 := h12268c.2.2.2
                                  rcases p12268_3 (m.d 0 1) (by simp) with h12308 | h12308
                                  · linarith only [h11387, h12308, hlam]
                                  · linarith only [h11386, h12308, hlam]
                                · have p12268_0 := h12268c.1
                                  have p12268_1 := h12268c.2.1
                                  have p12268_2 := h12268c.2.2.1
                                  have p12268_3 := h12268c.2.2.2
                                  linarith only [hlam, p12268_0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h12312 | h12312
                  · linarith only [h0, h11385, h12253, h12312, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h12314 | h12314
                    · linarith only [h0, h11386, h12253, h12312, h12314, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h12316 | h12316
                      · linarith only [h0, h11386, h12253, h12316, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h12318 | h12318
                        · linarith only [h11385, h12227, h12251, h12318, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h12320 | h12320
                          · linarith only [h0, h11386, h12251, h12253, h12312, h12314, h12320, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · linarith only [h0, h11386, h12251, h12253, h12312, h12320, hc23, hc35, hlam, hphi]
              · linarith only [h0, h12226, h12252, hlam]
            · linarith only [h0, h12225, h12251, hlam]
    · linarith only [h0, h11386, h12226, hlam]
  · linarith only [h0, h11385, h12225, hlam]

set_option maxHeartbeats 15022000 in
set_option maxHeartbeats 15022000 in
theorem r1l7_11_23_L_I_H_I_s11_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h11385 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h11386 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h11387 | h11387
  · exact r1l7_11_23_L_I_H_I_s11_x0_x0_x0 m hb1 hb3 hg0 h11385 h11386 h11387
  · exact r1l7_11_23_L_I_H_I_s11_x0_x0_x1 m hb1 hb3 hg0 h11385 h11386 h11387

end R2N4
