import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 24306000 in
set_option maxHeartbeats 24306000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h19744 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h19745 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19746 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19747 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19748 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 1 2 3 (by decide) (by decide) with h19749 | h19749
  · linarith only [h0, h19744, h19749, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h19751 | h19751
    · rcases m.htr 1 2 5 (by decide) (by decide) with h19752 | h19752
      · rcases m.htr 1 3 4 (by decide) (by decide) with h19753 | h19753
        · rcases m.htr 1 3 5 (by decide) (by decide) with h19754 | h19754
          · rcases m.htr 1 4 5 (by decide) (by decide) with h19755 | h19755
            · rcases m.htr 2 3 4 (by decide) (by decide) with h19756 | h19756
              · rcases m.htr 2 3 5 (by decide) (by decide) with h19757 | h19757
                · rcases m.htr 2 4 5 (by decide) (by decide) with h19758 | h19758
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h19759 | h19759
                    · rcases h1bigk with h19760c | h19760c | h19760c | h19760c | h19760c | h19760c | h19760c | h19760c | h19760c | h19760c | h19760c | h19760c | h19760c | h19760c | h19760c | h19760c | h19760c | h19760c | h19760c | h19760c | h19760c | h19760c | h19760c | h19760c | h19760c
                      · have p19760_0 := h19760c.1
                        have p19760_1 := h19760c.2.1
                        have p19760_2 := h19760c.2.2.1
                        have p19760_3 := h19760c.2.2.2
                        linarith only [hlam, p19760_0]
                      · have p19760_0 := h19760c.1
                        have p19760_1 := h19760c.2.1
                        have p19760_2 := h19760c.2.2.1
                        have p19760_3 := h19760c.2.2.2
                        linarith only [h19751, h19756, h19759, hc01, hc45, hlam, hphi, ht0b, ht5b, p19760_1]
                      · have p19760_0 := h19760c.1
                        have p19760_1 := h19760c.2.1
                        have p19760_2 := h19760c.2.2.1
                        have p19760_3 := h19760c.2.2.2
                        linarith only [h19749, h19751, h19756, h19759, hc01, hc45, hlam, hphi, ht0b, ht5b, p19760_1]
                      · have p19760_0 := h19760c.1
                        have p19760_1 := h19760c.2.1
                        have p19760_2 := h19760c.2.2.1
                        have p19760_3 := h19760c.2.2.2
                        rcases p19760_3 (m.d 0 1) (by simp) with h19764 | h19764
                        · rcases p19760_3 (m.d 1 2) (by simp) with h19765 | h19765
                          · linarith only [h0, h19765, hlam]
                          · linarith only [h19751, h19765, hlam]
                        · linarith only [h19764, hlam, p19760_0]
                      · have p19760_0 := h19760c.1
                        have p19760_1 := h19760c.2.1
                        have p19760_2 := h19760c.2.2.1
                        have p19760_3 := h19760c.2.2.2
                        rcases p19760_3 (m.d 0 1) (by simp) with h19769 | h19769
                        · rcases p19760_3 (m.d 1 2) (by simp) with h19770 | h19770
                          · linarith only [h0, h19770, hlam]
                          · linarith only [h19752, h19770, hlam]
                        · linarith only [h19769, hlam, p19760_0]
                      · have p19760_0 := h19760c.1
                        have p19760_1 := h19760c.2.1
                        have p19760_2 := h19760c.2.2.1
                        have p19760_3 := h19760c.2.2.2
                        linarith only [h0, hlam, p19760_0]
                      · have p19760_0 := h19760c.1
                        have p19760_1 := h19760c.2.1
                        have p19760_2 := h19760c.2.2.1
                        have p19760_3 := h19760c.2.2.2
                        linarith only [hlam, p19760_0]
                      · have p19760_0 := h19760c.1
                        have p19760_1 := h19760c.2.1
                        have p19760_2 := h19760c.2.2.1
                        have p19760_3 := h19760c.2.2.2
                        linarith only [h19749, hlam, p19760_1]
                      · have p19760_0 := h19760c.1
                        have p19760_1 := h19760c.2.1
                        have p19760_2 := h19760c.2.2.1
                        have p19760_3 := h19760c.2.2.2
                        linarith only [h0, h19751, h19756, h19759, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p19760_1]
                      · have p19760_0 := h19760c.1
                        have p19760_1 := h19760c.2.1
                        have p19760_2 := h19760c.2.2.1
                        have p19760_3 := h19760c.2.2.2
                        rcases p19760_3 (m.d 0 1) (by simp) with h19778 | h19778
                        · rcases p19760_3 (m.d 1 2) (by simp) with h19779 | h19779
                          · rcases p19760_3 (m.d 1 3) (by simp) with h19780 | h19780
                            · rcases p19760_3 (m.d 1 4) (by simp) with h19781 | h19781
                              · linarith only [h19751, h19781, hlam]
                              · linarith only [h19755, h19781, hlam]
                            · linarith only [h19754, h19780, hlam]
                          · linarith only [h19752, h19779, hlam]
                        · linarith only [h19778, h3, hlam]
                      · have p19760_0 := h19760c.1
                        have p19760_1 := h19760c.2.1
                        have p19760_2 := h19760c.2.2.1
                        have p19760_3 := h19760c.2.2.2
                        linarith only [h1, hlam, p19760_0]
                      · have p19760_0 := h19760c.1
                        have p19760_1 := h19760c.2.1
                        have p19760_2 := h19760c.2.2.1
                        have p19760_3 := h19760c.2.2.2
                        linarith only [h1, h19751, h19756, h19759, hc01, hc45, hlam, hphi, ht0b, ht5b, p19760_1]
                      · have p19760_0 := h19760c.1
                        have p19760_1 := h19760c.2.1
                        have p19760_2 := h19760c.2.2.1
                        have p19760_3 := h19760c.2.2.2
                        linarith only [hlam, p19760_0]
                      · have p19760_0 := h19760c.1
                        have p19760_1 := h19760c.2.1
                        have p19760_2 := h19760c.2.2.1
                        have p19760_3 := h19760c.2.2.2
                        linarith only [h1, h19751, h19756, h19759, hc01, hc45, hlam, hphi, ht0b, ht5b, p19760_1]
                      · have p19760_0 := h19760c.1
                        have p19760_1 := h19760c.2.1
                        have p19760_2 := h19760c.2.2.1
                        have p19760_3 := h19760c.2.2.2
                        rcases p19760_3 (m.d 0 1) (by simp) with h19791 | h19791
                        · rcases p19760_3 (m.d 1 2) (by simp) with h19792 | h19792
                          · linarith only [h19749, h19792, hlam]
                          · linarith only [h19752, h19792, hlam]
                        · linarith only [h19791, h3, hlam]
                      · have p19760_0 := h19760c.1
                        have p19760_1 := h19760c.2.1
                        have p19760_2 := h19760c.2.2.1
                        have p19760_3 := h19760c.2.2.2
                        linarith only [h2, hlam, p19760_0]
                      · have p19760_0 := h19760c.1
                        have p19760_1 := h19760c.2.1
                        have p19760_2 := h19760c.2.2.1
                        have p19760_3 := h19760c.2.2.2
                        linarith only [h19751, hlam, p19760_0]
                      · have p19760_0 := h19760c.1
                        have p19760_1 := h19760c.2.1
                        have p19760_2 := h19760c.2.2.1
                        have p19760_3 := h19760c.2.2.2
                        linarith only [h19753, hlam, p19760_1]
                      · have p19760_0 := h19760c.1
                        have p19760_1 := h19760c.2.1
                        have p19760_2 := h19760c.2.2.1
                        have p19760_3 := h19760c.2.2.2
                        linarith only [hlam, p19760_0]
                      · have p19760_0 := h19760c.1
                        have p19760_1 := h19760c.2.1
                        have p19760_2 := h19760c.2.2.1
                        have p19760_3 := h19760c.2.2.2
                        rcases p19760_3 (m.d 0 1) (by simp) with h19800 | h19800
                        · rcases p19760_3 (m.d 1 2) (by simp) with h19801 | h19801
                          · rcases p19760_3 (m.d 1 3) (by simp) with h19802 | h19802
                            · rcases p19760_3 (m.d 1 4) (by simp) with h19803 | h19803
                              · rcases p19760_3 (m.d 1 5) (by simp) with h19804 | h19804
                                · linarith only [h19755, h19804, hlam]
                                · rcases h1emax with h19806 | h19806 | h19806 | h19806 | h19806
                                  · linarith only [h0, h19751, h19752, h19757, h19759, h19806, hc45, hlam, hphi, ht01, ht0b, ht5b, p19760_1]
                                  · linarith only [h19751, h19752, h19757, h19759, h19806, hc45, hlam, hphi, ht01, ht0b, ht5b, p19760_1]
                                  · linarith only [h19749, h19751, h19752, h19757, h19759, h19806, hc45, hlam, hphi, ht01, ht0b, ht5b, p19760_1]
                                  · linarith only [h19752, h19757, h19759, h19806, hc45, hlam, hphi, ht01, ht0b, ht5b, p19760_1]
                                  · rcases h2bigk with h19811c | h19811c | h19811c | h19811c | h19811c | h19811c | h19811c | h19811c | h19811c | h19811c | h19811c | h19811c | h19811c | h19811c | h19811c | h19811c | h19811c | h19811c | h19811c | h19811c | h19811c | h19811c | h19811c | h19811c | h19811c
                                    · have p19811_0 := h19811c.1
                                      have p19811_1 := h19811c.2.1
                                      have p19811_2 := h19811c.2.2.1
                                      have p19811_3 := h19811c.2.2.2
                                      linarith only [hlam, p19811_0]
                                    · have p19811_0 := h19811c.1
                                      have p19811_1 := h19811c.2.1
                                      have p19811_2 := h19811c.2.2.1
                                      have p19811_3 := h19811c.2.2.2
                                      linarith only [h19751, h19752, h19757, h19759, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p19760_1, p19811_1]
                                    · have p19811_0 := h19811c.1
                                      have p19811_1 := h19811c.2.1
                                      have p19811_2 := h19811c.2.2.1
                                      have p19811_3 := h19811c.2.2.2
                                      linarith only [h4, hlam, p19811_0]
                                    · have p19811_0 := h19811c.1
                                      have p19811_1 := h19811c.2.1
                                      have p19811_2 := h19811c.2.2.1
                                      have p19811_3 := h19811c.2.2.2
                                      linarith only [h19756, h19759, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p19811_1]
                                    · have p19811_0 := h19811c.1
                                      have p19811_1 := h19811c.2.1
                                      have p19811_2 := h19811c.2.2.1
                                      have p19811_3 := h19811c.2.2.2
                                      rcases p19811_3 (m.d 0 2) (by simp) with h19816 | h19816
                                      · rcases p19811_3 (m.d 1 2) (by simp) with h19817 | h19817
                                        · linarith only [h0, h19817, hlam]
                                        · linarith only [h19752, h19817, hlam]
                                      · linarith only [h19816, hlam, p19811_0]
                                    · have p19811_0 := h19811c.1
                                      have p19811_1 := h19811c.2.1
                                      have p19811_2 := h19811c.2.2.1
                                      have p19811_3 := h19811c.2.2.2
                                      linarith only [h0, hlam, p19811_1]
                                    · have p19811_0 := h19811c.1
                                      have p19811_1 := h19811c.2.1
                                      have p19811_2 := h19811c.2.2.1
                                      have p19811_3 := h19811c.2.2.2
                                      linarith only [hlam, p19811_0]
                                    · have p19811_0 := h19811c.1
                                      have p19811_1 := h19811c.2.1
                                      have p19811_2 := h19811c.2.2.1
                                      have p19811_3 := h19811c.2.2.2
                                      linarith only [h19749, hlam, p19811_0]
                                    · have p19811_0 := h19811c.1
                                      have p19811_1 := h19811c.2.1
                                      have p19811_2 := h19811c.2.2.1
                                      have p19811_3 := h19811c.2.2.2
                                      linarith only [h1, h19749, h19756, h19759, hc01, hc45, hlam, hphi, ht0b, ht5b, p19811_1]
                                    · have p19811_0 := h19811c.1
                                      have p19811_1 := h19811c.2.1
                                      have p19811_2 := h19811c.2.2.1
                                      have p19811_3 := h19811c.2.2.2
                                      rcases p19811_3 (m.d 0 2) (by simp) with h19825 | h19825
                                      · rcases p19811_3 (m.d 1 2) (by simp) with h19826 | h19826
                                        · rcases p19811_3 (m.d 2 3) (by simp) with h19827 | h19827
                                          · rcases p19811_3 (m.d 2 4) (by simp) with h19828 | h19828
                                            · linarith only [h19751, h19828, hlam]
                                            · linarith only [h19758, h19828, hlam]
                                          · linarith only [h19757, h19827, hlam]
                                        · linarith only [h19826, hlam, p19811_0]
                                      · linarith only [h19745, h19825, hlam]
                                    · have p19811_0 := h19811c.1
                                      have p19811_1 := h19811c.2.1
                                      have p19811_2 := h19811c.2.2.1
                                      have p19811_3 := h19811c.2.2.2
                                      linarith only [h19744, h19752, h19757, h19759, h2, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p19760_1, p19811_1]
                                    · have p19811_0 := h19811c.1
                                      have p19811_1 := h19811c.2.1
                                      have p19811_2 := h19811c.2.2.1
                                      have p19811_3 := h19811c.2.2.2
                                      linarith only [h19751, h19756, h19759, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p19811_1]
                                    · have p19811_0 := h19811c.1
                                      have p19811_1 := h19811c.2.1
                                      have p19811_2 := h19811c.2.2.1
                                      have p19811_3 := h19811c.2.2.2
                                      linarith only [hlam, p19811_0]
                                    · have p19811_0 := h19811c.1
                                      have p19811_1 := h19811c.2.1
                                      have p19811_2 := h19811c.2.2.1
                                      have p19811_3 := h19811c.2.2.2
                                      rcases p19811_3 (m.d 0 2) (by simp) with h19837 | h19837
                                      · linarith only [h19837, h4, hlam]
                                      · linarith only [h19744, h19837, hlam]
                                    · have p19811_0 := h19811c.1
                                      have p19811_1 := h19811c.2.1
                                      have p19811_2 := h19811c.2.2.1
                                      have p19811_3 := h19811c.2.2.2
                                      linarith only [h19744, h19752, h2, h4, hlam, p19760_1, p19811_2]
                                    · have p19811_0 := h19811c.1
                                      have p19811_1 := h19811c.2.1
                                      have p19811_2 := h19811c.2.2.1
                                      have p19811_3 := h19811c.2.2.2
                                      linarith only [h19744, hlam, p19811_0]
                                    · have p19811_0 := h19811c.1
                                      have p19811_1 := h19811c.2.1
                                      have p19811_2 := h19811c.2.2.1
                                      have p19811_3 := h19811c.2.2.2
                                      linarith only [h19751, hlam, p19811_0]
                                    · have p19811_0 := h19811c.1
                                      have p19811_1 := h19811c.2.1
                                      have p19811_2 := h19811c.2.2.1
                                      have p19811_3 := h19811c.2.2.2
                                      linarith only [h19756, hlam, p19811_0]
                                    · have p19811_0 := h19811c.1
                                      have p19811_1 := h19811c.2.1
                                      have p19811_2 := h19811c.2.2.1
                                      have p19811_3 := h19811c.2.2.2
                                      linarith only [hlam, p19811_0]
                                    · have p19811_0 := h19811c.1
                                      have p19811_1 := h19811c.2.1
                                      have p19811_2 := h19811c.2.2.1
                                      have p19811_3 := h19811c.2.2.2
                                      linarith only [h19744, h19757, h19759, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p19811_1]
                                    · have p19811_0 := h19811c.1
                                      have p19811_1 := h19811c.2.1
                                      have p19811_2 := h19811c.2.2.1
                                      have p19811_3 := h19811c.2.2.2
                                      linarith only [h19745, hlam, p19811_0]
                                    · have p19811_0 := h19811c.1
                                      have p19811_1 := h19811c.2.1
                                      have p19811_2 := h19811c.2.2.1
                                      have p19811_3 := h19811c.2.2.2
                                      linarith only [h19752, hlam, p19811_0]
                                    · have p19811_0 := h19811c.1
                                      have p19811_1 := h19811c.2.1
                                      have p19811_2 := h19811c.2.2.1
                                      have p19811_3 := h19811c.2.2.2
                                      linarith only [h19757, hlam, p19811_0]
                                    · have p19811_0 := h19811c.1
                                      have p19811_1 := h19811c.2.1
                                      have p19811_2 := h19811c.2.2.1
                                      have p19811_3 := h19811c.2.2.2
                                      linarith only [h19758, hlam, p19811_1]
                                    · have p19811_0 := h19811c.1
                                      have p19811_1 := h19811c.2.1
                                      have p19811_2 := h19811c.2.2.1
                                      have p19811_3 := h19811c.2.2.2
                                      linarith only [hlam, p19811_0]
                              · linarith only [h19755, h19803, hlam]
                            · linarith only [h19754, h19802, hlam]
                          · linarith only [h19752, h19801, hlam]
                        · linarith only [h19800, h3, hlam]
                      · have p19760_0 := h19760c.1
                        have p19760_1 := h19760c.2.1
                        have p19760_2 := h19760c.2.2.1
                        have p19760_3 := h19760c.2.2.2
                        linarith only [h3, hlam, p19760_0]
                      · have p19760_0 := h19760c.1
                        have p19760_1 := h19760c.2.1
                        have p19760_2 := h19760c.2.2.1
                        have p19760_3 := h19760c.2.2.2
                        linarith only [h19752, hlam, p19760_0]
                      · have p19760_0 := h19760c.1
                        have p19760_1 := h19760c.2.1
                        have p19760_2 := h19760c.2.2.1
                        have p19760_3 := h19760c.2.2.2
                        linarith only [h19754, hlam, p19760_0]
                      · have p19760_0 := h19760c.1
                        have p19760_1 := h19760c.2.1
                        have p19760_2 := h19760c.2.2.1
                        have p19760_3 := h19760c.2.2.2
                        linarith only [h19755, hlam, p19760_0]
                      · have p19760_0 := h19760c.1
                        have p19760_1 := h19760c.2.1
                        have p19760_2 := h19760c.2.2.1
                        have p19760_3 := h19760c.2.2.2
                        linarith only [hlam, p19760_0]
                    · linarith only [h0, h19751, h19758, h19759, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h19861 | h19861
                    · linarith only [h19756, h19758, h19861, hlam]
                    · rcases h1bigk with h19863c | h19863c | h19863c | h19863c | h19863c | h19863c | h19863c | h19863c | h19863c | h19863c | h19863c | h19863c | h19863c | h19863c | h19863c | h19863c | h19863c | h19863c | h19863c | h19863c | h19863c | h19863c | h19863c | h19863c | h19863c
                      · have p19863_0 := h19863c.1
                        have p19863_1 := h19863c.2.1
                        have p19863_2 := h19863c.2.2.1
                        have p19863_3 := h19863c.2.2.2
                        linarith only [hlam, p19863_0]
                      · have p19863_0 := h19863c.1
                        have p19863_1 := h19863c.2.1
                        have p19863_2 := h19863c.2.2.1
                        have p19863_3 := h19863c.2.2.2
                        linarith only [h19751, h19755, h19756, h19758, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p19863_1]
                      · have p19863_0 := h19863c.1
                        have p19863_1 := h19863c.2.1
                        have p19863_2 := h19863c.2.2.1
                        have p19863_3 := h19863c.2.2.2
                        linarith only [h19749, h19751, h19755, h19756, h19758, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p19863_1]
                      · have p19863_0 := h19863c.1
                        have p19863_1 := h19863c.2.1
                        have p19863_2 := h19863c.2.2.1
                        have p19863_3 := h19863c.2.2.2
                        linarith only [h19755, h19756, h19758, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p19863_1]
                      · have p19863_0 := h19863c.1
                        have p19863_1 := h19863c.2.1
                        have p19863_2 := h19863c.2.2.1
                        have p19863_3 := h19863c.2.2.2
                        rcases p19863_3 (m.d 0 1) (by simp) with h19868 | h19868
                        · rcases p19863_3 (m.d 1 2) (by simp) with h19869 | h19869
                          · linarith only [h0, h19869, hlam]
                          · linarith only [h19752, h19869, hlam]
                        · linarith only [h19868, hlam, p19863_0]
                      · have p19863_0 := h19863c.1
                        have p19863_1 := h19863c.2.1
                        have p19863_2 := h19863c.2.2.1
                        have p19863_3 := h19863c.2.2.2
                        linarith only [h0, hlam, p19863_0]
                      · have p19863_0 := h19863c.1
                        have p19863_1 := h19863c.2.1
                        have p19863_2 := h19863c.2.2.1
                        have p19863_3 := h19863c.2.2.2
                        linarith only [hlam, p19863_0]
                      · have p19863_0 := h19863c.1
                        have p19863_1 := h19863c.2.1
                        have p19863_2 := h19863c.2.2.1
                        have p19863_3 := h19863c.2.2.2
                        linarith only [h19749, hlam, p19863_1]
                      · have p19863_0 := h19863c.1
                        have p19863_1 := h19863c.2.1
                        have p19863_2 := h19863c.2.2.1
                        have p19863_3 := h19863c.2.2.2
                        linarith only [h0, h19755, h19756, h19758, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p19863_1]
                      · have p19863_0 := h19863c.1
                        have p19863_1 := h19863c.2.1
                        have p19863_2 := h19863c.2.2.1
                        have p19863_3 := h19863c.2.2.2
                        linarith only [h0, h19755, h19756, h19758, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p19863_1]
                      · have p19863_0 := h19863c.1
                        have p19863_1 := h19863c.2.1
                        have p19863_2 := h19863c.2.2.1
                        have p19863_3 := h19863c.2.2.2
                        linarith only [h1, hlam, p19863_0]
                      · have p19863_0 := h19863c.1
                        have p19863_1 := h19863c.2.1
                        have p19863_2 := h19863c.2.2.1
                        have p19863_3 := h19863c.2.2.2
                        linarith only [h1, h19751, h19756, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p19863_1]
                      · have p19863_0 := h19863c.1
                        have p19863_1 := h19863c.2.1
                        have p19863_2 := h19863c.2.2.1
                        have p19863_3 := h19863c.2.2.2
                        linarith only [hlam, p19863_0]
                      · have p19863_0 := h19863c.1
                        have p19863_1 := h19863c.2.1
                        have p19863_2 := h19863c.2.2.1
                        have p19863_3 := h19863c.2.2.2
                        linarith only [h1, h19755, h19756, h19758, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p19863_1]
                      · have p19863_0 := h19863c.1
                        have p19863_1 := h19863c.2.1
                        have p19863_2 := h19863c.2.2.1
                        have p19863_3 := h19863c.2.2.2
                        linarith only [h1, h19755, h19756, h19758, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p19863_1]
                      · have p19863_0 := h19863c.1
                        have p19863_1 := h19863c.2.1
                        have p19863_2 := h19863c.2.2.1
                        have p19863_3 := h19863c.2.2.2
                        linarith only [h2, hlam, p19863_0]
                      · have p19863_0 := h19863c.1
                        have p19863_1 := h19863c.2.1
                        have p19863_2 := h19863c.2.2.1
                        have p19863_3 := h19863c.2.2.2
                        linarith only [h19751, hlam, p19863_0]
                      · have p19863_0 := h19863c.1
                        have p19863_1 := h19863c.2.1
                        have p19863_2 := h19863c.2.2.1
                        have p19863_3 := h19863c.2.2.2
                        linarith only [h19753, hlam, p19863_1]
                      · have p19863_0 := h19863c.1
                        have p19863_1 := h19863c.2.1
                        have p19863_2 := h19863c.2.2.1
                        have p19863_3 := h19863c.2.2.2
                        linarith only [hlam, p19863_0]
                      · have p19863_0 := h19863c.1
                        have p19863_1 := h19863c.2.1
                        have p19863_2 := h19863c.2.2.1
                        have p19863_3 := h19863c.2.2.2
                        linarith only [h0, h19751, h19755, h19756, h19758, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p19863_1]
                      · have p19863_0 := h19863c.1
                        have p19863_1 := h19863c.2.1
                        have p19863_2 := h19863c.2.2.1
                        have p19863_3 := h19863c.2.2.2
                        linarith only [h3, hlam, p19863_0]
                      · have p19863_0 := h19863c.1
                        have p19863_1 := h19863c.2.1
                        have p19863_2 := h19863c.2.2.1
                        have p19863_3 := h19863c.2.2.2
                        linarith only [h19752, hlam, p19863_0]
                      · have p19863_0 := h19863c.1
                        have p19863_1 := h19863c.2.1
                        have p19863_2 := h19863c.2.2.1
                        have p19863_3 := h19863c.2.2.2
                        linarith only [h19754, hlam, p19863_0]
                      · have p19863_0 := h19863c.1
                        have p19863_1 := h19863c.2.1
                        have p19863_2 := h19863c.2.2.1
                        have p19863_3 := h19863c.2.2.2
                        linarith only [h19755, hlam, p19863_0]
                      · have p19863_0 := h19863c.1
                        have p19863_1 := h19863c.2.1
                        have p19863_2 := h19863c.2.2.1
                        have p19863_3 := h19863c.2.2.2
                        linarith only [hlam, p19863_0]
                · linarith only [h19747, h19757, h4, hlam]
              · linarith only [h19746, h19756, h4, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h19895 | h19895
              · rcases m.htr 2 3 5 (by decide) (by decide) with h19896 | h19896
                · rcases m.htr 2 4 5 (by decide) (by decide) with h19897 | h19897
                  · linarith only [h19751, h19755, h19897, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h19899 | h19899
                    · linarith only [h19751, h19755, h19895, h19899, hlam]
                    · rcases h1bigk with h19901c | h19901c | h19901c | h19901c | h19901c | h19901c | h19901c | h19901c | h19901c | h19901c | h19901c | h19901c | h19901c | h19901c | h19901c | h19901c | h19901c | h19901c | h19901c | h19901c | h19901c | h19901c | h19901c | h19901c | h19901c
                      · have p19901_0 := h19901c.1
                        have p19901_1 := h19901c.2.1
                        have p19901_2 := h19901c.2.2.1
                        have p19901_3 := h19901c.2.2.2
                        linarith only [hlam, p19901_0]
                      · have p19901_0 := h19901c.1
                        have p19901_1 := h19901c.2.1
                        have p19901_2 := h19901c.2.2.1
                        have p19901_3 := h19901c.2.2.2
                        rcases p19901_3 (m.d 0 1) (by simp) with h19903 | h19903
                        · rcases p19901_3 (m.d 1 2) (by simp) with h19904 | h19904
                          · linarith only [h19904, hlam, p19901_0]
                          · rcases p19901_3 (m.d 1 3) (by simp) with h19906 | h19906
                            · linarith only [h1, h19906, hlam]
                            · linarith only [h19749, h19906, hlam]
                        · linarith only [h19903, hlam, p19901_0]
                      · have p19901_0 := h19901c.1
                        have p19901_1 := h19901c.2.1
                        have p19901_2 := h19901c.2.2.1
                        have p19901_3 := h19901c.2.2.2
                        rcases p19901_3 (m.d 0 1) (by simp) with h19910 | h19910
                        · rcases p19901_3 (m.d 1 2) (by simp) with h19911 | h19911
                          · linarith only [h0, h19911, hlam]
                          · rcases p19901_3 (m.d 1 3) (by simp) with h19913 | h19913
                            · linarith only [h19913, hlam, p19901_0]
                            · rcases p19901_3 (m.d 1 4) (by simp) with h19915 | h19915
                              · linarith only [h19915, h2, hlam]
                              · rcases p19901_3 (m.d 1 5) (by simp) with h19917 | h19917
                                · linarith only [h19917, h3, hlam]
                                · rcases h1emax with h19919 | h19919 | h19919 | h19919 | h19919
                                  · linarith only [h19749, h19919, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p19901_1]
                                  · rcases h2bigk with h19921c | h19921c | h19921c | h19921c | h19921c | h19921c | h19921c | h19921c | h19921c | h19921c | h19921c | h19921c | h19921c | h19921c | h19921c | h19921c | h19921c | h19921c | h19921c | h19921c | h19921c | h19921c | h19921c | h19921c | h19921c
                                    · have p19921_0 := h19921c.1
                                      have p19921_1 := h19921c.2.1
                                      have p19921_2 := h19921c.2.2.1
                                      have p19921_3 := h19921c.2.2.2
                                      linarith only [hlam, p19921_0]
                                    · have p19921_0 := h19921c.1
                                      have p19921_1 := h19921c.2.1
                                      have p19921_2 := h19921c.2.2.1
                                      have p19921_3 := h19921c.2.2.2
                                      linarith only [h19752, h19895, h19897, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p19921_1]
                                    · have p19921_0 := h19921c.1
                                      have p19921_1 := h19921c.2.1
                                      have p19921_2 := h19921c.2.2.1
                                      have p19921_3 := h19921c.2.2.2
                                      linarith only [h4, hlam, p19921_0]
                                    · have p19921_0 := h19921c.1
                                      have p19921_1 := h19921c.2.1
                                      have p19921_2 := h19921c.2.2.1
                                      have p19921_3 := h19921c.2.2.2
                                      rcases p19921_3 (m.d 0 2) (by simp) with h19925 | h19925
                                      · rcases p19921_3 (m.d 1 2) (by simp) with h19926 | h19926
                                        · linarith only [h0, h19926, hlam]
                                        · linarith only [h19751, h19926, hlam]
                                      · linarith only [h19925, hlam, p19921_0]
                                    · have p19921_0 := h19921c.1
                                      have p19921_1 := h19921c.2.1
                                      have p19921_2 := h19921c.2.2.1
                                      have p19921_3 := h19921c.2.2.2
                                      rcases p19921_3 (m.d 0 2) (by simp) with h19930 | h19930
                                      · rcases p19921_3 (m.d 1 2) (by simp) with h19931 | h19931
                                        · linarith only [h0, h19931, hlam]
                                        · linarith only [h19752, h19931, hlam]
                                      · linarith only [h19930, hlam, p19921_0]
                                    · have p19921_0 := h19921c.1
                                      have p19921_1 := h19921c.2.1
                                      have p19921_2 := h19921c.2.2.1
                                      have p19921_3 := h19921c.2.2.2
                                      linarith only [h0, hlam, p19921_1]
                                    · have p19921_0 := h19921c.1
                                      have p19921_1 := h19921c.2.1
                                      have p19921_2 := h19921c.2.2.1
                                      have p19921_3 := h19921c.2.2.2
                                      linarith only [hlam, p19921_0]
                                    · have p19921_0 := h19921c.1
                                      have p19921_1 := h19921c.2.1
                                      have p19921_2 := h19921c.2.2.1
                                      have p19921_3 := h19921c.2.2.2
                                      linarith only [h19749, hlam, p19921_0]
                                    · have p19921_0 := h19921c.1
                                      have p19921_1 := h19921c.2.1
                                      have p19921_2 := h19921c.2.2.1
                                      have p19921_3 := h19921c.2.2.2
                                      linarith only [h19749, h19895, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p19901_1, p19921_1]
                                    · have p19921_0 := h19921c.1
                                      have p19921_1 := h19921c.2.1
                                      have p19921_2 := h19921c.2.2.1
                                      have p19921_3 := h19921c.2.2.2
                                      linarith only [h19749, h19895, h19897, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p19901_1, p19921_1]
                                    · have p19921_0 := h19921c.1
                                      have p19921_1 := h19921c.2.1
                                      have p19921_2 := h19921c.2.2.1
                                      have p19921_3 := h19921c.2.2.2
                                      linarith only [h19744, h19748, h19751, h19755, h19895, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p19921_1]
                                    · have p19921_0 := h19921c.1
                                      have p19921_1 := h19921c.2.1
                                      have p19921_2 := h19921c.2.2.1
                                      have p19921_3 := h19921c.2.2.2
                                      rcases p19921_3 (m.d 0 2) (by simp) with h19941 | h19941
                                      · linarith only [h19941, h4, hlam]
                                      · linarith only [h0, h19941, hlam]
                                    · have p19921_0 := h19921c.1
                                      have p19921_1 := h19921c.2.1
                                      have p19921_2 := h19921c.2.2.1
                                      have p19921_3 := h19921c.2.2.2
                                      linarith only [hlam, p19921_0]
                                    · have p19921_0 := h19921c.1
                                      have p19921_1 := h19921c.2.1
                                      have p19921_2 := h19921c.2.2.1
                                      have p19921_3 := h19921c.2.2.2
                                      linarith only [h19744, h19748, h19751, h19755, h4, hlam, p19921_2]
                                    · have p19921_0 := h19921c.1
                                      have p19921_1 := h19921c.2.1
                                      have p19921_2 := h19921c.2.2.1
                                      have p19921_3 := h19921c.2.2.2
                                      rcases p19921_3 (m.d 0 2) (by simp) with h19946 | h19946
                                      · linarith only [h19946, h4, hlam]
                                      · linarith only [h19745, h19946, hlam]
                                    · have p19921_0 := h19921c.1
                                      have p19921_1 := h19921c.2.1
                                      have p19921_2 := h19921c.2.2.1
                                      have p19921_3 := h19921c.2.2.2
                                      linarith only [h19744, hlam, p19921_0]
                                    · have p19921_0 := h19921c.1
                                      have p19921_1 := h19921c.2.1
                                      have p19921_2 := h19921c.2.2.1
                                      have p19921_3 := h19921c.2.2.2
                                      linarith only [h19751, hlam, p19921_0]
                                    · have p19921_0 := h19921c.1
                                      have p19921_1 := h19921c.2.1
                                      have p19921_2 := h19921c.2.2.1
                                      have p19921_3 := h19921c.2.2.2
                                      linarith only [h19895, hlam, p19921_0]
                                    · have p19921_0 := h19921c.1
                                      have p19921_1 := h19921c.2.1
                                      have p19921_2 := h19921c.2.2.1
                                      have p19921_3 := h19921c.2.2.2
                                      linarith only [hlam, p19921_0]
                                    · have p19921_0 := h19921c.1
                                      have p19921_1 := h19921c.2.1
                                      have p19921_2 := h19921c.2.2.1
                                      have p19921_3 := h19921c.2.2.2
                                      linarith only [h19897, hlam, p19921_0]
                                    · have p19921_0 := h19921c.1
                                      have p19921_1 := h19921c.2.1
                                      have p19921_2 := h19921c.2.2.1
                                      have p19921_3 := h19921c.2.2.2
                                      linarith only [h19745, hlam, p19921_0]
                                    · have p19921_0 := h19921c.1
                                      have p19921_1 := h19921c.2.1
                                      have p19921_2 := h19921c.2.2.1
                                      have p19921_3 := h19921c.2.2.2
                                      linarith only [h19752, hlam, p19921_0]
                                    · have p19921_0 := h19921c.1
                                      have p19921_1 := h19921c.2.1
                                      have p19921_2 := h19921c.2.2.1
                                      have p19921_3 := h19921c.2.2.2
                                      linarith only [h19896, hlam, p19921_0]
                                    · have p19921_0 := h19921c.1
                                      have p19921_1 := h19921c.2.1
                                      have p19921_2 := h19921c.2.2.1
                                      have p19921_3 := h19921c.2.2.2
                                      linarith only [h0, h19752, h19895, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p19921_1]
                                    · have p19921_0 := h19921c.1
                                      have p19921_1 := h19921c.2.1
                                      have p19921_2 := h19921c.2.2.1
                                      have p19921_3 := h19921c.2.2.2
                                      linarith only [hlam, p19921_0]
                                  · rcases h2bigk with h19959c | h19959c | h19959c | h19959c | h19959c | h19959c | h19959c | h19959c | h19959c | h19959c | h19959c | h19959c | h19959c | h19959c | h19959c | h19959c | h19959c | h19959c | h19959c | h19959c | h19959c | h19959c | h19959c | h19959c | h19959c
                                    · have p19959_0 := h19959c.1
                                      have p19959_1 := h19959c.2.1
                                      have p19959_2 := h19959c.2.2.1
                                      have p19959_3 := h19959c.2.2.2
                                      linarith only [hlam, p19959_0]
                                    · have p19959_0 := h19959c.1
                                      have p19959_1 := h19959c.2.1
                                      have p19959_2 := h19959c.2.2.1
                                      have p19959_3 := h19959c.2.2.2
                                      linarith only [h4, hc12, hc23, hlam, hphi, p19959_1]
                                    · have p19959_0 := h19959c.1
                                      have p19959_1 := h19959c.2.1
                                      have p19959_2 := h19959c.2.2.1
                                      have p19959_3 := h19959c.2.2.2
                                      linarith only [h4, hlam, p19959_0]
                                    · have p19959_0 := h19959c.1
                                      have p19959_1 := h19959c.2.1
                                      have p19959_2 := h19959c.2.2.1
                                      have p19959_3 := h19959c.2.2.2
                                      rcases p19959_3 (m.d 0 2) (by simp) with h19963 | h19963
                                      · rcases p19959_3 (m.d 1 2) (by simp) with h19964 | h19964
                                        · linarith only [h0, h19964, hlam]
                                        · linarith only [h19751, h19964, hlam]
                                      · linarith only [h19963, hlam, p19959_0]
                                    · have p19959_0 := h19959c.1
                                      have p19959_1 := h19959c.2.1
                                      have p19959_2 := h19959c.2.2.1
                                      have p19959_3 := h19959c.2.2.2
                                      rcases p19959_3 (m.d 0 2) (by simp) with h19968 | h19968
                                      · rcases p19959_3 (m.d 1 2) (by simp) with h19969 | h19969
                                        · linarith only [h0, h19969, hlam]
                                        · linarith only [h19752, h19969, hlam]
                                      · linarith only [h19968, hlam, p19959_0]
                                    · have p19959_0 := h19959c.1
                                      have p19959_1 := h19959c.2.1
                                      have p19959_2 := h19959c.2.2.1
                                      have p19959_3 := h19959c.2.2.2
                                      linarith only [h0, hlam, p19959_1]
                                    · have p19959_0 := h19959c.1
                                      have p19959_1 := h19959c.2.1
                                      have p19959_2 := h19959c.2.2.1
                                      have p19959_3 := h19959c.2.2.2
                                      linarith only [hlam, p19959_0]
                                    · have p19959_0 := h19959c.1
                                      have p19959_1 := h19959c.2.1
                                      have p19959_2 := h19959c.2.2.1
                                      have p19959_3 := h19959c.2.2.2
                                      linarith only [h19749, hlam, p19959_0]
                                    · have p19959_0 := h19959c.1
                                      have p19959_1 := h19959c.2.1
                                      have p19959_2 := h19959c.2.2.1
                                      have p19959_3 := h19959c.2.2.2
                                      linarith only [h19749, h19895, h19919, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19959_1]
                                    · have p19959_0 := h19959c.1
                                      have p19959_1 := h19959c.2.1
                                      have p19959_2 := h19959c.2.2.1
                                      have p19959_3 := h19959c.2.2.2
                                      linarith only [h19749, h19896, h19899, h19919, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19959_1]
                                    · have p19959_0 := h19959c.1
                                      have p19959_1 := h19959c.2.1
                                      have p19959_2 := h19959c.2.2.1
                                      have p19959_3 := h19959c.2.2.2
                                      linarith only [h19744, h19748, h19751, h19755, h19895, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p19959_1]
                                    · have p19959_0 := h19959c.1
                                      have p19959_1 := h19959c.2.1
                                      have p19959_2 := h19959c.2.2.1
                                      have p19959_3 := h19959c.2.2.2
                                      rcases p19959_3 (m.d 0 2) (by simp) with h19979 | h19979
                                      · linarith only [h19979, h4, hlam]
                                      · linarith only [h0, h19979, hlam]
                                    · have p19959_0 := h19959c.1
                                      have p19959_1 := h19959c.2.1
                                      have p19959_2 := h19959c.2.2.1
                                      have p19959_3 := h19959c.2.2.2
                                      linarith only [hlam, p19959_0]
                                    · have p19959_0 := h19959c.1
                                      have p19959_1 := h19959c.2.1
                                      have p19959_2 := h19959c.2.2.1
                                      have p19959_3 := h19959c.2.2.2
                                      linarith only [h19744, h19748, h19751, h19755, h4, hlam, p19959_2]
                                    · have p19959_0 := h19959c.1
                                      have p19959_1 := h19959c.2.1
                                      have p19959_2 := h19959c.2.2.1
                                      have p19959_3 := h19959c.2.2.2
                                      rcases p19959_3 (m.d 0 2) (by simp) with h19984 | h19984
                                      · linarith only [h19984, h4, hlam]
                                      · linarith only [h19745, h19984, hlam]
                                    · have p19959_0 := h19959c.1
                                      have p19959_1 := h19959c.2.1
                                      have p19959_2 := h19959c.2.2.1
                                      have p19959_3 := h19959c.2.2.2
                                      linarith only [h19744, hlam, p19959_0]
                                    · have p19959_0 := h19959c.1
                                      have p19959_1 := h19959c.2.1
                                      have p19959_2 := h19959c.2.2.1
                                      have p19959_3 := h19959c.2.2.2
                                      linarith only [h19751, hlam, p19959_0]
                                    · have p19959_0 := h19959c.1
                                      have p19959_1 := h19959c.2.1
                                      have p19959_2 := h19959c.2.2.1
                                      have p19959_3 := h19959c.2.2.2
                                      linarith only [h19895, hlam, p19959_0]
                                    · have p19959_0 := h19959c.1
                                      have p19959_1 := h19959c.2.1
                                      have p19959_2 := h19959c.2.2.1
                                      have p19959_3 := h19959c.2.2.2
                                      linarith only [hlam, p19959_0]
                                    · have p19959_0 := h19959c.1
                                      have p19959_1 := h19959c.2.1
                                      have p19959_2 := h19959c.2.2.1
                                      have p19959_3 := h19959c.2.2.2
                                      linarith only [h19897, hlam, p19959_0]
                                    · have p19959_0 := h19959c.1
                                      have p19959_1 := h19959c.2.1
                                      have p19959_2 := h19959c.2.2.1
                                      have p19959_3 := h19959c.2.2.2
                                      linarith only [h19745, hlam, p19959_0]
                                    · have p19959_0 := h19959c.1
                                      have p19959_1 := h19959c.2.1
                                      have p19959_2 := h19959c.2.2.1
                                      have p19959_3 := h19959c.2.2.2
                                      linarith only [h19752, hlam, p19959_0]
                                    · have p19959_0 := h19959c.1
                                      have p19959_1 := h19959c.2.1
                                      have p19959_2 := h19959c.2.2.1
                                      have p19959_3 := h19959c.2.2.2
                                      linarith only [h19896, hlam, p19959_0]
                                    · have p19959_0 := h19959c.1
                                      have p19959_1 := h19959c.2.1
                                      have p19959_2 := h19959c.2.2.1
                                      have p19959_3 := h19959c.2.2.2
                                      linarith only [h0, h19752, h19895, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p19959_1]
                                    · have p19959_0 := h19959c.1
                                      have p19959_1 := h19959c.2.1
                                      have p19959_2 := h19959c.2.2.1
                                      have p19959_3 := h19959c.2.2.2
                                      linarith only [hlam, p19959_0]
                                  · rcases h2bigk with h19997c | h19997c | h19997c | h19997c | h19997c | h19997c | h19997c | h19997c | h19997c | h19997c | h19997c | h19997c | h19997c | h19997c | h19997c | h19997c | h19997c | h19997c | h19997c | h19997c | h19997c | h19997c | h19997c | h19997c | h19997c
                                    · have p19997_0 := h19997c.1
                                      have p19997_1 := h19997c.2.1
                                      have p19997_2 := h19997c.2.2.1
                                      have p19997_3 := h19997c.2.2.2
                                      linarith only [hlam, p19997_0]
                                    · have p19997_0 := h19997c.1
                                      have p19997_1 := h19997c.2.1
                                      have p19997_2 := h19997c.2.2.1
                                      have p19997_3 := h19997c.2.2.2
                                      linarith only [h4, hc12, hc23, hlam, hphi, p19997_1]
                                    · have p19997_0 := h19997c.1
                                      have p19997_1 := h19997c.2.1
                                      have p19997_2 := h19997c.2.2.1
                                      have p19997_3 := h19997c.2.2.2
                                      linarith only [h4, hlam, p19997_0]
                                    · have p19997_0 := h19997c.1
                                      have p19997_1 := h19997c.2.1
                                      have p19997_2 := h19997c.2.2.1
                                      have p19997_3 := h19997c.2.2.2
                                      rcases p19997_3 (m.d 0 2) (by simp) with h20001 | h20001
                                      · rcases p19997_3 (m.d 1 2) (by simp) with h20002 | h20002
                                        · linarith only [h0, h20002, hlam]
                                        · linarith only [h19751, h20002, hlam]
                                      · linarith only [h20001, hlam, p19997_0]
                                    · have p19997_0 := h19997c.1
                                      have p19997_1 := h19997c.2.1
                                      have p19997_2 := h19997c.2.2.1
                                      have p19997_3 := h19997c.2.2.2
                                      rcases p19997_3 (m.d 0 2) (by simp) with h20006 | h20006
                                      · rcases p19997_3 (m.d 1 2) (by simp) with h20007 | h20007
                                        · linarith only [h0, h20007, hlam]
                                        · linarith only [h19752, h20007, hlam]
                                      · linarith only [h20006, hlam, p19997_0]
                                    · have p19997_0 := h19997c.1
                                      have p19997_1 := h19997c.2.1
                                      have p19997_2 := h19997c.2.2.1
                                      have p19997_3 := h19997c.2.2.2
                                      linarith only [h0, hlam, p19997_1]
                                    · have p19997_0 := h19997c.1
                                      have p19997_1 := h19997c.2.1
                                      have p19997_2 := h19997c.2.2.1
                                      have p19997_3 := h19997c.2.2.2
                                      linarith only [hlam, p19997_0]
                                    · have p19997_0 := h19997c.1
                                      have p19997_1 := h19997c.2.1
                                      have p19997_2 := h19997c.2.2.1
                                      have p19997_3 := h19997c.2.2.2
                                      linarith only [h19749, hlam, p19997_0]
                                    · have p19997_0 := h19997c.1
                                      have p19997_1 := h19997c.2.1
                                      have p19997_2 := h19997c.2.2.1
                                      have p19997_3 := h19997c.2.2.2
                                      linarith only [h19749, h19895, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p19901_1, p19997_1]
                                    · have p19997_0 := h19997c.1
                                      have p19997_1 := h19997c.2.1
                                      have p19997_2 := h19997c.2.2.1
                                      have p19997_3 := h19997c.2.2.2
                                      linarith only [h19749, h19896, h19899, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p19901_1, p19997_1]
                                    · have p19997_0 := h19997c.1
                                      have p19997_1 := h19997c.2.1
                                      have p19997_2 := h19997c.2.2.1
                                      have p19997_3 := h19997c.2.2.2
                                      linarith only [h19744, h19748, h19751, h19755, h19895, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p19997_1]
                                    · have p19997_0 := h19997c.1
                                      have p19997_1 := h19997c.2.1
                                      have p19997_2 := h19997c.2.2.1
                                      have p19997_3 := h19997c.2.2.2
                                      rcases p19997_3 (m.d 0 2) (by simp) with h20017 | h20017
                                      · linarith only [h20017, h4, hlam]
                                      · linarith only [h0, h20017, hlam]
                                    · have p19997_0 := h19997c.1
                                      have p19997_1 := h19997c.2.1
                                      have p19997_2 := h19997c.2.2.1
                                      have p19997_3 := h19997c.2.2.2
                                      linarith only [hlam, p19997_0]
                                    · have p19997_0 := h19997c.1
                                      have p19997_1 := h19997c.2.1
                                      have p19997_2 := h19997c.2.2.1
                                      have p19997_3 := h19997c.2.2.2
                                      linarith only [h19744, h19748, h19751, h19755, h4, hlam, p19997_2]
                                    · have p19997_0 := h19997c.1
                                      have p19997_1 := h19997c.2.1
                                      have p19997_2 := h19997c.2.2.1
                                      have p19997_3 := h19997c.2.2.2
                                      rcases p19997_3 (m.d 0 2) (by simp) with h20022 | h20022
                                      · linarith only [h20022, h4, hlam]
                                      · linarith only [h19745, h20022, hlam]
                                    · have p19997_0 := h19997c.1
                                      have p19997_1 := h19997c.2.1
                                      have p19997_2 := h19997c.2.2.1
                                      have p19997_3 := h19997c.2.2.2
                                      linarith only [h19744, hlam, p19997_0]
                                    · have p19997_0 := h19997c.1
                                      have p19997_1 := h19997c.2.1
                                      have p19997_2 := h19997c.2.2.1
                                      have p19997_3 := h19997c.2.2.2
                                      linarith only [h19751, hlam, p19997_0]
                                    · have p19997_0 := h19997c.1
                                      have p19997_1 := h19997c.2.1
                                      have p19997_2 := h19997c.2.2.1
                                      have p19997_3 := h19997c.2.2.2
                                      linarith only [h19895, hlam, p19997_0]
                                    · have p19997_0 := h19997c.1
                                      have p19997_1 := h19997c.2.1
                                      have p19997_2 := h19997c.2.2.1
                                      have p19997_3 := h19997c.2.2.2
                                      linarith only [hlam, p19997_0]
                                    · have p19997_0 := h19997c.1
                                      have p19997_1 := h19997c.2.1
                                      have p19997_2 := h19997c.2.2.1
                                      have p19997_3 := h19997c.2.2.2
                                      linarith only [h19897, hlam, p19997_0]
                                    · have p19997_0 := h19997c.1
                                      have p19997_1 := h19997c.2.1
                                      have p19997_2 := h19997c.2.2.1
                                      have p19997_3 := h19997c.2.2.2
                                      linarith only [h19745, hlam, p19997_0]
                                    · have p19997_0 := h19997c.1
                                      have p19997_1 := h19997c.2.1
                                      have p19997_2 := h19997c.2.2.1
                                      have p19997_3 := h19997c.2.2.2
                                      linarith only [h19752, hlam, p19997_0]
                                    · have p19997_0 := h19997c.1
                                      have p19997_1 := h19997c.2.1
                                      have p19997_2 := h19997c.2.2.1
                                      have p19997_3 := h19997c.2.2.2
                                      linarith only [h19896, hlam, p19997_0]
                                    · have p19997_0 := h19997c.1
                                      have p19997_1 := h19997c.2.1
                                      have p19997_2 := h19997c.2.2.1
                                      have p19997_3 := h19997c.2.2.2
                                      linarith only [h0, h19752, h19895, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p19997_1]
                                    · have p19997_0 := h19997c.1
                                      have p19997_1 := h19997c.2.1
                                      have p19997_2 := h19997c.2.2.1
                                      have p19997_3 := h19997c.2.2.2
                                      linarith only [hlam, p19997_0]
                                  · rcases h2bigk with h20035c | h20035c | h20035c | h20035c | h20035c | h20035c | h20035c | h20035c | h20035c | h20035c | h20035c | h20035c | h20035c | h20035c | h20035c | h20035c | h20035c | h20035c | h20035c | h20035c | h20035c | h20035c | h20035c | h20035c | h20035c
                                    · have p20035_0 := h20035c.1
                                      have p20035_1 := h20035c.2.1
                                      have p20035_2 := h20035c.2.2.1
                                      have p20035_3 := h20035c.2.2.2
                                      linarith only [hlam, p20035_0]
                                    · have p20035_0 := h20035c.1
                                      have p20035_1 := h20035c.2.1
                                      have p20035_2 := h20035c.2.2.1
                                      have p20035_3 := h20035c.2.2.2
                                      linarith only [h4, hc12, hc23, hlam, hphi, p20035_1]
                                    · have p20035_0 := h20035c.1
                                      have p20035_1 := h20035c.2.1
                                      have p20035_2 := h20035c.2.2.1
                                      have p20035_3 := h20035c.2.2.2
                                      linarith only [h4, hlam, p20035_0]
                                    · have p20035_0 := h20035c.1
                                      have p20035_1 := h20035c.2.1
                                      have p20035_2 := h20035c.2.2.1
                                      have p20035_3 := h20035c.2.2.2
                                      rcases p20035_3 (m.d 0 2) (by simp) with h20039 | h20039
                                      · rcases p20035_3 (m.d 1 2) (by simp) with h20040 | h20040
                                        · linarith only [h0, h20040, hlam]
                                        · linarith only [h19751, h20040, hlam]
                                      · linarith only [h20039, hlam, p20035_0]
                                    · have p20035_0 := h20035c.1
                                      have p20035_1 := h20035c.2.1
                                      have p20035_2 := h20035c.2.2.1
                                      have p20035_3 := h20035c.2.2.2
                                      rcases p20035_3 (m.d 0 2) (by simp) with h20044 | h20044
                                      · rcases p20035_3 (m.d 1 2) (by simp) with h20045 | h20045
                                        · linarith only [h0, h20045, hlam]
                                        · linarith only [h19752, h20045, hlam]
                                      · linarith only [h20044, hlam, p20035_0]
                                    · have p20035_0 := h20035c.1
                                      have p20035_1 := h20035c.2.1
                                      have p20035_2 := h20035c.2.2.1
                                      have p20035_3 := h20035c.2.2.2
                                      linarith only [h0, hlam, p20035_1]
                                    · have p20035_0 := h20035c.1
                                      have p20035_1 := h20035c.2.1
                                      have p20035_2 := h20035c.2.2.1
                                      have p20035_3 := h20035c.2.2.2
                                      linarith only [hlam, p20035_0]
                                    · have p20035_0 := h20035c.1
                                      have p20035_1 := h20035c.2.1
                                      have p20035_2 := h20035c.2.2.1
                                      have p20035_3 := h20035c.2.2.2
                                      linarith only [h19749, hlam, p20035_0]
                                    · have p20035_0 := h20035c.1
                                      have p20035_1 := h20035c.2.1
                                      have p20035_2 := h20035c.2.2.1
                                      have p20035_3 := h20035c.2.2.2
                                      linarith only [h19749, h19895, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p19901_1, p20035_1]
                                    · have p20035_0 := h20035c.1
                                      have p20035_1 := h20035c.2.1
                                      have p20035_2 := h20035c.2.2.1
                                      have p20035_3 := h20035c.2.2.2
                                      linarith only [h19749, h19896, h19899, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p19901_1, p20035_1]
                                    · have p20035_0 := h20035c.1
                                      have p20035_1 := h20035c.2.1
                                      have p20035_2 := h20035c.2.2.1
                                      have p20035_3 := h20035c.2.2.2
                                      linarith only [h19744, h19748, h19751, h19755, h19895, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20035_1]
                                    · have p20035_0 := h20035c.1
                                      have p20035_1 := h20035c.2.1
                                      have p20035_2 := h20035c.2.2.1
                                      have p20035_3 := h20035c.2.2.2
                                      rcases p20035_3 (m.d 0 2) (by simp) with h20055 | h20055
                                      · linarith only [h20055, h4, hlam]
                                      · linarith only [h0, h20055, hlam]
                                    · have p20035_0 := h20035c.1
                                      have p20035_1 := h20035c.2.1
                                      have p20035_2 := h20035c.2.2.1
                                      have p20035_3 := h20035c.2.2.2
                                      linarith only [hlam, p20035_0]
                                    · have p20035_0 := h20035c.1
                                      have p20035_1 := h20035c.2.1
                                      have p20035_2 := h20035c.2.2.1
                                      have p20035_3 := h20035c.2.2.2
                                      linarith only [h19744, h19748, h19751, h19755, h4, hlam, p20035_2]
                                    · have p20035_0 := h20035c.1
                                      have p20035_1 := h20035c.2.1
                                      have p20035_2 := h20035c.2.2.1
                                      have p20035_3 := h20035c.2.2.2
                                      rcases p20035_3 (m.d 0 2) (by simp) with h20060 | h20060
                                      · linarith only [h20060, h4, hlam]
                                      · linarith only [h19745, h20060, hlam]
                                    · have p20035_0 := h20035c.1
                                      have p20035_1 := h20035c.2.1
                                      have p20035_2 := h20035c.2.2.1
                                      have p20035_3 := h20035c.2.2.2
                                      linarith only [h19744, hlam, p20035_0]
                                    · have p20035_0 := h20035c.1
                                      have p20035_1 := h20035c.2.1
                                      have p20035_2 := h20035c.2.2.1
                                      have p20035_3 := h20035c.2.2.2
                                      linarith only [h19751, hlam, p20035_0]
                                    · have p20035_0 := h20035c.1
                                      have p20035_1 := h20035c.2.1
                                      have p20035_2 := h20035c.2.2.1
                                      have p20035_3 := h20035c.2.2.2
                                      linarith only [h19895, hlam, p20035_0]
                                    · have p20035_0 := h20035c.1
                                      have p20035_1 := h20035c.2.1
                                      have p20035_2 := h20035c.2.2.1
                                      have p20035_3 := h20035c.2.2.2
                                      linarith only [hlam, p20035_0]
                                    · have p20035_0 := h20035c.1
                                      have p20035_1 := h20035c.2.1
                                      have p20035_2 := h20035c.2.2.1
                                      have p20035_3 := h20035c.2.2.2
                                      linarith only [h19897, hlam, p20035_0]
                                    · have p20035_0 := h20035c.1
                                      have p20035_1 := h20035c.2.1
                                      have p20035_2 := h20035c.2.2.1
                                      have p20035_3 := h20035c.2.2.2
                                      linarith only [h19745, hlam, p20035_0]
                                    · have p20035_0 := h20035c.1
                                      have p20035_1 := h20035c.2.1
                                      have p20035_2 := h20035c.2.2.1
                                      have p20035_3 := h20035c.2.2.2
                                      linarith only [h19752, hlam, p20035_0]
                                    · have p20035_0 := h20035c.1
                                      have p20035_1 := h20035c.2.1
                                      have p20035_2 := h20035c.2.2.1
                                      have p20035_3 := h20035c.2.2.2
                                      linarith only [h19896, hlam, p20035_0]
                                    · have p20035_0 := h20035c.1
                                      have p20035_1 := h20035c.2.1
                                      have p20035_2 := h20035c.2.2.1
                                      have p20035_3 := h20035c.2.2.2
                                      linarith only [h0, h19752, h19895, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20035_1]
                                    · have p20035_0 := h20035c.1
                                      have p20035_1 := h20035c.2.1
                                      have p20035_2 := h20035c.2.2.1
                                      have p20035_3 := h20035c.2.2.2
                                      linarith only [hlam, p20035_0]
                        · linarith only [h19910, hlam, p19901_0]
                      · have p19901_0 := h19901c.1
                        have p19901_1 := h19901c.2.1
                        have p19901_2 := h19901c.2.2.1
                        have p19901_3 := h19901c.2.2.2
                        rcases p19901_3 (m.d 0 1) (by simp) with h20074 | h20074
                        · rcases p19901_3 (m.d 1 2) (by simp) with h20075 | h20075
                          · linarith only [h0, h20075, hlam]
                          · linarith only [h19751, h20075, hlam]
                        · linarith only [h20074, hlam, p19901_0]
                      · have p19901_0 := h19901c.1
                        have p19901_1 := h19901c.2.1
                        have p19901_2 := h19901c.2.2.1
                        have p19901_3 := h19901c.2.2.2
                        rcases p19901_3 (m.d 0 1) (by simp) with h20079 | h20079
                        · rcases p19901_3 (m.d 1 2) (by simp) with h20080 | h20080
                          · linarith only [h0, h20080, hlam]
                          · linarith only [h19752, h20080, hlam]
                        · linarith only [h20079, hlam, p19901_0]
                      · have p19901_0 := h19901c.1
                        have p19901_1 := h19901c.2.1
                        have p19901_2 := h19901c.2.2.1
                        have p19901_3 := h19901c.2.2.2
                        linarith only [h0, hlam, p19901_0]
                      · have p19901_0 := h19901c.1
                        have p19901_1 := h19901c.2.1
                        have p19901_2 := h19901c.2.2.1
                        have p19901_3 := h19901c.2.2.2
                        linarith only [hlam, p19901_0]
                      · have p19901_0 := h19901c.1
                        have p19901_1 := h19901c.2.1
                        have p19901_2 := h19901c.2.2.1
                        have p19901_3 := h19901c.2.2.2
                        linarith only [h19749, hlam, p19901_1]
                      · have p19901_0 := h19901c.1
                        have p19901_1 := h19901c.2.1
                        have p19901_2 := h19901c.2.2.1
                        have p19901_3 := h19901c.2.2.2
                        rcases p19901_3 (m.d 0 1) (by simp) with h20087 | h20087
                        · rcases p19901_3 (m.d 1 2) (by simp) with h20088 | h20088
                          · rcases p19901_3 (m.d 1 3) (by simp) with h20089 | h20089
                            · rcases p19901_3 (m.d 1 4) (by simp) with h20090 | h20090
                              · linarith only [h19751, h20090, hlam]
                              · rcases p19901_3 (m.d 1 5) (by simp) with h20092 | h20092
                                · linarith only [h19752, h20092, hlam]
                                · linarith only [h19755, h20092, hlam]
                            · linarith only [h19753, h20089, hlam]
                          · linarith only [h19751, h20088, hlam]
                        · linarith only [h2, h20087, hlam]
                      · have p19901_0 := h19901c.1
                        have p19901_1 := h19901c.2.1
                        have p19901_2 := h19901c.2.2.1
                        have p19901_3 := h19901c.2.2.2
                        rcases p19901_3 (m.d 0 1) (by simp) with h20098 | h20098
                        · rcases p19901_3 (m.d 1 2) (by simp) with h20099 | h20099
                          · rcases p19901_3 (m.d 1 3) (by simp) with h20100 | h20100
                            · rcases p19901_3 (m.d 1 4) (by simp) with h20101 | h20101
                              · linarith only [h19751, h20101, hlam]
                              · rcases p19901_3 (m.d 1 5) (by simp) with h20103 | h20103
                                · linarith only [h19752, h20103, hlam]
                                · rcases h1emax with h20105 | h20105 | h20105 | h20105 | h20105
                                  · linarith only [h1, h19749, h19751, h19755, h19895, h20105, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19901_1]
                                  · linarith only [h19751, h19755, h19895, h20105, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19901_1]
                                  · linarith only [h19749, h19751, h19755, h19895, h20105, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19901_1]
                                  · rcases h2bigk with h20109c | h20109c | h20109c | h20109c | h20109c | h20109c | h20109c | h20109c | h20109c | h20109c | h20109c | h20109c | h20109c | h20109c | h20109c | h20109c | h20109c | h20109c | h20109c | h20109c | h20109c | h20109c | h20109c | h20109c | h20109c
                                    · have p20109_0 := h20109c.1
                                      have p20109_1 := h20109c.2.1
                                      have p20109_2 := h20109c.2.2.1
                                      have p20109_3 := h20109c.2.2.2
                                      linarith only [hlam, p20109_0]
                                    · have p20109_0 := h20109c.1
                                      have p20109_1 := h20109c.2.1
                                      have p20109_2 := h20109c.2.2.1
                                      have p20109_3 := h20109c.2.2.2
                                      linarith only [h19751, h19755, h19895, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p19901_1, p20109_1]
                                    · have p20109_0 := h20109c.1
                                      have p20109_1 := h20109c.2.1
                                      have p20109_2 := h20109c.2.2.1
                                      have p20109_3 := h20109c.2.2.2
                                      linarith only [h4, hlam, p20109_0]
                                    · have p20109_0 := h20109c.1
                                      have p20109_1 := h20109c.2.1
                                      have p20109_2 := h20109c.2.2.1
                                      have p20109_3 := h20109c.2.2.2
                                      rcases p20109_3 (m.d 0 2) (by simp) with h20113 | h20113
                                      · rcases p20109_3 (m.d 1 2) (by simp) with h20114 | h20114
                                        · linarith only [h0, h20114, hlam]
                                        · linarith only [h19751, h20114, hlam]
                                      · linarith only [h20113, hlam, p20109_0]
                                    · have p20109_0 := h20109c.1
                                      have p20109_1 := h20109c.2.1
                                      have p20109_2 := h20109c.2.2.1
                                      have p20109_3 := h20109c.2.2.2
                                      rcases p20109_3 (m.d 0 2) (by simp) with h20118 | h20118
                                      · rcases p20109_3 (m.d 1 2) (by simp) with h20119 | h20119
                                        · linarith only [h0, h20119, hlam]
                                        · linarith only [h19752, h20119, hlam]
                                      · linarith only [h20118, hlam, p20109_0]
                                    · have p20109_0 := h20109c.1
                                      have p20109_1 := h20109c.2.1
                                      have p20109_2 := h20109c.2.2.1
                                      have p20109_3 := h20109c.2.2.2
                                      linarith only [h0, hlam, p20109_1]
                                    · have p20109_0 := h20109c.1
                                      have p20109_1 := h20109c.2.1
                                      have p20109_2 := h20109c.2.2.1
                                      have p20109_3 := h20109c.2.2.2
                                      linarith only [hlam, p20109_0]
                                    · have p20109_0 := h20109c.1
                                      have p20109_1 := h20109c.2.1
                                      have p20109_2 := h20109c.2.2.1
                                      have p20109_3 := h20109c.2.2.2
                                      linarith only [h19749, hlam, p20109_0]
                                    · have p20109_0 := h20109c.1
                                      have p20109_1 := h20109c.2.1
                                      have p20109_2 := h20109c.2.2.1
                                      have p20109_3 := h20109c.2.2.2
                                      rcases p20109_3 (m.d 0 2) (by simp) with h20126 | h20126
                                      · rcases p20109_3 (m.d 1 2) (by simp) with h20127 | h20127
                                        · rcases p20109_3 (m.d 2 3) (by simp) with h20128 | h20128
                                          · rcases p20109_3 (m.d 2 4) (by simp) with h20129 | h20129
                                            · linarith only [h20129, hlam, p20109_0]
                                            · rcases p20109_3 (m.d 2 5) (by simp) with h20131 | h20131
                                              · linarith only [h19752, h20131, hlam]
                                              · linarith only [h19897, h20131, hlam]
                                          · linarith only [h19895, h20128, hlam]
                                        · linarith only [h20127, hlam, p20109_0]
                                      · linarith only [h19744, h20126, hlam]
                                    · have p20109_0 := h20109c.1
                                      have p20109_1 := h20109c.2.1
                                      have p20109_2 := h20109c.2.2.1
                                      have p20109_3 := h20109c.2.2.2
                                      rcases p20109_3 (m.d 0 2) (by simp) with h20137 | h20137
                                      · rcases p20109_3 (m.d 1 2) (by simp) with h20138 | h20138
                                        · rcases p20109_3 (m.d 2 3) (by simp) with h20139 | h20139
                                          · rcases p20109_3 (m.d 2 4) (by simp) with h20140 | h20140
                                            · linarith only [h19751, h20140, hlam]
                                            · rcases p20109_3 (m.d 2 5) (by simp) with h20142 | h20142
                                              · linarith only [h20142, hlam, p20109_0]
                                              · rcases h4bigk with h20144c | h20144c | h20144c | h20144c | h20144c | h20144c | h20144c | h20144c | h20144c | h20144c | h20144c | h20144c | h20144c | h20144c | h20144c | h20144c | h20144c | h20144c | h20144c | h20144c | h20144c | h20144c | h20144c | h20144c | h20144c
                                                · have p20144_0 := h20144c.1
                                                  have p20144_1 := h20144c.2.1
                                                  have p20144_2 := h20144c.2.2.1
                                                  have p20144_3 := h20144c.2.2.2
                                                  linarith only [hlam, p20144_0]
                                                · have p20144_0 := h20144c.1
                                                  have p20144_1 := h20144c.2.1
                                                  have p20144_2 := h20144c.2.2.1
                                                  have p20144_3 := h20144c.2.2.2
                                                  rcases p20144_3 (m.d 0 4) (by simp) with h20146 | h20146
                                                  · rcases p20144_3 (m.d 1 4) (by simp) with h20147 | h20147
                                                    · linarith only [h2, h20147, hlam]
                                                    · rcases p20144_3 (m.d 2 4) (by simp) with h20149 | h20149
                                                      · linarith only [h19744, h20149, hlam]
                                                      · rcases p20144_3 (m.d 3 4) (by simp) with h20151 | h20151
                                                        · linarith only [h19746, h20151, hlam]
                                                        · rcases p20144_3 (m.d 4 5) (by simp) with h20153 | h20153
                                                          · linarith only [h19748, h20153, hlam]
                                                          · linarith only [h19755, h20153, hlam]
                                                  · linarith only [h2, h20146, hlam]
                                                · have p20144_0 := h20144c.1
                                                  have p20144_1 := h20144c.2.1
                                                  have p20144_2 := h20144c.2.2.1
                                                  have p20144_3 := h20144c.2.2.2
                                                  rcases p20144_3 (m.d 0 4) (by simp) with h20157 | h20157
                                                  · rcases p20144_3 (m.d 1 4) (by simp) with h20158 | h20158
                                                    · linarith only [h2, h20158, hlam]
                                                    · linarith only [h19751, h20158, hlam]
                                                  · linarith only [h19744, h20157, hlam]
                                                · have p20144_0 := h20144c.1
                                                  have p20144_1 := h20144c.2.1
                                                  have p20144_2 := h20144c.2.2.1
                                                  have p20144_3 := h20144c.2.2.2
                                                  rcases p20144_3 (m.d 0 4) (by simp) with h20162 | h20162
                                                  · rcases p20144_3 (m.d 1 4) (by simp) with h20163 | h20163
                                                    · linarith only [h2, h20163, hlam]
                                                    · linarith only [h19753, h20163, hlam]
                                                  · linarith only [h19746, h20162, hlam]
                                                · have p20144_0 := h20144c.1
                                                  have p20144_1 := h20144c.2.1
                                                  have p20144_2 := h20144c.2.2.1
                                                  have p20144_3 := h20144c.2.2.2
                                                  linarith only [h19744, h19751, h19755, h19895, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20144_1]
                                                · have p20144_0 := h20144c.1
                                                  have p20144_1 := h20144c.2.1
                                                  have p20144_2 := h20144c.2.2.1
                                                  have p20144_3 := h20144c.2.2.2
                                                  linarith only [h2, hlam, p20144_0]
                                                · have p20144_0 := h20144c.1
                                                  have p20144_1 := h20144c.2.1
                                                  have p20144_2 := h20144c.2.2.1
                                                  have p20144_3 := h20144c.2.2.2
                                                  linarith only [hlam, p20144_0]
                                                · have p20144_0 := h20144c.1
                                                  have p20144_1 := h20144c.2.1
                                                  have p20144_2 := h20144c.2.2.1
                                                  have p20144_3 := h20144c.2.2.2
                                                  linarith only [h1, h19749, h19755, h19895, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p19901_1, p20144_1]
                                                · have p20144_0 := h20144c.1
                                                  have p20144_1 := h20144c.2.1
                                                  have p20144_2 := h20144c.2.2.1
                                                  have p20144_3 := h20144c.2.2.2
                                                  linarith only [h0, h19755, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p19901_1, p20144_1]
                                                · have p20144_0 := h20144c.1
                                                  have p20144_1 := h20144c.2.1
                                                  have p20144_2 := h20144c.2.2.1
                                                  have p20144_3 := h20144c.2.2.2
                                                  linarith only [h19755, hlam, p20144_0]
                                                · have p20144_0 := h20144c.1
                                                  have p20144_1 := h20144c.2.1
                                                  have p20144_2 := h20144c.2.2.1
                                                  have p20144_3 := h20144c.2.2.2
                                                  linarith only [h19744, hlam, p20144_0]
                                                · have p20144_0 := h20144c.1
                                                  have p20144_1 := h20144c.2.1
                                                  have p20144_2 := h20144c.2.2.1
                                                  have p20144_3 := h20144c.2.2.2
                                                  linarith only [h19751, hlam, p20144_0]
                                                · have p20144_0 := h20144c.1
                                                  have p20144_1 := h20144c.2.1
                                                  have p20144_2 := h20144c.2.2.1
                                                  have p20144_3 := h20144c.2.2.2
                                                  linarith only [hlam, p20144_0]
                                                · have p20144_0 := h20144c.1
                                                  have p20144_1 := h20144c.2.1
                                                  have p20144_2 := h20144c.2.2.1
                                                  have p20144_3 := h20144c.2.2.2
                                                  linarith only [h19744, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20144_1]
                                                · have p20144_0 := h20144c.1
                                                  have p20144_1 := h20144c.2.1
                                                  have p20144_2 := h20144c.2.2.1
                                                  have p20144_3 := h20144c.2.2.2
                                                  linarith only [h19897, hlam, p20144_0]
                                                · have p20144_0 := h20144c.1
                                                  have p20144_1 := h20144c.2.1
                                                  have p20144_2 := h20144c.2.2.1
                                                  have p20144_3 := h20144c.2.2.2
                                                  linarith only [h19746, hlam, p20144_0]
                                                · have p20144_0 := h20144c.1
                                                  have p20144_1 := h20144c.2.1
                                                  have p20144_2 := h20144c.2.2.1
                                                  have p20144_3 := h20144c.2.2.2
                                                  linarith only [h19753, hlam, p20144_0]
                                                · have p20144_0 := h20144c.1
                                                  have p20144_1 := h20144c.2.1
                                                  have p20144_2 := h20144c.2.2.1
                                                  have p20144_3 := h20144c.2.2.2
                                                  linarith only [h19895, hlam, p20144_0]
                                                · have p20144_0 := h20144c.1
                                                  have p20144_1 := h20144c.2.1
                                                  have p20144_2 := h20144c.2.2.1
                                                  have p20144_3 := h20144c.2.2.2
                                                  linarith only [hlam, p20144_0]
                                                · have p20144_0 := h20144c.1
                                                  have p20144_1 := h20144c.2.1
                                                  have p20144_2 := h20144c.2.2.1
                                                  have p20144_3 := h20144c.2.2.2
                                                  linarith only [h19899, hlam, p20144_0]
                                                · have p20144_0 := h20144c.1
                                                  have p20144_1 := h20144c.2.1
                                                  have p20144_2 := h20144c.2.2.1
                                                  have p20144_3 := h20144c.2.2.2
                                                  linarith only [h19748, hlam, p20144_0]
                                                · have p20144_0 := h20144c.1
                                                  have p20144_1 := h20144c.2.1
                                                  have p20144_2 := h20144c.2.2.1
                                                  have p20144_3 := h20144c.2.2.2
                                                  linarith only [h19744, h19748, h4, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20144_1]
                                                · have p20144_0 := h20144c.1
                                                  have p20144_1 := h20144c.2.1
                                                  have p20144_2 := h20144c.2.2.1
                                                  have p20144_3 := h20144c.2.2.2
                                                  linarith only [h19744, h19748, h19895, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20144_1]
                                                · have p20144_0 := h20144c.1
                                                  have p20144_1 := h20144c.2.1
                                                  have p20144_2 := h20144c.2.2.1
                                                  have p20144_3 := h20144c.2.2.2
                                                  linarith only [h19744, h19748, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20144_1]
                                                · have p20144_0 := h20144c.1
                                                  have p20144_1 := h20144c.2.1
                                                  have p20144_2 := h20144c.2.2.1
                                                  have p20144_3 := h20144c.2.2.2
                                                  linarith only [hlam, p20144_0]
                                          · linarith only [h19896, h20139, hlam]
                                        · linarith only [h20138, hlam, p20109_0]
                                      · linarith only [h19745, h20137, hlam]
                                    · have p20109_0 := h20109c.1
                                      have p20109_1 := h20109c.2.1
                                      have p20109_2 := h20109c.2.2.1
                                      have p20109_3 := h20109c.2.2.2
                                      linarith only [h0, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p19901_1, p20109_1]
                                    · have p20109_0 := h20109c.1
                                      have p20109_1 := h20109c.2.1
                                      have p20109_2 := h20109c.2.2.1
                                      have p20109_3 := h20109c.2.2.2
                                      linarith only [h19752, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p19901_1, p20109_1]
                                    · have p20109_0 := h20109c.1
                                      have p20109_1 := h20109c.2.1
                                      have p20109_2 := h20109c.2.2.1
                                      have p20109_3 := h20109c.2.2.2
                                      linarith only [hlam, p20109_0]
                                    · have p20109_0 := h20109c.1
                                      have p20109_1 := h20109c.2.1
                                      have p20109_2 := h20109c.2.2.1
                                      have p20109_3 := h20109c.2.2.2
                                      linarith only [h0, h19751, h19755, h4, hlam, p19901_1, p20109_2]
                                    · have p20109_0 := h20109c.1
                                      have p20109_1 := h20109c.2.1
                                      have p20109_2 := h20109c.2.2.1
                                      have p20109_3 := h20109c.2.2.2
                                      linarith only [h0, h19752, h4, hlam, p19901_1, p20109_2]
                                    · have p20109_0 := h20109c.1
                                      have p20109_1 := h20109c.2.1
                                      have p20109_2 := h20109c.2.2.1
                                      have p20109_3 := h20109c.2.2.2
                                      linarith only [h19744, hlam, p20109_0]
                                    · have p20109_0 := h20109c.1
                                      have p20109_1 := h20109c.2.1
                                      have p20109_2 := h20109c.2.2.1
                                      have p20109_3 := h20109c.2.2.2
                                      linarith only [h19751, hlam, p20109_0]
                                    · have p20109_0 := h20109c.1
                                      have p20109_1 := h20109c.2.1
                                      have p20109_2 := h20109c.2.2.1
                                      have p20109_3 := h20109c.2.2.2
                                      linarith only [h19895, hlam, p20109_0]
                                    · have p20109_0 := h20109c.1
                                      have p20109_1 := h20109c.2.1
                                      have p20109_2 := h20109c.2.2.1
                                      have p20109_3 := h20109c.2.2.2
                                      linarith only [hlam, p20109_0]
                                    · have p20109_0 := h20109c.1
                                      have p20109_1 := h20109c.2.1
                                      have p20109_2 := h20109c.2.2.1
                                      have p20109_3 := h20109c.2.2.2
                                      linarith only [h19897, hlam, p20109_0]
                                    · have p20109_0 := h20109c.1
                                      have p20109_1 := h20109c.2.1
                                      have p20109_2 := h20109c.2.2.1
                                      have p20109_3 := h20109c.2.2.2
                                      linarith only [h19745, hlam, p20109_0]
                                    · have p20109_0 := h20109c.1
                                      have p20109_1 := h20109c.2.1
                                      have p20109_2 := h20109c.2.2.1
                                      have p20109_3 := h20109c.2.2.2
                                      linarith only [h19752, hlam, p20109_0]
                                    · have p20109_0 := h20109c.1
                                      have p20109_1 := h20109c.2.1
                                      have p20109_2 := h20109c.2.2.1
                                      have p20109_3 := h20109c.2.2.2
                                      linarith only [h19896, hlam, p20109_0]
                                    · have p20109_0 := h20109c.1
                                      have p20109_1 := h20109c.2.1
                                      have p20109_2 := h20109c.2.2.1
                                      have p20109_3 := h20109c.2.2.2
                                      linarith only [h0, h19752, h19895, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p19901_1, p20109_1]
                                    · have p20109_0 := h20109c.1
                                      have p20109_1 := h20109c.2.1
                                      have p20109_2 := h20109c.2.2.1
                                      have p20109_3 := h20109c.2.2.2
                                      linarith only [hlam, p20109_0]
                                  · rcases h2bigk with h20206c | h20206c | h20206c | h20206c | h20206c | h20206c | h20206c | h20206c | h20206c | h20206c | h20206c | h20206c | h20206c | h20206c | h20206c | h20206c | h20206c | h20206c | h20206c | h20206c | h20206c | h20206c | h20206c | h20206c | h20206c
                                    · have p20206_0 := h20206c.1
                                      have p20206_1 := h20206c.2.1
                                      have p20206_2 := h20206c.2.2.1
                                      have p20206_3 := h20206c.2.2.2
                                      linarith only [hlam, p20206_0]
                                    · have p20206_0 := h20206c.1
                                      have p20206_1 := h20206c.2.1
                                      have p20206_2 := h20206c.2.2.1
                                      have p20206_3 := h20206c.2.2.2
                                      linarith only [h4, hc12, hc23, hlam, hphi, p20206_1]
                                    · have p20206_0 := h20206c.1
                                      have p20206_1 := h20206c.2.1
                                      have p20206_2 := h20206c.2.2.1
                                      have p20206_3 := h20206c.2.2.2
                                      linarith only [h4, hlam, p20206_0]
                                    · have p20206_0 := h20206c.1
                                      have p20206_1 := h20206c.2.1
                                      have p20206_2 := h20206c.2.2.1
                                      have p20206_3 := h20206c.2.2.2
                                      rcases p20206_3 (m.d 0 2) (by simp) with h20210 | h20210
                                      · rcases p20206_3 (m.d 1 2) (by simp) with h20211 | h20211
                                        · linarith only [h0, h20211, hlam]
                                        · linarith only [h19751, h20211, hlam]
                                      · linarith only [h20210, hlam, p20206_0]
                                    · have p20206_0 := h20206c.1
                                      have p20206_1 := h20206c.2.1
                                      have p20206_2 := h20206c.2.2.1
                                      have p20206_3 := h20206c.2.2.2
                                      rcases p20206_3 (m.d 0 2) (by simp) with h20215 | h20215
                                      · rcases p20206_3 (m.d 1 2) (by simp) with h20216 | h20216
                                        · linarith only [h0, h20216, hlam]
                                        · linarith only [h19752, h20216, hlam]
                                      · linarith only [h20215, hlam, p20206_0]
                                    · have p20206_0 := h20206c.1
                                      have p20206_1 := h20206c.2.1
                                      have p20206_2 := h20206c.2.2.1
                                      have p20206_3 := h20206c.2.2.2
                                      linarith only [h0, hlam, p20206_1]
                                    · have p20206_0 := h20206c.1
                                      have p20206_1 := h20206c.2.1
                                      have p20206_2 := h20206c.2.2.1
                                      have p20206_3 := h20206c.2.2.2
                                      linarith only [hlam, p20206_0]
                                    · have p20206_0 := h20206c.1
                                      have p20206_1 := h20206c.2.1
                                      have p20206_2 := h20206c.2.2.1
                                      have p20206_3 := h20206c.2.2.2
                                      linarith only [h19749, hlam, p20206_0]
                                    · have p20206_0 := h20206c.1
                                      have p20206_1 := h20206c.2.1
                                      have p20206_2 := h20206c.2.2.1
                                      have p20206_3 := h20206c.2.2.2
                                      rcases p20206_3 (m.d 0 2) (by simp) with h20223 | h20223
                                      · rcases p20206_3 (m.d 1 2) (by simp) with h20224 | h20224
                                        · rcases p20206_3 (m.d 2 3) (by simp) with h20225 | h20225
                                          · rcases p20206_3 (m.d 2 4) (by simp) with h20226 | h20226
                                            · linarith only [h20226, hlam, p20206_0]
                                            · rcases p20206_3 (m.d 2 5) (by simp) with h20228 | h20228
                                              · linarith only [h19752, h20228, hlam]
                                              · linarith only [h19897, h20228, hlam]
                                          · linarith only [h19895, h20225, hlam]
                                        · linarith only [h20224, hlam, p20206_0]
                                      · linarith only [h19744, h20223, hlam]
                                    · have p20206_0 := h20206c.1
                                      have p20206_1 := h20206c.2.1
                                      have p20206_2 := h20206c.2.2.1
                                      have p20206_3 := h20206c.2.2.2
                                      rcases p20206_3 (m.d 0 2) (by simp) with h20234 | h20234
                                      · rcases p20206_3 (m.d 1 2) (by simp) with h20235 | h20235
                                        · rcases p20206_3 (m.d 2 3) (by simp) with h20236 | h20236
                                          · rcases p20206_3 (m.d 2 4) (by simp) with h20237 | h20237
                                            · linarith only [h19751, h20237, hlam]
                                            · rcases p20206_3 (m.d 2 5) (by simp) with h20239 | h20239
                                              · linarith only [h20239, hlam, p20206_0]
                                              · rcases h4bigk with h20241c | h20241c | h20241c | h20241c | h20241c | h20241c | h20241c | h20241c | h20241c | h20241c | h20241c | h20241c | h20241c | h20241c | h20241c | h20241c | h20241c | h20241c | h20241c | h20241c | h20241c | h20241c | h20241c | h20241c | h20241c
                                                · have p20241_0 := h20241c.1
                                                  have p20241_1 := h20241c.2.1
                                                  have p20241_2 := h20241c.2.2.1
                                                  have p20241_3 := h20241c.2.2.2
                                                  linarith only [hlam, p20241_0]
                                                · have p20241_0 := h20241c.1
                                                  have p20241_1 := h20241c.2.1
                                                  have p20241_2 := h20241c.2.2.1
                                                  have p20241_3 := h20241c.2.2.2
                                                  rcases p20241_3 (m.d 0 4) (by simp) with h20243 | h20243
                                                  · rcases p20241_3 (m.d 1 4) (by simp) with h20244 | h20244
                                                    · linarith only [h2, h20244, hlam]
                                                    · rcases p20241_3 (m.d 2 4) (by simp) with h20246 | h20246
                                                      · linarith only [h19744, h20246, hlam]
                                                      · rcases p20241_3 (m.d 3 4) (by simp) with h20248 | h20248
                                                        · linarith only [h19746, h20248, hlam]
                                                        · rcases p20241_3 (m.d 4 5) (by simp) with h20250 | h20250
                                                          · linarith only [h19748, h20250, hlam]
                                                          · linarith only [h19755, h20250, hlam]
                                                  · linarith only [h2, h20243, hlam]
                                                · have p20241_0 := h20241c.1
                                                  have p20241_1 := h20241c.2.1
                                                  have p20241_2 := h20241c.2.2.1
                                                  have p20241_3 := h20241c.2.2.2
                                                  rcases p20241_3 (m.d 0 4) (by simp) with h20254 | h20254
                                                  · rcases p20241_3 (m.d 1 4) (by simp) with h20255 | h20255
                                                    · linarith only [h2, h20255, hlam]
                                                    · linarith only [h19751, h20255, hlam]
                                                  · linarith only [h19744, h20254, hlam]
                                                · have p20241_0 := h20241c.1
                                                  have p20241_1 := h20241c.2.1
                                                  have p20241_2 := h20241c.2.2.1
                                                  have p20241_3 := h20241c.2.2.2
                                                  rcases p20241_3 (m.d 0 4) (by simp) with h20259 | h20259
                                                  · rcases p20241_3 (m.d 1 4) (by simp) with h20260 | h20260
                                                    · linarith only [h2, h20260, hlam]
                                                    · linarith only [h19753, h20260, hlam]
                                                  · linarith only [h19746, h20259, hlam]
                                                · have p20241_0 := h20241c.1
                                                  have p20241_1 := h20241c.2.1
                                                  have p20241_2 := h20241c.2.2.1
                                                  have p20241_3 := h20241c.2.2.2
                                                  linarith only [h19744, h19751, h19755, h19895, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20241_1]
                                                · have p20241_0 := h20241c.1
                                                  have p20241_1 := h20241c.2.1
                                                  have p20241_2 := h20241c.2.2.1
                                                  have p20241_3 := h20241c.2.2.2
                                                  linarith only [h2, hlam, p20241_0]
                                                · have p20241_0 := h20241c.1
                                                  have p20241_1 := h20241c.2.1
                                                  have p20241_2 := h20241c.2.2.1
                                                  have p20241_3 := h20241c.2.2.2
                                                  linarith only [hlam, p20241_0]
                                                · have p20241_0 := h20241c.1
                                                  have p20241_1 := h20241c.2.1
                                                  have p20241_2 := h20241c.2.2.1
                                                  have p20241_3 := h20241c.2.2.2
                                                  linarith only [h19755, h19895, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19901_1, p20241_1]
                                                · have p20241_0 := h20241c.1
                                                  have p20241_1 := h20241c.2.1
                                                  have p20241_2 := h20241c.2.2.1
                                                  have p20241_3 := h20241c.2.2.2
                                                  linarith only [h0, h19755, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p19901_1, p20241_1]
                                                · have p20241_0 := h20241c.1
                                                  have p20241_1 := h20241c.2.1
                                                  have p20241_2 := h20241c.2.2.1
                                                  have p20241_3 := h20241c.2.2.2
                                                  linarith only [h19755, hlam, p20241_0]
                                                · have p20241_0 := h20241c.1
                                                  have p20241_1 := h20241c.2.1
                                                  have p20241_2 := h20241c.2.2.1
                                                  have p20241_3 := h20241c.2.2.2
                                                  linarith only [h19744, hlam, p20241_0]
                                                · have p20241_0 := h20241c.1
                                                  have p20241_1 := h20241c.2.1
                                                  have p20241_2 := h20241c.2.2.1
                                                  have p20241_3 := h20241c.2.2.2
                                                  linarith only [h19751, hlam, p20241_0]
                                                · have p20241_0 := h20241c.1
                                                  have p20241_1 := h20241c.2.1
                                                  have p20241_2 := h20241c.2.2.1
                                                  have p20241_3 := h20241c.2.2.2
                                                  linarith only [hlam, p20241_0]
                                                · have p20241_0 := h20241c.1
                                                  have p20241_1 := h20241c.2.1
                                                  have p20241_2 := h20241c.2.2.1
                                                  have p20241_3 := h20241c.2.2.2
                                                  linarith only [h19744, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20241_1]
                                                · have p20241_0 := h20241c.1
                                                  have p20241_1 := h20241c.2.1
                                                  have p20241_2 := h20241c.2.2.1
                                                  have p20241_3 := h20241c.2.2.2
                                                  linarith only [h19897, hlam, p20241_0]
                                                · have p20241_0 := h20241c.1
                                                  have p20241_1 := h20241c.2.1
                                                  have p20241_2 := h20241c.2.2.1
                                                  have p20241_3 := h20241c.2.2.2
                                                  linarith only [h19746, hlam, p20241_0]
                                                · have p20241_0 := h20241c.1
                                                  have p20241_1 := h20241c.2.1
                                                  have p20241_2 := h20241c.2.2.1
                                                  have p20241_3 := h20241c.2.2.2
                                                  linarith only [h19753, hlam, p20241_0]
                                                · have p20241_0 := h20241c.1
                                                  have p20241_1 := h20241c.2.1
                                                  have p20241_2 := h20241c.2.2.1
                                                  have p20241_3 := h20241c.2.2.2
                                                  linarith only [h19895, hlam, p20241_0]
                                                · have p20241_0 := h20241c.1
                                                  have p20241_1 := h20241c.2.1
                                                  have p20241_2 := h20241c.2.2.1
                                                  have p20241_3 := h20241c.2.2.2
                                                  linarith only [hlam, p20241_0]
                                                · have p20241_0 := h20241c.1
                                                  have p20241_1 := h20241c.2.1
                                                  have p20241_2 := h20241c.2.2.1
                                                  have p20241_3 := h20241c.2.2.2
                                                  linarith only [h19899, hlam, p20241_0]
                                                · have p20241_0 := h20241c.1
                                                  have p20241_1 := h20241c.2.1
                                                  have p20241_2 := h20241c.2.2.1
                                                  have p20241_3 := h20241c.2.2.2
                                                  linarith only [h19748, hlam, p20241_0]
                                                · have p20241_0 := h20241c.1
                                                  have p20241_1 := h20241c.2.1
                                                  have p20241_2 := h20241c.2.2.1
                                                  have p20241_3 := h20241c.2.2.2
                                                  linarith only [h19744, h19748, h4, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20241_1]
                                                · have p20241_0 := h20241c.1
                                                  have p20241_1 := h20241c.2.1
                                                  have p20241_2 := h20241c.2.2.1
                                                  have p20241_3 := h20241c.2.2.2
                                                  linarith only [h19744, h19748, h19895, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20241_1]
                                                · have p20241_0 := h20241c.1
                                                  have p20241_1 := h20241c.2.1
                                                  have p20241_2 := h20241c.2.2.1
                                                  have p20241_3 := h20241c.2.2.2
                                                  linarith only [h19744, h19748, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20241_1]
                                                · have p20241_0 := h20241c.1
                                                  have p20241_1 := h20241c.2.1
                                                  have p20241_2 := h20241c.2.2.1
                                                  have p20241_3 := h20241c.2.2.2
                                                  linarith only [hlam, p20241_0]
                                          · linarith only [h19896, h20236, hlam]
                                        · linarith only [h20235, hlam, p20206_0]
                                      · linarith only [h19745, h20234, hlam]
                                    · have p20206_0 := h20206c.1
                                      have p20206_1 := h20206c.2.1
                                      have p20206_2 := h20206c.2.2.1
                                      have p20206_3 := h20206c.2.2.2
                                      linarith only [h0, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p19901_1, p20206_1]
                                    · have p20206_0 := h20206c.1
                                      have p20206_1 := h20206c.2.1
                                      have p20206_2 := h20206c.2.2.1
                                      have p20206_3 := h20206c.2.2.2
                                      linarith only [hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p19901_1, p20206_1]
                                    · have p20206_0 := h20206c.1
                                      have p20206_1 := h20206c.2.1
                                      have p20206_2 := h20206c.2.2.1
                                      have p20206_3 := h20206c.2.2.2
                                      linarith only [hlam, p20206_0]
                                    · have p20206_0 := h20206c.1
                                      have p20206_1 := h20206c.2.1
                                      have p20206_2 := h20206c.2.2.1
                                      have p20206_3 := h20206c.2.2.2
                                      linarith only [h19744, h19748, h19751, h19755, h4, hlam, p20206_2]
                                    · have p20206_0 := h20206c.1
                                      have p20206_1 := h20206c.2.1
                                      have p20206_2 := h20206c.2.2.1
                                      have p20206_3 := h20206c.2.2.2
                                      linarith only [h0, h19752, h4, hlam, p19901_1, p20206_2]
                                    · have p20206_0 := h20206c.1
                                      have p20206_1 := h20206c.2.1
                                      have p20206_2 := h20206c.2.2.1
                                      have p20206_3 := h20206c.2.2.2
                                      linarith only [h19744, hlam, p20206_0]
                                    · have p20206_0 := h20206c.1
                                      have p20206_1 := h20206c.2.1
                                      have p20206_2 := h20206c.2.2.1
                                      have p20206_3 := h20206c.2.2.2
                                      linarith only [h19751, hlam, p20206_0]
                                    · have p20206_0 := h20206c.1
                                      have p20206_1 := h20206c.2.1
                                      have p20206_2 := h20206c.2.2.1
                                      have p20206_3 := h20206c.2.2.2
                                      linarith only [h19895, hlam, p20206_0]
                                    · have p20206_0 := h20206c.1
                                      have p20206_1 := h20206c.2.1
                                      have p20206_2 := h20206c.2.2.1
                                      have p20206_3 := h20206c.2.2.2
                                      linarith only [hlam, p20206_0]
                                    · have p20206_0 := h20206c.1
                                      have p20206_1 := h20206c.2.1
                                      have p20206_2 := h20206c.2.2.1
                                      have p20206_3 := h20206c.2.2.2
                                      linarith only [h19897, hlam, p20206_0]
                                    · have p20206_0 := h20206c.1
                                      have p20206_1 := h20206c.2.1
                                      have p20206_2 := h20206c.2.2.1
                                      have p20206_3 := h20206c.2.2.2
                                      linarith only [h19745, hlam, p20206_0]
                                    · have p20206_0 := h20206c.1
                                      have p20206_1 := h20206c.2.1
                                      have p20206_2 := h20206c.2.2.1
                                      have p20206_3 := h20206c.2.2.2
                                      linarith only [h19752, hlam, p20206_0]
                                    · have p20206_0 := h20206c.1
                                      have p20206_1 := h20206c.2.1
                                      have p20206_2 := h20206c.2.2.1
                                      have p20206_3 := h20206c.2.2.2
                                      linarith only [h19896, hlam, p20206_0]
                                    · have p20206_0 := h20206c.1
                                      have p20206_1 := h20206c.2.1
                                      have p20206_2 := h20206c.2.2.1
                                      have p20206_3 := h20206c.2.2.2
                                      linarith only [h0, h19752, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p19901_1, p20206_1]
                                    · have p20206_0 := h20206c.1
                                      have p20206_1 := h20206c.2.1
                                      have p20206_2 := h20206c.2.2.1
                                      have p20206_3 := h20206c.2.2.2
                                      linarith only [hlam, p20206_0]
                            · linarith only [h19754, h20100, hlam]
                          · linarith only [h19752, h20099, hlam]
                        · linarith only [h20098, h3, hlam]
                      · have p19901_0 := h19901c.1
                        have p19901_1 := h19901c.2.1
                        have p19901_2 := h19901c.2.2.1
                        have p19901_3 := h19901c.2.2.2
                        linarith only [h1, hlam, p19901_0]
                      · have p19901_0 := h19901c.1
                        have p19901_1 := h19901c.2.1
                        have p19901_2 := h19901c.2.2.1
                        have p19901_3 := h19901c.2.2.2
                        linarith only [h1, h19751, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p19901_1]
                      · have p19901_0 := h19901c.1
                        have p19901_1 := h19901c.2.1
                        have p19901_2 := h19901c.2.2.1
                        have p19901_3 := h19901c.2.2.2
                        linarith only [hlam, p19901_0]
                      · have p19901_0 := h19901c.1
                        have p19901_1 := h19901c.2.1
                        have p19901_2 := h19901c.2.2.1
                        have p19901_3 := h19901c.2.2.2
                        rcases p19901_3 (m.d 0 1) (by simp) with h20309 | h20309
                        · rcases p19901_3 (m.d 1 2) (by simp) with h20310 | h20310
                          · linarith only [h19749, h20310, hlam]
                          · linarith only [h19751, h20310, hlam]
                        · linarith only [h2, h20309, hlam]
                      · have p19901_0 := h19901c.1
                        have p19901_1 := h19901c.2.1
                        have p19901_2 := h19901c.2.2.1
                        have p19901_3 := h19901c.2.2.2
                        rcases p19901_3 (m.d 0 1) (by simp) with h20314 | h20314
                        · rcases p19901_3 (m.d 1 2) (by simp) with h20315 | h20315
                          · linarith only [h19749, h20315, hlam]
                          · linarith only [h19752, h20315, hlam]
                        · linarith only [h20314, h3, hlam]
                      · have p19901_0 := h19901c.1
                        have p19901_1 := h19901c.2.1
                        have p19901_2 := h19901c.2.2.1
                        have p19901_3 := h19901c.2.2.2
                        linarith only [h2, hlam, p19901_0]
                      · have p19901_0 := h19901c.1
                        have p19901_1 := h19901c.2.1
                        have p19901_2 := h19901c.2.2.1
                        have p19901_3 := h19901c.2.2.2
                        linarith only [h19751, hlam, p19901_0]
                      · have p19901_0 := h19901c.1
                        have p19901_1 := h19901c.2.1
                        have p19901_2 := h19901c.2.2.1
                        have p19901_3 := h19901c.2.2.2
                        linarith only [h19753, hlam, p19901_1]
                      · have p19901_0 := h19901c.1
                        have p19901_1 := h19901c.2.1
                        have p19901_2 := h19901c.2.2.1
                        have p19901_3 := h19901c.2.2.2
                        linarith only [hlam, p19901_0]
                      · have p19901_0 := h19901c.1
                        have p19901_1 := h19901c.2.1
                        have p19901_2 := h19901c.2.2.1
                        have p19901_3 := h19901c.2.2.2
                        linarith only [h19755, hlam, p19901_1]
                      · have p19901_0 := h19901c.1
                        have p19901_1 := h19901c.2.1
                        have p19901_2 := h19901c.2.2.1
                        have p19901_3 := h19901c.2.2.2
                        linarith only [h3, hlam, p19901_0]
                      · have p19901_0 := h19901c.1
                        have p19901_1 := h19901c.2.1
                        have p19901_2 := h19901c.2.2.1
                        have p19901_3 := h19901c.2.2.2
                        linarith only [h19752, hlam, p19901_0]
                      · have p19901_0 := h19901c.1
                        have p19901_1 := h19901c.2.1
                        have p19901_2 := h19901c.2.2.1
                        have p19901_3 := h19901c.2.2.2
                        linarith only [h19754, hlam, p19901_0]
                      · have p19901_0 := h19901c.1
                        have p19901_1 := h19901c.2.1
                        have p19901_2 := h19901c.2.2.1
                        have p19901_3 := h19901c.2.2.2
                        linarith only [h19744, h19748, h19751, h19755, h19895, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p19901_1]
                      · have p19901_0 := h19901c.1
                        have p19901_1 := h19901c.2.1
                        have p19901_2 := h19901c.2.2.1
                        have p19901_3 := h19901c.2.2.2
                        linarith only [hlam, p19901_0]
                · linarith only [h19744, h19748, h19754, h19755, h19896, h4, hlam]
              · linarith only [h19746, h19895, h4, hlam]
          · linarith only [h19749, h19752, h19754, hlam]
        · linarith only [h19749, h19751, h19753, hlam]
      · linarith only [h19745, h19752, h4, hc12, hc23, hlam, hphi]
    · linarith only [h19744, h19751, h4, hc12, hc23, hlam, hphi]

set_option maxHeartbeats 24306000 in
set_option maxHeartbeats 24306000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x0_x0_x0_x0_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h19744 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h19745 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19746 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19747 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19748 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h20335 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  linarith only [h0, h19744, h20335, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]

set_option maxHeartbeats 24306000 in
set_option maxHeartbeats 24306000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h19744 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h19745 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19746 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19747 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19748 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h20335 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h20337 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20338 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20339 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20340 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20341 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  linarith only [h19748, h2, h20341, hlam]

set_option maxHeartbeats 24306000 in
set_option maxHeartbeats 24306000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x1_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h19744 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h19745 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19746 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19747 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19748 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h20335 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h20337 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20338 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20339 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20340 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20341 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h20343 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h20344 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h20345 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  linarith only [h0, h19748, h2, h20337, h20345, h4, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]

set_option maxHeartbeats 24306000 in
set_option maxHeartbeats 24306000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x1_x0_x0_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h19744 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h19745 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19746 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19747 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19748 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h20335 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h20337 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20338 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20339 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20340 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20341 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h20343 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h20344 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h20345 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h20347 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  linarith only [h19748, h2, h20337, h20343, h20347, hlam]

set_option maxHeartbeats 24306000 in
set_option maxHeartbeats 24306000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x1_x0_x0_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h19744 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h19745 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19746 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19747 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19748 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h20335 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h20337 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20338 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20339 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20340 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20341 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h20343 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h20344 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h20345 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h20347 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h20349c : ((m.d 0 1) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 0 1) ∧ (m.d 0 1) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 0 1) ≤ z)))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have p20349_0 := h20349c.1
  have p20349_1 := h20349c.2.1
  have p20349_2 := h20349c.2.2.1
  have p20349_3 := h20349c.2.2.2
  linarith only [hlam, p20349_0]

set_option maxHeartbeats 24306000 in
set_option maxHeartbeats 24306000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x1_x0_x0_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h19744 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h19745 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19746 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19747 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19748 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h20335 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h20337 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20338 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20339 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20340 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20341 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h20343 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h20344 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h20345 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h20347 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h20349c : ((m.d 0 1) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 0 1) ∧ (m.d 1 2) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 1 2) ≤ z)))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have p20349_0 := h20349c.1
  have p20349_1 := h20349c.2.1
  have p20349_2 := h20349c.2.2.1
  have p20349_3 := h20349c.2.2.2
  rcases p20349_3 (m.d 0 1) (by simp) with h20351 | h20351
  · rcases p20349_3 (m.d 1 2) (by simp) with h20352 | h20352
    · linarith only [h20352, hlam, p20349_0]
    · rcases p20349_3 (m.d 1 3) (by simp) with h20354 | h20354
      · linarith only [h1, h20354, hlam]
      · linarith only [h20335, h20354, hlam]
  · linarith only [h20351, hlam, p20349_0]

end R2N4
