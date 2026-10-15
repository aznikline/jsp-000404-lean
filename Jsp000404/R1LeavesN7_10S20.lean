import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10432000 in
set_option maxHeartbeats 10432000 in
theorem r1l7_12_24_L_I_H_I_s7_x1_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h8886 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h12751 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  rcases m.htr 0 2 5 (by decide) (by decide) with h12752 | h12752
  · rcases m.htr 0 3 4 (by decide) (by decide) with h12753 | h12753
    · rcases m.htr 0 4 5 (by decide) (by decide) with h12754 | h12754
      · rcases m.htr 1 2 3 (by decide) (by decide) with h12755 | h12755
        · rcases m.htr 1 2 4 (by decide) (by decide) with h12756 | h12756
          · rcases m.htr 1 2 5 (by decide) (by decide) with h12757 | h12757
            · rcases m.htr 1 3 4 (by decide) (by decide) with h12758 | h12758
              · rcases m.htr 1 4 5 (by decide) (by decide) with h12759 | h12759
                · rcases m.htr 2 3 4 (by decide) (by decide) with h12760 | h12760
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h12761 | h12761
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h12762 | h12762
                      · linarith only [h12751, h12755, h12762, h8886, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h12751, h12754, h12755, h12762, h8886, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h12752, h12761, h8886, hlam]
                  · linarith only [h12753, h12760, h8886, hlam]
                · linarith only [h12751, h12754, h12755, h12759, h6874, h8886, hc01, hc13, hlam, hphi]
              · linarith only [h12751, h12753, h12755, h12758, h8886, hlam]
            · linarith only [h12752, h12755, h12757, h8886, hlam]
          · linarith only [h12755, h12756, h8886, hc02, hc24, hlam, hphi]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h12771 | h12771
          · rcases m.htr 1 2 5 (by decide) (by decide) with h12772 | h12772
            · rcases m.htr 1 3 4 (by decide) (by decide) with h12773 | h12773
              · rcases m.htr 1 4 5 (by decide) (by decide) with h12774 | h12774
                · rcases m.htr 2 3 4 (by decide) (by decide) with h12775 | h12775
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h12776 | h12776
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h12777 | h12777
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h12778 | h12778
                        · rcases h2bigk with h12779c | h12779c | h12779c | h12779c | h12779c | h12779c | h12779c | h12779c | h12779c | h12779c | h12779c | h12779c | h12779c | h12779c | h12779c | h12779c | h12779c | h12779c | h12779c | h12779c | h12779c | h12779c | h12779c | h12779c | h12779c
                          · have p12779_0 := h12779c.1
                            have p12779_1 := h12779c.2.1
                            have p12779_2 := h12779c.2.2.1
                            have p12779_3 := h12779c.2.2.2
                            linarith only [hlam, p12779_0]
                          · have p12779_0 := h12779c.1
                            have p12779_1 := h12779c.2.1
                            have p12779_2 := h12779c.2.2.1
                            have p12779_3 := h12779c.2.2.2
                            linarith only [h0, hlam, p12779_0]
                          · have p12779_0 := h12779c.1
                            have p12779_1 := h12779c.2.1
                            have p12779_2 := h12779c.2.2.1
                            have p12779_3 := h12779c.2.2.2
                            linarith only [h8886, hlam, p12779_0]
                          · have p12779_0 := h12779c.1
                            have p12779_1 := h12779c.2.1
                            have p12779_2 := h12779c.2.2.1
                            have p12779_3 := h12779c.2.2.2
                            linarith only [h0, h12755, h12775, h12778, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p12779_1]
                          · have p12779_0 := h12779c.1
                            have p12779_1 := h12779c.2.1
                            have p12779_2 := h12779c.2.2.1
                            have p12779_3 := h12779c.2.2.2
                            rcases p12779_3 (m.d 0 2) (by simp) with h12784 | h12784
                            · rcases p12779_3 (m.d 1 2) (by simp) with h12785 | h12785
                              · rcases p12779_3 (m.d 2 3) (by simp) with h12786 | h12786
                                · rcases p12779_3 (m.d 2 4) (by simp) with h12787 | h12787
                                  · linarith only [h12751, h12787, hlam]
                                  · linarith only [h12777, h12787, hlam]
                                · linarith only [h12776, h12786, hlam]
                              · linarith only [h12772, h12785, hlam]
                            · linarith only [h12784, hlam, p12779_0]
                          · have p12779_0 := h12779c.1
                            have p12779_1 := h12779c.2.1
                            have p12779_2 := h12779c.2.2.1
                            have p12779_3 := h12779c.2.2.2
                            linarith only [h12755, hc02, hc23, hlam, hphi, p12779_1]
                          · have p12779_0 := h12779c.1
                            have p12779_1 := h12779c.2.1
                            have p12779_2 := h12779c.2.2.1
                            have p12779_3 := h12779c.2.2.2
                            linarith only [hlam, p12779_0]
                          · have p12779_0 := h12779c.1
                            have p12779_1 := h12779c.2.1
                            have p12779_2 := h12779c.2.2.1
                            have p12779_3 := h12779c.2.2.2
                            linarith only [h12755, hlam, p12779_0]
                          · have p12779_0 := h12779c.1
                            have p12779_1 := h12779c.2.1
                            have p12779_2 := h12779c.2.2.1
                            have p12779_3 := h12779c.2.2.2
                            linarith only [h12755, h12775, h12778, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p12779_1]
                          · have p12779_0 := h12779c.1
                            have p12779_1 := h12779c.2.1
                            have p12779_2 := h12779c.2.2.1
                            have p12779_3 := h12779c.2.2.2
                            rcases p12779_3 (m.d 0 2) (by simp) with h12797 | h12797
                            · linarith only [h0, h12797, hlam]
                            · linarith only [h12752, h12797, hlam]
                          · have p12779_0 := h12779c.1
                            have p12779_1 := h12779c.2.1
                            have p12779_2 := h12779c.2.2.1
                            have p12779_3 := h12779c.2.2.2
                            linarith only [h12751, h12775, h12778, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p12779_1]
                          · have p12779_0 := h12779c.1
                            have p12779_1 := h12779c.2.1
                            have p12779_2 := h12779c.2.2.1
                            have p12779_3 := h12779c.2.2.2
                            linarith only [h0, hc01, hc23, hlam, hphi, ht12, p12779_1]
                          · have p12779_0 := h12779c.1
                            have p12779_1 := h12779c.2.1
                            have p12779_2 := h12779c.2.2.1
                            have p12779_3 := h12779c.2.2.2
                            linarith only [hlam, p12779_0]
                          · have p12779_0 := h12779c.1
                            have p12779_1 := h12779c.2.1
                            have p12779_2 := h12779c.2.2.1
                            have p12779_3 := h12779c.2.2.2
                            rcases p12779_3 (m.d 0 2) (by simp) with h12803 | h12803
                            · linarith only [h12803, h8886, hlam]
                            · linarith only [h12751, h12803, hlam]
                          · have p12779_0 := h12779c.1
                            have p12779_1 := h12779c.2.1
                            have p12779_2 := h12779c.2.2.1
                            have p12779_3 := h12779c.2.2.2
                            rcases p12779_3 (m.d 0 2) (by simp) with h12806 | h12806
                            · linarith only [h12806, h8886, hlam]
                            · linarith only [h12752, h12806, hlam]
                          · have p12779_0 := h12779c.1
                            have p12779_1 := h12779c.2.1
                            have p12779_2 := h12779c.2.2.1
                            have p12779_3 := h12779c.2.2.2
                            linarith only [h12751, hlam, p12779_0]
                          · have p12779_0 := h12779c.1
                            have p12779_1 := h12779c.2.1
                            have p12779_2 := h12779c.2.2.1
                            have p12779_3 := h12779c.2.2.2
                            linarith only [h12771, hlam, p12779_0]
                          · have p12779_0 := h12779c.1
                            have p12779_1 := h12779c.2.1
                            have p12779_2 := h12779c.2.2.1
                            have p12779_3 := h12779c.2.2.2
                            linarith only [h12775, hlam, p12779_0]
                          · have p12779_0 := h12779c.1
                            have p12779_1 := h12779c.2.1
                            have p12779_2 := h12779c.2.2.1
                            have p12779_3 := h12779c.2.2.2
                            linarith only [hlam, p12779_0]
                          · have p12779_0 := h12779c.1
                            have p12779_1 := h12779c.2.1
                            have p12779_2 := h12779c.2.2.1
                            have p12779_3 := h12779c.2.2.2
                            linarith only [h12751, h8886, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p12779_1]
                          · have p12779_0 := h12779c.1
                            have p12779_1 := h12779c.2.1
                            have p12779_2 := h12779c.2.2.1
                            have p12779_3 := h12779c.2.2.2
                            linarith only [h12752, hlam, p12779_0]
                          · have p12779_0 := h12779c.1
                            have p12779_1 := h12779c.2.1
                            have p12779_2 := h12779c.2.2.1
                            have p12779_3 := h12779c.2.2.2
                            linarith only [h12772, hlam, p12779_0]
                          · have p12779_0 := h12779c.1
                            have p12779_1 := h12779c.2.1
                            have p12779_2 := h12779c.2.2.1
                            have p12779_3 := h12779c.2.2.2
                            linarith only [h12776, hlam, p12779_0]
                          · have p12779_0 := h12779c.1
                            have p12779_1 := h12779c.2.1
                            have p12779_2 := h12779c.2.2.1
                            have p12779_3 := h12779c.2.2.2
                            linarith only [h12777, hlam, p12779_1]
                          · have p12779_0 := h12779c.1
                            have p12779_1 := h12779c.2.1
                            have p12779_2 := h12779c.2.2.1
                            have p12779_3 := h12779c.2.2.2
                            linarith only [hlam, p12779_0]
                        · linarith only [h0, h12751, h12755, h12777, h12778, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h12820 | h12820
                        · linarith only [h12775, h12777, h12820, hlam]
                        · rcases h2bigk with h12822c | h12822c | h12822c | h12822c | h12822c | h12822c | h12822c | h12822c | h12822c | h12822c | h12822c | h12822c | h12822c | h12822c | h12822c | h12822c | h12822c | h12822c | h12822c | h12822c | h12822c | h12822c | h12822c | h12822c | h12822c
                          · have p12822_0 := h12822c.1
                            have p12822_1 := h12822c.2.1
                            have p12822_2 := h12822c.2.2.1
                            have p12822_3 := h12822c.2.2.2
                            linarith only [hlam, p12822_0]
                          · have p12822_0 := h12822c.1
                            have p12822_1 := h12822c.2.1
                            have p12822_2 := h12822c.2.2.1
                            have p12822_3 := h12822c.2.2.2
                            linarith only [h0, hlam, p12822_0]
                          · have p12822_0 := h12822c.1
                            have p12822_1 := h12822c.2.1
                            have p12822_2 := h12822c.2.2.1
                            have p12822_3 := h12822c.2.2.2
                            linarith only [h8886, hlam, p12822_0]
                          · have p12822_0 := h12822c.1
                            have p12822_1 := h12822c.2.1
                            have p12822_2 := h12822c.2.2.1
                            have p12822_3 := h12822c.2.2.2
                            rcases p12822_3 (m.d 0 2) (by simp) with h12826 | h12826
                            · rcases p12822_3 (m.d 1 2) (by simp) with h12827 | h12827
                              · rcases p12822_3 (m.d 2 3) (by simp) with h12828 | h12828
                                · rcases p12822_3 (m.d 2 4) (by simp) with h12829 | h12829
                                  · linarith only [h12829, hlam, p12822_0]
                                  · rcases p12822_3 (m.d 2 5) (by simp) with h12831 | h12831
                                    · linarith only [h12752, h12831, hlam]
                                    · linarith only [h12777, h12831, hlam]
                                · linarith only [h12775, h12828, hlam]
                              · linarith only [h12771, h12827, hlam]
                            · linarith only [h12826, hlam, p12822_0]
                          · have p12822_0 := h12822c.1
                            have p12822_1 := h12822c.2.1
                            have p12822_2 := h12822c.2.2.1
                            have p12822_3 := h12822c.2.2.2
                            rcases p12822_3 (m.d 0 2) (by simp) with h12837 | h12837
                            · rcases p12822_3 (m.d 1 2) (by simp) with h12838 | h12838
                              · rcases p12822_3 (m.d 2 3) (by simp) with h12839 | h12839
                                · rcases p12822_3 (m.d 2 4) (by simp) with h12840 | h12840
                                  · linarith only [h12751, h12840, hlam]
                                  · rcases p12822_3 (m.d 2 5) (by simp) with h12842 | h12842
                                    · linarith only [h12842, hlam, p12822_0]
                                    · rcases h4bigk with h12844c | h12844c | h12844c | h12844c | h12844c | h12844c | h12844c | h12844c | h12844c | h12844c | h12844c | h12844c | h12844c | h12844c | h12844c | h12844c | h12844c | h12844c | h12844c | h12844c | h12844c | h12844c | h12844c | h12844c | h12844c
                                      · have p12844_0 := h12844c.1
                                        have p12844_1 := h12844c.2.1
                                        have p12844_2 := h12844c.2.2.1
                                        have p12844_3 := h12844c.2.2.2
                                        linarith only [hlam, p12844_0]
                                      · have p12844_0 := h12844c.1
                                        have p12844_1 := h12844c.2.1
                                        have p12844_2 := h12844c.2.2.1
                                        have p12844_3 := h12844c.2.2.2
                                        linarith only [h6874, hlam, p12844_1]
                                      · have p12844_0 := h12844c.1
                                        have p12844_1 := h12844c.2.1
                                        have p12844_2 := h12844c.2.2.1
                                        have p12844_3 := h12844c.2.2.2
                                        linarith only [h0, h12751, h12755, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12844_1]
                                      · have p12844_0 := h12844c.1
                                        have p12844_1 := h12844c.2.1
                                        have p12844_2 := h12844c.2.2.1
                                        have p12844_3 := h12844c.2.2.2
                                        linarith only [h0, h12751, h12755, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12844_1]
                                      · have p12844_0 := h12844c.1
                                        have p12844_1 := h12844c.2.1
                                        have p12844_2 := h12844c.2.2.1
                                        have p12844_3 := h12844c.2.2.2
                                        linarith only [h0, h12751, h12755, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p12844_1]
                                      · have p12844_0 := h12844c.1
                                        have p12844_1 := h12844c.2.1
                                        have p12844_2 := h12844c.2.2.1
                                        have p12844_3 := h12844c.2.2.2
                                        linarith only [h6874, hc01, hc14, hlam, hphi, p12844_1]
                                      · have p12844_0 := h12844c.1
                                        have p12844_1 := h12844c.2.1
                                        have p12844_2 := h12844c.2.2.1
                                        have p12844_3 := h12844c.2.2.2
                                        linarith only [hlam, p12844_0]
                                      · have p12844_0 := h12844c.1
                                        have p12844_1 := h12844c.2.1
                                        have p12844_2 := h12844c.2.2.1
                                        have p12844_3 := h12844c.2.2.2
                                        linarith only [h12755, h12771, h12775, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12844_1]
                                      · have p12844_0 := h12844c.1
                                        have p12844_1 := h12844c.2.1
                                        have p12844_2 := h12844c.2.2.1
                                        have p12844_3 := h12844c.2.2.2
                                        linarith only [h12755, h12771, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12844_1]
                                      · have p12844_0 := h12844c.1
                                        have p12844_1 := h12844c.2.1
                                        have p12844_2 := h12844c.2.2.1
                                        have p12844_3 := h12844c.2.2.2
                                        linarith only [h12755, h12771, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p12844_1]
                                      · have p12844_0 := h12844c.1
                                        have p12844_1 := h12844c.2.1
                                        have p12844_2 := h12844c.2.2.1
                                        have p12844_3 := h12844c.2.2.2
                                        linarith only [h12751, hlam, p12844_0]
                                      · have p12844_0 := h12844c.1
                                        have p12844_1 := h12844c.2.1
                                        have p12844_2 := h12844c.2.2.1
                                        have p12844_3 := h12844c.2.2.2
                                        linarith only [h12771, hlam, p12844_0]
                                      · have p12844_0 := h12844c.1
                                        have p12844_1 := h12844c.2.1
                                        have p12844_2 := h12844c.2.2.1
                                        have p12844_3 := h12844c.2.2.2
                                        linarith only [hlam, p12844_0]
                                      · have p12844_0 := h12844c.1
                                        have p12844_1 := h12844c.2.1
                                        have p12844_2 := h12844c.2.2.1
                                        have p12844_3 := h12844c.2.2.2
                                        linarith only [h0, h12751, h12755, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12844_1]
                                      · have p12844_0 := h12844c.1
                                        have p12844_1 := h12844c.2.1
                                        have p12844_2 := h12844c.2.2.1
                                        have p12844_3 := h12844c.2.2.2
                                        linarith only [h12777, hlam, p12844_0]
                                      · have p12844_0 := h12844c.1
                                        have p12844_1 := h12844c.2.1
                                        have p12844_2 := h12844c.2.2.1
                                        have p12844_3 := h12844c.2.2.2
                                        linarith only [h12753, hlam, p12844_0]
                                      · have p12844_0 := h12844c.1
                                        have p12844_1 := h12844c.2.1
                                        have p12844_2 := h12844c.2.2.1
                                        have p12844_3 := h12844c.2.2.2
                                        linarith only [h12773, hlam, p12844_0]
                                      · have p12844_0 := h12844c.1
                                        have p12844_1 := h12844c.2.1
                                        have p12844_2 := h12844c.2.2.1
                                        have p12844_3 := h12844c.2.2.2
                                        linarith only [h12775, hlam, p12844_0]
                                      · have p12844_0 := h12844c.1
                                        have p12844_1 := h12844c.2.1
                                        have p12844_2 := h12844c.2.2.1
                                        have p12844_3 := h12844c.2.2.2
                                        linarith only [hlam, p12844_0]
                                      · have p12844_0 := h12844c.1
                                        have p12844_1 := h12844c.2.1
                                        have p12844_2 := h12844c.2.2.1
                                        have p12844_3 := h12844c.2.2.2
                                        linarith only [h12820, hlam, p12844_0]
                                      · have p12844_0 := h12844c.1
                                        have p12844_1 := h12844c.2.1
                                        have p12844_2 := h12844c.2.2.1
                                        have p12844_3 := h12844c.2.2.2
                                        linarith only [h12754, hlam, p12844_0]
                                      · have p12844_0 := h12844c.1
                                        have p12844_1 := h12844c.2.1
                                        have p12844_2 := h12844c.2.2.1
                                        have p12844_3 := h12844c.2.2.2
                                        linarith only [h12774, hlam, p12844_0]
                                      · have p12844_0 := h12844c.1
                                        have p12844_1 := h12844c.2.1
                                        have p12844_2 := h12844c.2.2.1
                                        have p12844_3 := h12844c.2.2.2
                                        linarith only [h12754, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b, p12844_1]
                                      · have p12844_0 := h12844c.1
                                        have p12844_1 := h12844c.2.1
                                        have p12844_2 := h12844c.2.2.1
                                        have p12844_3 := h12844c.2.2.2
                                        linarith only [h12754, h12755, h12771, h6874, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12844_1]
                                      · have p12844_0 := h12844c.1
                                        have p12844_1 := h12844c.2.1
                                        have p12844_2 := h12844c.2.2.1
                                        have p12844_3 := h12844c.2.2.2
                                        linarith only [hlam, p12844_0]
                                · linarith only [h12776, h12839, hlam]
                              · linarith only [h12772, h12838, hlam]
                            · linarith only [h12837, hlam, p12822_0]
                          · have p12822_0 := h12822c.1
                            have p12822_1 := h12822c.2.1
                            have p12822_2 := h12822c.2.2.1
                            have p12822_3 := h12822c.2.2.2
                            linarith only [h12755, hc02, hc23, hlam, hphi, p12822_1]
                          · have p12822_0 := h12822c.1
                            have p12822_1 := h12822c.2.1
                            have p12822_2 := h12822c.2.2.1
                            have p12822_3 := h12822c.2.2.2
                            linarith only [hlam, p12822_0]
                          · have p12822_0 := h12822c.1
                            have p12822_1 := h12822c.2.1
                            have p12822_2 := h12822c.2.2.1
                            have p12822_3 := h12822c.2.2.2
                            linarith only [h12755, hlam, p12822_0]
                          · have p12822_0 := h12822c.1
                            have p12822_1 := h12822c.2.1
                            have p12822_2 := h12822c.2.2.1
                            have p12822_3 := h12822c.2.2.2
                            rcases p12822_3 (m.d 0 2) (by simp) with h12876 | h12876
                            · linarith only [h0, h12876, hlam]
                            · linarith only [h12751, h12876, hlam]
                          · have p12822_0 := h12822c.1
                            have p12822_1 := h12822c.2.1
                            have p12822_2 := h12822c.2.2.1
                            have p12822_3 := h12822c.2.2.2
                            rcases p12822_3 (m.d 0 2) (by simp) with h12879 | h12879
                            · linarith only [h0, h12879, hlam]
                            · linarith only [h12752, h12879, hlam]
                          · have p12822_0 := h12822c.1
                            have p12822_1 := h12822c.2.1
                            have p12822_2 := h12822c.2.2.1
                            have p12822_3 := h12822c.2.2.2
                            linarith only [h12751, h12754, h12775, h12777, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12822_1]
                          · have p12822_0 := h12822c.1
                            have p12822_1 := h12822c.2.1
                            have p12822_2 := h12822c.2.2.1
                            have p12822_3 := h12822c.2.2.2
                            linarith only [h0, hc01, hc23, hlam, hphi, ht12, p12822_1]
                          · have p12822_0 := h12822c.1
                            have p12822_1 := h12822c.2.1
                            have p12822_2 := h12822c.2.2.1
                            have p12822_3 := h12822c.2.2.2
                            linarith only [hlam, p12822_0]
                          · have p12822_0 := h12822c.1
                            have p12822_1 := h12822c.2.1
                            have p12822_2 := h12822c.2.2.1
                            have p12822_3 := h12822c.2.2.2
                            linarith only [h12751, h12754, h12777, h8886, hlam, p12822_2]
                          · have p12822_0 := h12822c.1
                            have p12822_1 := h12822c.2.1
                            have p12822_2 := h12822c.2.2.1
                            have p12822_3 := h12822c.2.2.2
                            rcases p12822_3 (m.d 0 2) (by simp) with h12886 | h12886
                            · linarith only [h12886, h8886, hlam]
                            · linarith only [h12752, h12886, hlam]
                          · have p12822_0 := h12822c.1
                            have p12822_1 := h12822c.2.1
                            have p12822_2 := h12822c.2.2.1
                            have p12822_3 := h12822c.2.2.2
                            linarith only [h12751, hlam, p12822_0]
                          · have p12822_0 := h12822c.1
                            have p12822_1 := h12822c.2.1
                            have p12822_2 := h12822c.2.2.1
                            have p12822_3 := h12822c.2.2.2
                            linarith only [h12771, hlam, p12822_0]
                          · have p12822_0 := h12822c.1
                            have p12822_1 := h12822c.2.1
                            have p12822_2 := h12822c.2.2.1
                            have p12822_3 := h12822c.2.2.2
                            linarith only [h12775, hlam, p12822_0]
                          · have p12822_0 := h12822c.1
                            have p12822_1 := h12822c.2.1
                            have p12822_2 := h12822c.2.2.1
                            have p12822_3 := h12822c.2.2.2
                            linarith only [hlam, p12822_0]
                          · have p12822_0 := h12822c.1
                            have p12822_1 := h12822c.2.1
                            have p12822_2 := h12822c.2.2.1
                            have p12822_3 := h12822c.2.2.2
                            linarith only [h12777, hlam, p12822_0]
                          · have p12822_0 := h12822c.1
                            have p12822_1 := h12822c.2.1
                            have p12822_2 := h12822c.2.2.1
                            have p12822_3 := h12822c.2.2.2
                            linarith only [h12752, hlam, p12822_0]
                          · have p12822_0 := h12822c.1
                            have p12822_1 := h12822c.2.1
                            have p12822_2 := h12822c.2.2.1
                            have p12822_3 := h12822c.2.2.2
                            linarith only [h12772, hlam, p12822_0]
                          · have p12822_0 := h12822c.1
                            have p12822_1 := h12822c.2.1
                            have p12822_2 := h12822c.2.2.1
                            have p12822_3 := h12822c.2.2.2
                            linarith only [h12776, hlam, p12822_0]
                          · have p12822_0 := h12822c.1
                            have p12822_1 := h12822c.2.1
                            have p12822_2 := h12822c.2.2.1
                            have p12822_3 := h12822c.2.2.2
                            linarith only [h0, h12752, h12755, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12822_1]
                          · have p12822_0 := h12822c.1
                            have p12822_1 := h12822c.2.1
                            have p12822_2 := h12822c.2.2.1
                            have p12822_3 := h12822c.2.2.2
                            linarith only [hlam, p12822_0]
                    · linarith only [h0, h12755, h12776, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h12755, h12771, h12775, h6874, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h0, h12751, h12754, h12774, h6874, hc01, hc12, hlam, hphi]
              · linarith only [h0, h12753, h12755, h12773, h8886, hc01, hc23, hlam, hphi, ht12]
            · linarith only [h0, h12752, h12772, hlam]
          · linarith only [h0, h12751, h12771, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h12905 | h12905
        · rcases m.htr 1 2 4 (by decide) (by decide) with h12906 | h12906
          · rcases m.htr 1 2 5 (by decide) (by decide) with h12907 | h12907
            · rcases m.htr 1 3 4 (by decide) (by decide) with h12908 | h12908
              · rcases m.htr 1 4 5 (by decide) (by decide) with h12909 | h12909
                · rcases m.htr 2 3 4 (by decide) (by decide) with h12910 | h12910
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h12911 | h12911
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h12912 | h12912
                      · linarith only [h12751, h12754, h12905, h12912, h8886, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h12914 | h12914
                        · linarith only [h12752, h12754, h12905, h12910, h12912, h12914, h6874, h8886, hc01, hc12, hlam, hphi]
                        · rcases h2bigk with h12916c | h12916c | h12916c | h12916c | h12916c | h12916c | h12916c | h12916c | h12916c | h12916c | h12916c | h12916c | h12916c | h12916c | h12916c | h12916c | h12916c | h12916c | h12916c | h12916c | h12916c | h12916c | h12916c | h12916c | h12916c
                          · have p12916_0 := h12916c.1
                            have p12916_1 := h12916c.2.1
                            have p12916_2 := h12916c.2.2.1
                            have p12916_3 := h12916c.2.2.2
                            linarith only [hlam, p12916_0]
                          · have p12916_0 := h12916c.1
                            have p12916_1 := h12916c.2.1
                            have p12916_2 := h12916c.2.2.1
                            have p12916_3 := h12916c.2.2.2
                            linarith only [h0, hlam, p12916_0]
                          · have p12916_0 := h12916c.1
                            have p12916_1 := h12916c.2.1
                            have p12916_2 := h12916c.2.2.1
                            have p12916_3 := h12916c.2.2.2
                            linarith only [h8886, hlam, p12916_0]
                          · have p12916_0 := h12916c.1
                            have p12916_1 := h12916c.2.1
                            have p12916_2 := h12916c.2.2.1
                            have p12916_3 := h12916c.2.2.2
                            linarith only [h12905, h8886, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p12916_1]
                          · have p12916_0 := h12916c.1
                            have p12916_1 := h12916c.2.1
                            have p12916_2 := h12916c.2.2.1
                            have p12916_3 := h12916c.2.2.2
                            linarith only [h12905, h8886, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p12916_1]
                          · have p12916_0 := h12916c.1
                            have p12916_1 := h12916c.2.1
                            have p12916_2 := h12916c.2.2.1
                            have p12916_3 := h12916c.2.2.2
                            rcases p12916_3 (m.d 0 2) (by simp) with h12922 | h12922
                            · linarith only [h0, h12922, hlam]
                            · rcases p12916_3 (m.d 1 2) (by simp) with h12924 | h12924
                              · rcases p12916_3 (m.d 2 3) (by simp) with h12925 | h12925
                                · linarith only [h12905, h12925, hlam]
                                · linarith only [h12925, h8886, hlam]
                              · linarith only [h0, h12924, hlam]
                          · have p12916_0 := h12916c.1
                            have p12916_1 := h12916c.2.1
                            have p12916_2 := h12916c.2.2.1
                            have p12916_3 := h12916c.2.2.2
                            linarith only [hlam, p12916_0]
                          · have p12916_0 := h12916c.1
                            have p12916_1 := h12916c.2.1
                            have p12916_2 := h12916c.2.2.1
                            have p12916_3 := h12916c.2.2.2
                            linarith only [h0, h8886, hc01, hc12, hlam, hphi, p12916_1]
                          · have p12916_0 := h12916c.1
                            have p12916_1 := h12916c.2.1
                            have p12916_2 := h12916c.2.2.1
                            have p12916_3 := h12916c.2.2.2
                            linarith only [h12752, h12905, h12912, h8886, hlam, p12916_2]
                          · have p12916_0 := h12916c.1
                            have p12916_1 := h12916c.2.1
                            have p12916_2 := h12916c.2.2.1
                            have p12916_3 := h12916c.2.2.2
                            linarith only [h12752, h12905, h8886, hlam, p12916_2]
                          · have p12916_0 := h12916c.1
                            have p12916_1 := h12916c.2.1
                            have p12916_2 := h12916c.2.2.1
                            have p12916_3 := h12916c.2.2.2
                            linarith only [h12752, h12905, h12910, h12912, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12916_1]
                          · have p12916_0 := h12916c.1
                            have p12916_1 := h12916c.2.1
                            have p12916_2 := h12916c.2.2.1
                            have p12916_3 := h12916c.2.2.2
                            linarith only [h12905, hlam, p12916_0]
                          · have p12916_0 := h12916c.1
                            have p12916_1 := h12916c.2.1
                            have p12916_2 := h12916c.2.2.1
                            have p12916_3 := h12916c.2.2.2
                            linarith only [hlam, p12916_0]
                          · have p12916_0 := h12916c.1
                            have p12916_1 := h12916c.2.1
                            have p12916_2 := h12916c.2.2.1
                            have p12916_3 := h12916c.2.2.2
                            rcases p12916_3 (m.d 0 2) (by simp) with h12936 | h12936
                            · linarith only [h12936, h8886, hlam]
                            · linarith only [h12751, h12936, hlam]
                          · have p12916_0 := h12916c.1
                            have p12916_1 := h12916c.2.1
                            have p12916_2 := h12916c.2.2.1
                            have p12916_3 := h12916c.2.2.2
                            rcases p12916_3 (m.d 0 2) (by simp) with h12939 | h12939
                            · linarith only [h12939, h8886, hlam]
                            · linarith only [h12752, h12939, hlam]
                          · have p12916_0 := h12916c.1
                            have p12916_1 := h12916c.2.1
                            have p12916_2 := h12916c.2.2.1
                            have p12916_3 := h12916c.2.2.2
                            linarith only [h12751, hlam, p12916_0]
                          · have p12916_0 := h12916c.1
                            have p12916_1 := h12916c.2.1
                            have p12916_2 := h12916c.2.2.1
                            have p12916_3 := h12916c.2.2.2
                            linarith only [h12906, hlam, p12916_0]
                          · have p12916_0 := h12916c.1
                            have p12916_1 := h12916c.2.1
                            have p12916_2 := h12916c.2.2.1
                            have p12916_3 := h12916c.2.2.2
                            linarith only [h12910, hlam, p12916_0]
                          · have p12916_0 := h12916c.1
                            have p12916_1 := h12916c.2.1
                            have p12916_2 := h12916c.2.2.1
                            have p12916_3 := h12916c.2.2.2
                            linarith only [hlam, p12916_0]
                          · have p12916_0 := h12916c.1
                            have p12916_1 := h12916c.2.1
                            have p12916_2 := h12916c.2.2.1
                            have p12916_3 := h12916c.2.2.2
                            linarith only [h12912, hlam, p12916_0]
                          · have p12916_0 := h12916c.1
                            have p12916_1 := h12916c.2.1
                            have p12916_2 := h12916c.2.2.1
                            have p12916_3 := h12916c.2.2.2
                            linarith only [h12752, hlam, p12916_0]
                          · have p12916_0 := h12916c.1
                            have p12916_1 := h12916c.2.1
                            have p12916_2 := h12916c.2.2.1
                            have p12916_3 := h12916c.2.2.2
                            linarith only [h12907, hlam, p12916_0]
                          · have p12916_0 := h12916c.1
                            have p12916_1 := h12916c.2.1
                            have p12916_2 := h12916c.2.2.1
                            have p12916_3 := h12916c.2.2.2
                            linarith only [h12911, hlam, p12916_0]
                          · have p12916_0 := h12916c.1
                            have p12916_1 := h12916c.2.1
                            have p12916_2 := h12916c.2.2.1
                            have p12916_3 := h12916c.2.2.2
                            linarith only [h12752, h12905, h12910, h8886, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12916_1]
                          · have p12916_0 := h12916c.1
                            have p12916_1 := h12916c.2.1
                            have p12916_2 := h12916c.2.2.1
                            have p12916_3 := h12916c.2.2.2
                            linarith only [hlam, p12916_0]
                    · linarith only [h12752, h12911, h8886, hlam]
                  · linarith only [h12753, h12910, h8886, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h12954 | h12954
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h12955 | h12955
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h12956 | h12956
                      · linarith only [h12751, h12905, h12909, h12956, h8886, hc13, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h12958 | h12958
                        · linarith only [h12752, h12905, h12909, h12954, h12956, h12958, h6874, h8886, hc01, hc12, hlam, hphi]
                        · rcases h2bigk with h12960c | h12960c | h12960c | h12960c | h12960c | h12960c | h12960c | h12960c | h12960c | h12960c | h12960c | h12960c | h12960c | h12960c | h12960c | h12960c | h12960c | h12960c | h12960c | h12960c | h12960c | h12960c | h12960c | h12960c | h12960c
                          · have p12960_0 := h12960c.1
                            have p12960_1 := h12960c.2.1
                            have p12960_2 := h12960c.2.2.1
                            have p12960_3 := h12960c.2.2.2
                            linarith only [hlam, p12960_0]
                          · have p12960_0 := h12960c.1
                            have p12960_1 := h12960c.2.1
                            have p12960_2 := h12960c.2.2.1
                            have p12960_3 := h12960c.2.2.2
                            linarith only [h0, hlam, p12960_0]
                          · have p12960_0 := h12960c.1
                            have p12960_1 := h12960c.2.1
                            have p12960_2 := h12960c.2.2.1
                            have p12960_3 := h12960c.2.2.2
                            linarith only [h8886, hlam, p12960_0]
                          · have p12960_0 := h12960c.1
                            have p12960_1 := h12960c.2.1
                            have p12960_2 := h12960c.2.2.1
                            have p12960_3 := h12960c.2.2.2
                            linarith only [h12905, h8886, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p12960_1]
                          · have p12960_0 := h12960c.1
                            have p12960_1 := h12960c.2.1
                            have p12960_2 := h12960c.2.2.1
                            have p12960_3 := h12960c.2.2.2
                            linarith only [h12905, h8886, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p12960_1]
                          · have p12960_0 := h12960c.1
                            have p12960_1 := h12960c.2.1
                            have p12960_2 := h12960c.2.2.1
                            have p12960_3 := h12960c.2.2.2
                            rcases p12960_3 (m.d 0 2) (by simp) with h12966 | h12966
                            · linarith only [h0, h12966, hlam]
                            · rcases p12960_3 (m.d 1 2) (by simp) with h12968 | h12968
                              · rcases p12960_3 (m.d 2 3) (by simp) with h12969 | h12969
                                · linarith only [h12905, h12969, hlam]
                                · linarith only [h12969, h8886, hlam]
                              · linarith only [h0, h12968, hlam]
                          · have p12960_0 := h12960c.1
                            have p12960_1 := h12960c.2.1
                            have p12960_2 := h12960c.2.2.1
                            have p12960_3 := h12960c.2.2.2
                            linarith only [hlam, p12960_0]
                          · have p12960_0 := h12960c.1
                            have p12960_1 := h12960c.2.1
                            have p12960_2 := h12960c.2.2.1
                            have p12960_3 := h12960c.2.2.2
                            linarith only [h0, h8886, hc01, hc12, hlam, hphi, p12960_1]
                          · have p12960_0 := h12960c.1
                            have p12960_1 := h12960c.2.1
                            have p12960_2 := h12960c.2.2.1
                            have p12960_3 := h12960c.2.2.2
                            linarith only [h12752, h12905, h12956, h8886, hlam, p12960_2]
                          · have p12960_0 := h12960c.1
                            have p12960_1 := h12960c.2.1
                            have p12960_2 := h12960c.2.2.1
                            have p12960_3 := h12960c.2.2.2
                            linarith only [h12752, h12905, h8886, hlam, p12960_2]
                          · have p12960_0 := h12960c.1
                            have p12960_1 := h12960c.2.1
                            have p12960_2 := h12960c.2.2.1
                            have p12960_3 := h12960c.2.2.2
                            linarith only [h12752, h12905, h12954, h12956, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12960_1]
                          · have p12960_0 := h12960c.1
                            have p12960_1 := h12960c.2.1
                            have p12960_2 := h12960c.2.2.1
                            have p12960_3 := h12960c.2.2.2
                            linarith only [h12905, hlam, p12960_0]
                          · have p12960_0 := h12960c.1
                            have p12960_1 := h12960c.2.1
                            have p12960_2 := h12960c.2.2.1
                            have p12960_3 := h12960c.2.2.2
                            linarith only [hlam, p12960_0]
                          · have p12960_0 := h12960c.1
                            have p12960_1 := h12960c.2.1
                            have p12960_2 := h12960c.2.2.1
                            have p12960_3 := h12960c.2.2.2
                            rcases p12960_3 (m.d 0 2) (by simp) with h12980 | h12980
                            · linarith only [h12980, h8886, hlam]
                            · linarith only [h12751, h12980, hlam]
                          · have p12960_0 := h12960c.1
                            have p12960_1 := h12960c.2.1
                            have p12960_2 := h12960c.2.2.1
                            have p12960_3 := h12960c.2.2.2
                            rcases p12960_3 (m.d 0 2) (by simp) with h12983 | h12983
                            · linarith only [h12983, h8886, hlam]
                            · linarith only [h12752, h12983, hlam]
                          · have p12960_0 := h12960c.1
                            have p12960_1 := h12960c.2.1
                            have p12960_2 := h12960c.2.2.1
                            have p12960_3 := h12960c.2.2.2
                            linarith only [h12751, hlam, p12960_0]
                          · have p12960_0 := h12960c.1
                            have p12960_1 := h12960c.2.1
                            have p12960_2 := h12960c.2.2.1
                            have p12960_3 := h12960c.2.2.2
                            linarith only [h12906, hlam, p12960_0]
                          · have p12960_0 := h12960c.1
                            have p12960_1 := h12960c.2.1
                            have p12960_2 := h12960c.2.2.1
                            have p12960_3 := h12960c.2.2.2
                            linarith only [h12954, hlam, p12960_0]
                          · have p12960_0 := h12960c.1
                            have p12960_1 := h12960c.2.1
                            have p12960_2 := h12960c.2.2.1
                            have p12960_3 := h12960c.2.2.2
                            linarith only [hlam, p12960_0]
                          · have p12960_0 := h12960c.1
                            have p12960_1 := h12960c.2.1
                            have p12960_2 := h12960c.2.2.1
                            have p12960_3 := h12960c.2.2.2
                            linarith only [h12956, hlam, p12960_0]
                          · have p12960_0 := h12960c.1
                            have p12960_1 := h12960c.2.1
                            have p12960_2 := h12960c.2.2.1
                            have p12960_3 := h12960c.2.2.2
                            linarith only [h12752, hlam, p12960_0]
                          · have p12960_0 := h12960c.1
                            have p12960_1 := h12960c.2.1
                            have p12960_2 := h12960c.2.2.1
                            have p12960_3 := h12960c.2.2.2
                            linarith only [h12907, hlam, p12960_0]
                          · have p12960_0 := h12960c.1
                            have p12960_1 := h12960c.2.1
                            have p12960_2 := h12960c.2.2.1
                            have p12960_3 := h12960c.2.2.2
                            linarith only [h12955, hlam, p12960_0]
                          · have p12960_0 := h12960c.1
                            have p12960_1 := h12960c.2.1
                            have p12960_2 := h12960c.2.2.1
                            have p12960_3 := h12960c.2.2.2
                            linarith only [h12752, h12905, h12954, h8886, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12960_1]
                          · have p12960_0 := h12960c.1
                            have p12960_1 := h12960c.2.1
                            have p12960_2 := h12960c.2.2.1
                            have p12960_3 := h12960c.2.2.2
                            linarith only [hlam, p12960_0]
                    · linarith only [h12752, h12955, h8886, hlam]
                  · linarith only [h12753, h12954, h8886, hlam]
              · linarith only [h12751, h12753, h12905, h12908, h8886, hlam]
            · linarith only [h12752, h12907, h8886, hc12, hc23, hlam, hphi]
          · linarith only [h12751, h12905, h12906, h8886, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h13001 | h13001
          · rcases m.htr 1 2 5 (by decide) (by decide) with h13002 | h13002
            · rcases m.htr 1 3 4 (by decide) (by decide) with h13003 | h13003
              · rcases m.htr 1 4 5 (by decide) (by decide) with h13004 | h13004
                · linarith only [h12754, h12905, h13001, h13004, h6874, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h13006 | h13006
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h13007 | h13007
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h13008 | h13008
                      · linarith only [h0, h12751, h12905, h13004, h13008, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h13010 | h13010
                        · linarith only [h13004, h13010, h6874, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases h2bigk with h13012c | h13012c | h13012c | h13012c | h13012c | h13012c | h13012c | h13012c | h13012c | h13012c | h13012c | h13012c | h13012c | h13012c | h13012c | h13012c | h13012c | h13012c | h13012c | h13012c | h13012c | h13012c | h13012c | h13012c | h13012c
                          · have p13012_0 := h13012c.1
                            have p13012_1 := h13012c.2.1
                            have p13012_2 := h13012c.2.2.1
                            have p13012_3 := h13012c.2.2.2
                            linarith only [hlam, p13012_0]
                          · have p13012_0 := h13012c.1
                            have p13012_1 := h13012c.2.1
                            have p13012_2 := h13012c.2.2.1
                            have p13012_3 := h13012c.2.2.2
                            linarith only [h0, hlam, p13012_0]
                          · have p13012_0 := h13012c.1
                            have p13012_1 := h13012c.2.1
                            have p13012_2 := h13012c.2.2.1
                            have p13012_3 := h13012c.2.2.2
                            linarith only [h8886, hlam, p13012_0]
                          · have p13012_0 := h13012c.1
                            have p13012_1 := h13012c.2.1
                            have p13012_2 := h13012c.2.2.1
                            have p13012_3 := h13012c.2.2.2
                            rcases p13012_3 (m.d 0 2) (by simp) with h13016 | h13016
                            · rcases p13012_3 (m.d 1 2) (by simp) with h13017 | h13017
                              · rcases p13012_3 (m.d 2 3) (by simp) with h13018 | h13018
                                · rcases p13012_3 (m.d 2 4) (by simp) with h13019 | h13019
                                  · linarith only [h13019, hlam, p13012_0]
                                  · rcases p13012_3 (m.d 2 5) (by simp) with h13021 | h13021
                                    · linarith only [h12752, h13021, hlam]
                                    · linarith only [h13008, h13021, hlam]
                                · linarith only [h13006, h13018, hlam]
                              · linarith only [h13001, h13017, hlam]
                            · linarith only [h13016, hlam, p13012_0]
                          · have p13012_0 := h13012c.1
                            have p13012_1 := h13012c.2.1
                            have p13012_2 := h13012c.2.2.1
                            have p13012_3 := h13012c.2.2.2
                            rcases p13012_3 (m.d 0 2) (by simp) with h13027 | h13027
                            · rcases p13012_3 (m.d 1 2) (by simp) with h13028 | h13028
                              · rcases p13012_3 (m.d 2 3) (by simp) with h13029 | h13029
                                · rcases p13012_3 (m.d 2 4) (by simp) with h13030 | h13030
                                  · linarith only [h12751, h13030, hlam]
                                  · rcases p13012_3 (m.d 2 5) (by simp) with h13032 | h13032
                                    · linarith only [h13032, hlam, p13012_0]
                                    · rcases h4bigk with h13034c | h13034c | h13034c | h13034c | h13034c | h13034c | h13034c | h13034c | h13034c | h13034c | h13034c | h13034c | h13034c | h13034c | h13034c | h13034c | h13034c | h13034c | h13034c | h13034c | h13034c | h13034c | h13034c | h13034c | h13034c
                                      · have p13034_0 := h13034c.1
                                        have p13034_1 := h13034c.2.1
                                        have p13034_2 := h13034c.2.2.1
                                        have p13034_3 := h13034c.2.2.2
                                        linarith only [hlam, p13034_0]
                                      · have p13034_0 := h13034c.1
                                        have p13034_1 := h13034c.2.1
                                        have p13034_2 := h13034c.2.2.1
                                        have p13034_3 := h13034c.2.2.2
                                        linarith only [h6874, hlam, p13034_1]
                                      · have p13034_0 := h13034c.1
                                        have p13034_1 := h13034c.2.1
                                        have p13034_2 := h13034c.2.2.1
                                        have p13034_3 := h13034c.2.2.2
                                        linarith only [h13004, h6874, hc24, hc45, hlam, hphi, p13034_1]
                                      · have p13034_0 := h13034c.1
                                        have p13034_1 := h13034c.2.1
                                        have p13034_2 := h13034c.2.2.1
                                        have p13034_3 := h13034c.2.2.2
                                        linarith only [h13004, h6874, hc34, hc45, hlam, hphi, p13034_1]
                                      · have p13034_0 := h13034c.1
                                        have p13034_1 := h13034c.2.1
                                        have p13034_2 := h13034c.2.2.1
                                        have p13034_3 := h13034c.2.2.2
                                        linarith only [h12754, hlam, p13034_0]
                                      · have p13034_0 := h13034c.1
                                        have p13034_1 := h13034c.2.1
                                        have p13034_2 := h13034c.2.2.1
                                        have p13034_3 := h13034c.2.2.2
                                        linarith only [h13004, hc04, hc45, hlam, hphi, p13034_1]
                                      · have p13034_0 := h13034c.1
                                        have p13034_1 := h13034c.2.1
                                        have p13034_2 := h13034c.2.2.1
                                        have p13034_3 := h13034c.2.2.2
                                        linarith only [hlam, p13034_0]
                                      · have p13034_0 := h13034c.1
                                        have p13034_1 := h13034c.2.1
                                        have p13034_2 := h13034c.2.2.1
                                        have p13034_3 := h13034c.2.2.2
                                        linarith only [h13004, h13006, hc34, hc45, hlam, hphi, p13034_1]
                                      · have p13034_0 := h13034c.1
                                        have p13034_1 := h13034c.2.1
                                        have p13034_2 := h13034c.2.2.1
                                        have p13034_3 := h13034c.2.2.2
                                        linarith only [h13004, hc34, hc45, hlam, hphi, p13034_1]
                                      · have p13034_0 := h13034c.1
                                        have p13034_1 := h13034c.2.1
                                        have p13034_2 := h13034c.2.2.1
                                        have p13034_3 := h13034c.2.2.2
                                        linarith only [h13004, hlam, p13034_0]
                                      · have p13034_0 := h13034c.1
                                        have p13034_1 := h13034c.2.1
                                        have p13034_2 := h13034c.2.2.1
                                        have p13034_3 := h13034c.2.2.2
                                        linarith only [h12751, hlam, p13034_0]
                                      · have p13034_0 := h13034c.1
                                        have p13034_1 := h13034c.2.1
                                        have p13034_2 := h13034c.2.2.1
                                        have p13034_3 := h13034c.2.2.2
                                        linarith only [h13001, hlam, p13034_0]
                                      · have p13034_0 := h13034c.1
                                        have p13034_1 := h13034c.2.1
                                        have p13034_2 := h13034c.2.2.1
                                        have p13034_3 := h13034c.2.2.2
                                        linarith only [hlam, p13034_0]
                                      · have p13034_0 := h13034c.1
                                        have p13034_1 := h13034c.2.1
                                        have p13034_2 := h13034c.2.2.1
                                        have p13034_3 := h13034c.2.2.2
                                        linarith only [h0, h12751, h12905, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13034_1]
                                      · have p13034_0 := h13034c.1
                                        have p13034_1 := h13034c.2.1
                                        have p13034_2 := h13034c.2.2.1
                                        have p13034_3 := h13034c.2.2.2
                                        linarith only [h13008, hlam, p13034_0]
                                      · have p13034_0 := h13034c.1
                                        have p13034_1 := h13034c.2.1
                                        have p13034_2 := h13034c.2.2.1
                                        have p13034_3 := h13034c.2.2.2
                                        linarith only [h12753, hlam, p13034_0]
                                      · have p13034_0 := h13034c.1
                                        have p13034_1 := h13034c.2.1
                                        have p13034_2 := h13034c.2.2.1
                                        have p13034_3 := h13034c.2.2.2
                                        linarith only [h13003, hlam, p13034_0]
                                      · have p13034_0 := h13034c.1
                                        have p13034_1 := h13034c.2.1
                                        have p13034_2 := h13034c.2.2.1
                                        have p13034_3 := h13034c.2.2.2
                                        linarith only [h13006, hlam, p13034_0]
                                      · have p13034_0 := h13034c.1
                                        have p13034_1 := h13034c.2.1
                                        have p13034_2 := h13034c.2.2.1
                                        have p13034_3 := h13034c.2.2.2
                                        linarith only [hlam, p13034_0]
                                      · have p13034_0 := h13034c.1
                                        have p13034_1 := h13034c.2.1
                                        have p13034_2 := h13034c.2.2.1
                                        have p13034_3 := h13034c.2.2.2
                                        linarith only [h13010, hlam, p13034_0]
                                      · have p13034_0 := h13034c.1
                                        have p13034_1 := h13034c.2.1
                                        have p13034_2 := h13034c.2.2.1
                                        have p13034_3 := h13034c.2.2.2
                                        linarith only [h6874, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p13034_1]
                                      · have p13034_0 := h13034c.1
                                        have p13034_1 := h13034c.2.1
                                        have p13034_2 := h13034c.2.2.1
                                        have p13034_3 := h13034c.2.2.2
                                        linarith only [hc14, hc45, hlam, hphi, p13034_1]
                                      · have p13034_0 := h13034c.1
                                        have p13034_1 := h13034c.2.1
                                        have p13034_2 := h13034c.2.2.1
                                        have p13034_3 := h13034c.2.2.2
                                        linarith only [hc24, hc45, hlam, hphi, p13034_1]
                                      · have p13034_0 := h13034c.1
                                        have p13034_1 := h13034c.2.1
                                        have p13034_2 := h13034c.2.2.1
                                        have p13034_3 := h13034c.2.2.2
                                        linarith only [hc34, hc45, hlam, hphi, p13034_1]
                                      · have p13034_0 := h13034c.1
                                        have p13034_1 := h13034c.2.1
                                        have p13034_2 := h13034c.2.2.1
                                        have p13034_3 := h13034c.2.2.2
                                        linarith only [hlam, p13034_0]
                                · linarith only [h13007, h13029, hlam]
                              · linarith only [h13002, h13028, hlam]
                            · linarith only [h13027, hlam, p13012_0]
                          · have p13012_0 := h13012c.1
                            have p13012_1 := h13012c.2.1
                            have p13012_2 := h13012c.2.2.1
                            have p13012_3 := h13012c.2.2.2
                            linarith only [h12905, hc02, hc23, hlam, hphi, p13012_1]
                          · have p13012_0 := h13012c.1
                            have p13012_1 := h13012c.2.1
                            have p13012_2 := h13012c.2.2.1
                            have p13012_3 := h13012c.2.2.2
                            linarith only [hlam, p13012_0]
                          · have p13012_0 := h13012c.1
                            have p13012_1 := h13012c.2.1
                            have p13012_2 := h13012c.2.2.1
                            have p13012_3 := h13012c.2.2.2
                            linarith only [h12905, hlam, p13012_0]
                          · have p13012_0 := h13012c.1
                            have p13012_1 := h13012c.2.1
                            have p13012_2 := h13012c.2.2.1
                            have p13012_3 := h13012c.2.2.2
                            rcases p13012_3 (m.d 0 2) (by simp) with h13066 | h13066
                            · linarith only [h0, h13066, hlam]
                            · linarith only [h12751, h13066, hlam]
                          · have p13012_0 := h13012c.1
                            have p13012_1 := h13012c.2.1
                            have p13012_2 := h13012c.2.2.1
                            have p13012_3 := h13012c.2.2.2
                            rcases p13012_3 (m.d 0 2) (by simp) with h13069 | h13069
                            · linarith only [h0, h13069, hlam]
                            · linarith only [h12752, h13069, hlam]
                          · have p13012_0 := h13012c.1
                            have p13012_1 := h13012c.2.1
                            have p13012_2 := h13012c.2.2.1
                            have p13012_3 := h13012c.2.2.2
                            rcases p13012_3 (m.d 0 2) (by simp) with h13072 | h13072
                            · linarith only [h13072, hlam, p13012_0]
                            · rcases p13012_3 (m.d 1 2) (by simp) with h13074 | h13074
                              · linarith only [h12905, h13074, hlam]
                              · linarith only [h0, h13074, hlam]
                          · have p13012_0 := h13012c.1
                            have p13012_1 := h13012c.2.1
                            have p13012_2 := h13012c.2.2.1
                            have p13012_3 := h13012c.2.2.2
                            linarith only [h0, hc01, hc23, hlam, hphi, ht12, p13012_1]
                          · have p13012_0 := h13012c.1
                            have p13012_1 := h13012c.2.1
                            have p13012_2 := h13012c.2.2.1
                            have p13012_3 := h13012c.2.2.2
                            linarith only [hlam, p13012_0]
                          · have p13012_0 := h13012c.1
                            have p13012_1 := h13012c.2.1
                            have p13012_2 := h13012c.2.2.1
                            have p13012_3 := h13012c.2.2.2
                            rcases p13012_3 (m.d 0 2) (by simp) with h13079 | h13079
                            · linarith only [h13079, h8886, hlam]
                            · linarith only [h12751, h13079, hlam]
                          · have p13012_0 := h13012c.1
                            have p13012_1 := h13012c.2.1
                            have p13012_2 := h13012c.2.2.1
                            have p13012_3 := h13012c.2.2.2
                            rcases p13012_3 (m.d 0 2) (by simp) with h13082 | h13082
                            · linarith only [h13082, h8886, hlam]
                            · linarith only [h12752, h13082, hlam]
                          · have p13012_0 := h13012c.1
                            have p13012_1 := h13012c.2.1
                            have p13012_2 := h13012c.2.2.1
                            have p13012_3 := h13012c.2.2.2
                            linarith only [h12751, hlam, p13012_0]
                          · have p13012_0 := h13012c.1
                            have p13012_1 := h13012c.2.1
                            have p13012_2 := h13012c.2.2.1
                            have p13012_3 := h13012c.2.2.2
                            linarith only [h13001, hlam, p13012_0]
                          · have p13012_0 := h13012c.1
                            have p13012_1 := h13012c.2.1
                            have p13012_2 := h13012c.2.2.1
                            have p13012_3 := h13012c.2.2.2
                            linarith only [h13006, hlam, p13012_0]
                          · have p13012_0 := h13012c.1
                            have p13012_1 := h13012c.2.1
                            have p13012_2 := h13012c.2.2.1
                            have p13012_3 := h13012c.2.2.2
                            linarith only [hlam, p13012_0]
                          · have p13012_0 := h13012c.1
                            have p13012_1 := h13012c.2.1
                            have p13012_2 := h13012c.2.2.1
                            have p13012_3 := h13012c.2.2.2
                            linarith only [h13008, hlam, p13012_0]
                          · have p13012_0 := h13012c.1
                            have p13012_1 := h13012c.2.1
                            have p13012_2 := h13012c.2.2.1
                            have p13012_3 := h13012c.2.2.2
                            linarith only [h12752, hlam, p13012_0]
                          · have p13012_0 := h13012c.1
                            have p13012_1 := h13012c.2.1
                            have p13012_2 := h13012c.2.2.1
                            have p13012_3 := h13012c.2.2.2
                            linarith only [h13002, hlam, p13012_0]
                          · have p13012_0 := h13012c.1
                            have p13012_1 := h13012c.2.1
                            have p13012_2 := h13012c.2.2.1
                            have p13012_3 := h13012c.2.2.2
                            linarith only [h13007, hlam, p13012_0]
                          · have p13012_0 := h13012c.1
                            have p13012_1 := h13012c.2.1
                            have p13012_2 := h13012c.2.2.1
                            have p13012_3 := h13012c.2.2.2
                            linarith only [h12752, h13006, h8886, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13012_1]
                          · have p13012_0 := h13012c.1
                            have p13012_1 := h13012c.2.1
                            have p13012_2 := h13012c.2.2.1
                            have p13012_3 := h13012c.2.2.2
                            linarith only [hlam, p13012_0]
                    · linarith only [h0, h12905, h13007, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h12905, h13002, h13004, h13006, h6874, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h0, h12751, h12753, h12905, h13003, hlam]
            · linarith only [h0, h12752, h13002, hlam]
          · linarith only [h0, h12751, h13001, hlam]
    · linarith only [h12751, h12753, h8886, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h13101 | h13101
    · rcases m.htr 0 4 5 (by decide) (by decide) with h13102 | h13102
      · linarith only [h12751, h12752, h13102, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h13104 | h13104
        · rcases m.htr 1 2 4 (by decide) (by decide) with h13105 | h13105
          · rcases m.htr 1 2 5 (by decide) (by decide) with h13106 | h13106
            · rcases m.htr 1 3 4 (by decide) (by decide) with h13107 | h13107
              · rcases m.htr 1 4 5 (by decide) (by decide) with h13108 | h13108
                · rcases m.htr 2 3 4 (by decide) (by decide) with h13109 | h13109
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h13110 | h13110
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h13111 | h13111
                      · linarith only [h12751, h12752, h13102, h13106, h13111, h6874, hc01, hc15, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h13113 | h13113
                        · linarith only [h12751, h12752, h13109, h13111, h13113, hlam]
                        · rcases h2bigk with h13115c | h13115c | h13115c | h13115c | h13115c | h13115c | h13115c | h13115c | h13115c | h13115c | h13115c | h13115c | h13115c | h13115c | h13115c | h13115c | h13115c | h13115c | h13115c | h13115c | h13115c | h13115c | h13115c | h13115c | h13115c
                          · have p13115_0 := h13115c.1
                            have p13115_1 := h13115c.2.1
                            have p13115_2 := h13115c.2.2.1
                            have p13115_3 := h13115c.2.2.2
                            linarith only [hlam, p13115_0]
                          · have p13115_0 := h13115c.1
                            have p13115_1 := h13115c.2.1
                            have p13115_2 := h13115c.2.2.1
                            have p13115_3 := h13115c.2.2.2
                            linarith only [h0, hlam, p13115_0]
                          · have p13115_0 := h13115c.1
                            have p13115_1 := h13115c.2.1
                            have p13115_2 := h13115c.2.2.1
                            have p13115_3 := h13115c.2.2.2
                            linarith only [h8886, hlam, p13115_0]
                          · have p13115_0 := h13115c.1
                            have p13115_1 := h13115c.2.1
                            have p13115_2 := h13115c.2.2.1
                            have p13115_3 := h13115c.2.2.2
                            linarith only [h12752, h13104, h13107, h13108, h13109, h13111, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13115_1]
                          · have p13115_0 := h13115c.1
                            have p13115_1 := h13115c.2.1
                            have p13115_2 := h13115c.2.2.1
                            have p13115_3 := h13115c.2.2.2
                            linarith only [h12752, hlam, p13115_0]
                          · have p13115_0 := h13115c.1
                            have p13115_1 := h13115c.2.1
                            have p13115_2 := h13115c.2.2.1
                            have p13115_3 := h13115c.2.2.2
                            rcases p13115_3 (m.d 0 2) (by simp) with h13121 | h13121
                            · linarith only [h0, h13121, hlam]
                            · rcases p13115_3 (m.d 1 2) (by simp) with h13123 | h13123
                              · rcases p13115_3 (m.d 2 3) (by simp) with h13124 | h13124
                                · linarith only [h13104, h13124, hlam]
                                · linarith only [h13124, h8886, hlam]
                              · linarith only [h0, h13123, hlam]
                          · have p13115_0 := h13115c.1
                            have p13115_1 := h13115c.2.1
                            have p13115_2 := h13115c.2.2.1
                            have p13115_3 := h13115c.2.2.2
                            linarith only [hlam, p13115_0]
                          · have p13115_0 := h13115c.1
                            have p13115_1 := h13115c.2.1
                            have p13115_2 := h13115c.2.2.1
                            have p13115_3 := h13115c.2.2.2
                            linarith only [h0, h12752, h13110, hc01, hc12, hlam, hphi, p13115_1]
                          · have p13115_0 := h13115c.1
                            have p13115_1 := h13115c.2.1
                            have p13115_2 := h13115c.2.2.1
                            have p13115_3 := h13115c.2.2.2
                            linarith only [h12751, h12752, h13104, h13110, hlam, p13115_2]
                          · have p13115_0 := h13115c.1
                            have p13115_1 := h13115c.2.1
                            have p13115_2 := h13115c.2.2.1
                            have p13115_3 := h13115c.2.2.2
                            linarith only [h12751, h12752, h13109, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13115_1]
                          · have p13115_0 := h13115c.1
                            have p13115_1 := h13115c.2.1
                            have p13115_2 := h13115c.2.2.1
                            have p13115_3 := h13115c.2.2.2
                            linarith only [h12751, h13104, h13109, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13115_1]
                          · have p13115_0 := h13115c.1
                            have p13115_1 := h13115c.2.1
                            have p13115_2 := h13115c.2.2.1
                            have p13115_3 := h13115c.2.2.2
                            linarith only [h13104, hlam, p13115_0]
                          · have p13115_0 := h13115c.1
                            have p13115_1 := h13115c.2.1
                            have p13115_2 := h13115c.2.2.1
                            have p13115_3 := h13115c.2.2.2
                            linarith only [hlam, p13115_0]
                          · have p13115_0 := h13115c.1
                            have p13115_1 := h13115c.2.1
                            have p13115_2 := h13115c.2.2.1
                            have p13115_3 := h13115c.2.2.2
                            rcases p13115_3 (m.d 0 2) (by simp) with h13135 | h13135
                            · linarith only [h13135, h8886, hlam]
                            · linarith only [h12751, h13135, hlam]
                          · have p13115_0 := h13115c.1
                            have p13115_1 := h13115c.2.1
                            have p13115_2 := h13115c.2.2.1
                            have p13115_3 := h13115c.2.2.2
                            linarith only [h12751, h12752, h13104, h13109, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13115_1]
                          · have p13115_0 := h13115c.1
                            have p13115_1 := h13115c.2.1
                            have p13115_2 := h13115c.2.2.1
                            have p13115_3 := h13115c.2.2.2
                            linarith only [h12751, hlam, p13115_0]
                          · have p13115_0 := h13115c.1
                            have p13115_1 := h13115c.2.1
                            have p13115_2 := h13115c.2.2.1
                            have p13115_3 := h13115c.2.2.2
                            linarith only [h13105, hlam, p13115_0]
                          · have p13115_0 := h13115c.1
                            have p13115_1 := h13115c.2.1
                            have p13115_2 := h13115c.2.2.1
                            have p13115_3 := h13115c.2.2.2
                            linarith only [h13109, hlam, p13115_0]
                          · have p13115_0 := h13115c.1
                            have p13115_1 := h13115c.2.1
                            have p13115_2 := h13115c.2.2.1
                            have p13115_3 := h13115c.2.2.2
                            linarith only [hlam, p13115_0]
                          · have p13115_0 := h13115c.1
                            have p13115_1 := h13115c.2.1
                            have p13115_2 := h13115c.2.2.1
                            have p13115_3 := h13115c.2.2.2
                            linarith only [h13111, hlam, p13115_0]
                          · have p13115_0 := h13115c.1
                            have p13115_1 := h13115c.2.1
                            have p13115_2 := h13115c.2.2.1
                            have p13115_3 := h13115c.2.2.2
                            linarith only [h12751, h13106, h13109, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13115_1]
                          · have p13115_0 := h13115c.1
                            have p13115_1 := h13115c.2.1
                            have p13115_2 := h13115c.2.2.1
                            have p13115_3 := h13115c.2.2.2
                            linarith only [h13106, hlam, p13115_0]
                          · have p13115_0 := h13115c.1
                            have p13115_1 := h13115c.2.1
                            have p13115_2 := h13115c.2.2.1
                            have p13115_3 := h13115c.2.2.2
                            linarith only [h13110, hlam, p13115_0]
                          · have p13115_0 := h13115c.1
                            have p13115_1 := h13115c.2.1
                            have p13115_2 := h13115c.2.2.1
                            have p13115_3 := h13115c.2.2.2
                            rcases p13115_3 (m.d 0 2) (by simp) with h13147 | h13147
                            · linarith only [h12752, h13147, hlam]
                            · linarith only [h12751, h13147, hlam]
                          · have p13115_0 := h13115c.1
                            have p13115_1 := h13115c.2.1
                            have p13115_2 := h13115c.2.2.1
                            have p13115_3 := h13115c.2.2.2
                            linarith only [hlam, p13115_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h13151 | h13151
                      · linarith only [h12751, h13102, h13151, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h13153 | h13153
                        · linarith only [h12751, h13101, h13110, h13151, h13153, h8886, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h12751, h13104, h13107, h13108, h13109, h13110, h13153, h8886, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h13101, h13109, h8886, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h13157 | h13157
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h13158 | h13158
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h13159 | h13159
                      · linarith only [h12751, h12752, h13108, h13158, h13159, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h13161 | h13161
                        · linarith only [h12751, h13108, h13157, h13161, h6874, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                        · rcases h2bigk with h13163c | h13163c | h13163c | h13163c | h13163c | h13163c | h13163c | h13163c | h13163c | h13163c | h13163c | h13163c | h13163c | h13163c | h13163c | h13163c | h13163c | h13163c | h13163c | h13163c | h13163c | h13163c | h13163c | h13163c | h13163c
                          · have p13163_0 := h13163c.1
                            have p13163_1 := h13163c.2.1
                            have p13163_2 := h13163c.2.2.1
                            have p13163_3 := h13163c.2.2.2
                            linarith only [hlam, p13163_0]
                          · have p13163_0 := h13163c.1
                            have p13163_1 := h13163c.2.1
                            have p13163_2 := h13163c.2.2.1
                            have p13163_3 := h13163c.2.2.2
                            linarith only [h0, hlam, p13163_0]
                          · have p13163_0 := h13163c.1
                            have p13163_1 := h13163c.2.1
                            have p13163_2 := h13163c.2.2.1
                            have p13163_3 := h13163c.2.2.2
                            linarith only [h8886, hlam, p13163_0]
                          · have p13163_0 := h13163c.1
                            have p13163_1 := h13163c.2.1
                            have p13163_2 := h13163c.2.2.1
                            have p13163_3 := h13163c.2.2.2
                            linarith only [h12752, h13104, h13158, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p13163_1]
                          · have p13163_0 := h13163c.1
                            have p13163_1 := h13163c.2.1
                            have p13163_2 := h13163c.2.2.1
                            have p13163_3 := h13163c.2.2.2
                            linarith only [h12752, hlam, p13163_0]
                          · have p13163_0 := h13163c.1
                            have p13163_1 := h13163c.2.1
                            have p13163_2 := h13163c.2.2.1
                            have p13163_3 := h13163c.2.2.2
                            rcases p13163_3 (m.d 0 2) (by simp) with h13169 | h13169
                            · linarith only [h0, h13169, hlam]
                            · rcases p13163_3 (m.d 1 2) (by simp) with h13171 | h13171
                              · rcases p13163_3 (m.d 2 3) (by simp) with h13172 | h13172
                                · linarith only [h13104, h13172, hlam]
                                · linarith only [h13172, h8886, hlam]
                              · linarith only [h0, h13171, hlam]
                          · have p13163_0 := h13163c.1
                            have p13163_1 := h13163c.2.1
                            have p13163_2 := h13163c.2.2.1
                            have p13163_3 := h13163c.2.2.2
                            linarith only [hlam, p13163_0]
                          · have p13163_0 := h13163c.1
                            have p13163_1 := h13163c.2.1
                            have p13163_2 := h13163c.2.2.1
                            have p13163_3 := h13163c.2.2.2
                            linarith only [h0, h12752, h13158, hc01, hc12, hlam, hphi, p13163_1]
                          · have p13163_0 := h13163c.1
                            have p13163_1 := h13163c.2.1
                            have p13163_2 := h13163c.2.2.1
                            have p13163_3 := h13163c.2.2.2
                            linarith only [h12751, h12752, h13104, h13158, hlam, p13163_2]
                          · have p13163_0 := h13163c.1
                            have p13163_1 := h13163c.2.1
                            have p13163_2 := h13163c.2.2.1
                            have p13163_3 := h13163c.2.2.2
                            linarith only [h12751, h12752, h13157, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13163_1]
                          · have p13163_0 := h13163c.1
                            have p13163_1 := h13163c.2.1
                            have p13163_2 := h13163c.2.2.1
                            have p13163_3 := h13163c.2.2.2
                            linarith only [h12751, h13104, h13157, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13163_1]
                          · have p13163_0 := h13163c.1
                            have p13163_1 := h13163c.2.1
                            have p13163_2 := h13163c.2.2.1
                            have p13163_3 := h13163c.2.2.2
                            linarith only [h13104, hlam, p13163_0]
                          · have p13163_0 := h13163c.1
                            have p13163_1 := h13163c.2.1
                            have p13163_2 := h13163c.2.2.1
                            have p13163_3 := h13163c.2.2.2
                            linarith only [hlam, p13163_0]
                          · have p13163_0 := h13163c.1
                            have p13163_1 := h13163c.2.1
                            have p13163_2 := h13163c.2.2.1
                            have p13163_3 := h13163c.2.2.2
                            rcases p13163_3 (m.d 0 2) (by simp) with h13183 | h13183
                            · linarith only [h13183, h8886, hlam]
                            · linarith only [h12751, h13183, hlam]
                          · have p13163_0 := h13163c.1
                            have p13163_1 := h13163c.2.1
                            have p13163_2 := h13163c.2.2.1
                            have p13163_3 := h13163c.2.2.2
                            linarith only [h12751, h12752, h13104, h13157, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13163_1]
                          · have p13163_0 := h13163c.1
                            have p13163_1 := h13163c.2.1
                            have p13163_2 := h13163c.2.2.1
                            have p13163_3 := h13163c.2.2.2
                            linarith only [h12751, hlam, p13163_0]
                          · have p13163_0 := h13163c.1
                            have p13163_1 := h13163c.2.1
                            have p13163_2 := h13163c.2.2.1
                            have p13163_3 := h13163c.2.2.2
                            linarith only [h13105, hlam, p13163_0]
                          · have p13163_0 := h13163c.1
                            have p13163_1 := h13163c.2.1
                            have p13163_2 := h13163c.2.2.1
                            have p13163_3 := h13163c.2.2.2
                            linarith only [h13157, hlam, p13163_0]
                          · have p13163_0 := h13163c.1
                            have p13163_1 := h13163c.2.1
                            have p13163_2 := h13163c.2.2.1
                            have p13163_3 := h13163c.2.2.2
                            linarith only [hlam, p13163_0]
                          · have p13163_0 := h13163c.1
                            have p13163_1 := h13163c.2.1
                            have p13163_2 := h13163c.2.2.1
                            have p13163_3 := h13163c.2.2.2
                            linarith only [h13159, hlam, p13163_0]
                          · have p13163_0 := h13163c.1
                            have p13163_1 := h13163c.2.1
                            have p13163_2 := h13163c.2.2.1
                            have p13163_3 := h13163c.2.2.2
                            linarith only [h12751, h13106, h13157, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13163_1]
                          · have p13163_0 := h13163c.1
                            have p13163_1 := h13163c.2.1
                            have p13163_2 := h13163c.2.2.1
                            have p13163_3 := h13163c.2.2.2
                            linarith only [h13106, hlam, p13163_0]
                          · have p13163_0 := h13163c.1
                            have p13163_1 := h13163c.2.1
                            have p13163_2 := h13163c.2.2.1
                            have p13163_3 := h13163c.2.2.2
                            linarith only [h13158, hlam, p13163_0]
                          · have p13163_0 := h13163c.1
                            have p13163_1 := h13163c.2.1
                            have p13163_2 := h13163c.2.2.1
                            have p13163_3 := h13163c.2.2.2
                            rcases p13163_3 (m.d 0 2) (by simp) with h13195 | h13195
                            · linarith only [h12752, h13195, hlam]
                            · linarith only [h12751, h13195, hlam]
                          · have p13163_0 := h13163c.1
                            have p13163_1 := h13163c.2.1
                            have p13163_2 := h13163c.2.2.1
                            have p13163_3 := h13163c.2.2.2
                            linarith only [hlam, p13163_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h13199 | h13199
                      · linarith only [h12751, h12752, h13106, h13108, h13158, h13199, h8886, hc05, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h13201 | h13201
                        · linarith only [h13108, h13201, h6874, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h12751, h13157, h13158, h13201, h8886, hc34, hc45, hlam, hphi]
                  · linarith only [h13101, h13157, h8886, hlam]
              · linarith only [h12751, h13101, h13104, h13107, h8886, hlam]
            · linarith only [h13104, h13106, h8886, hc02, hc25, hlam, hphi]
          · linarith only [h12751, h13104, h13105, h8886, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h13208 | h13208
          · rcases m.htr 1 2 5 (by decide) (by decide) with h13209 | h13209
            · linarith only [h12751, h12752, h13104, h13209, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h13211 | h13211
              · rcases m.htr 1 4 5 (by decide) (by decide) with h13212 | h13212
                · linarith only [h13102, h13104, h13208, h13212, h6874, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h13214 | h13214
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h13215 | h13215
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h13216 | h13216
                      · linarith only [h12751, h13212, h13216, h6874, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h13218 | h13218
                        · linarith only [h0, h13209, h13216, h13218, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases h2bigk with h13220c | h13220c | h13220c | h13220c | h13220c | h13220c | h13220c | h13220c | h13220c | h13220c | h13220c | h13220c | h13220c | h13220c | h13220c | h13220c | h13220c | h13220c | h13220c | h13220c | h13220c | h13220c | h13220c | h13220c | h13220c
                          · have p13220_0 := h13220c.1
                            have p13220_1 := h13220c.2.1
                            have p13220_2 := h13220c.2.2.1
                            have p13220_3 := h13220c.2.2.2
                            linarith only [hlam, p13220_0]
                          · have p13220_0 := h13220c.1
                            have p13220_1 := h13220c.2.1
                            have p13220_2 := h13220c.2.2.1
                            have p13220_3 := h13220c.2.2.2
                            linarith only [h0, hlam, p13220_0]
                          · have p13220_0 := h13220c.1
                            have p13220_1 := h13220c.2.1
                            have p13220_2 := h13220c.2.2.1
                            have p13220_3 := h13220c.2.2.2
                            linarith only [h8886, hlam, p13220_0]
                          · have p13220_0 := h13220c.1
                            have p13220_1 := h13220c.2.1
                            have p13220_2 := h13220c.2.2.1
                            have p13220_3 := h13220c.2.2.2
                            linarith only [h0, h13209, h13214, h13216, hc34, hc45, hlam, hphi, p13220_1]
                          · have p13220_0 := h13220c.1
                            have p13220_1 := h13220c.2.1
                            have p13220_2 := h13220c.2.2.1
                            have p13220_3 := h13220c.2.2.2
                            linarith only [h12752, hlam, p13220_0]
                          · have p13220_0 := h13220c.1
                            have p13220_1 := h13220c.2.1
                            have p13220_2 := h13220c.2.2.1
                            have p13220_3 := h13220c.2.2.2
                            linarith only [h13209, hc02, hc25, hlam, hphi, p13220_1]
                          · have p13220_0 := h13220c.1
                            have p13220_1 := h13220c.2.1
                            have p13220_2 := h13220c.2.2.1
                            have p13220_3 := h13220c.2.2.2
                            linarith only [hlam, p13220_0]
                          · have p13220_0 := h13220c.1
                            have p13220_1 := h13220c.2.1
                            have p13220_2 := h13220c.2.2.1
                            have p13220_3 := h13220c.2.2.2
                            linarith only [h13104, hlam, p13220_0]
                          · have p13220_0 := h13220c.1
                            have p13220_1 := h13220c.2.1
                            have p13220_2 := h13220c.2.2.1
                            have p13220_3 := h13220c.2.2.2
                            linarith only [h13209, h13214, h13216, hc34, hc45, hlam, hphi, p13220_1]
                          · have p13220_0 := h13220c.1
                            have p13220_1 := h13220c.2.1
                            have p13220_2 := h13220c.2.2.1
                            have p13220_3 := h13220c.2.2.2
                            linarith only [h13209, hlam, p13220_0]
                          · have p13220_0 := h13220c.1
                            have p13220_1 := h13220c.2.1
                            have p13220_2 := h13220c.2.2.1
                            have p13220_3 := h13220c.2.2.2
                            rcases p13220_3 (m.d 0 2) (by simp) with h13231 | h13231
                            · linarith only [h13231, hlam, p13220_0]
                            · rcases p13220_3 (m.d 1 2) (by simp) with h13233 | h13233
                              · linarith only [h13104, h13233, hlam]
                              · linarith only [h0, h13233, hlam]
                          · have p13220_0 := h13220c.1
                            have p13220_1 := h13220c.2.1
                            have p13220_2 := h13220c.2.2.1
                            have p13220_3 := h13220c.2.2.2
                            linarith only [h0, hc01, hc23, hlam, hphi, ht12, p13220_1]
                          · have p13220_0 := h13220c.1
                            have p13220_1 := h13220c.2.1
                            have p13220_2 := h13220c.2.2.1
                            have p13220_3 := h13220c.2.2.2
                            linarith only [hlam, p13220_0]
                          · have p13220_0 := h13220c.1
                            have p13220_1 := h13220c.2.1
                            have p13220_2 := h13220c.2.2.1
                            have p13220_3 := h13220c.2.2.2
                            rcases p13220_3 (m.d 0 2) (by simp) with h13238 | h13238
                            · linarith only [h13238, h8886, hlam]
                            · linarith only [h12751, h13238, hlam]
                          · have p13220_0 := h13220c.1
                            have p13220_1 := h13220c.2.1
                            have p13220_2 := h13220c.2.2.1
                            have p13220_3 := h13220c.2.2.2
                            linarith only [h12752, hc02, hc23, hlam, hphi, p13220_1]
                          · have p13220_0 := h13220c.1
                            have p13220_1 := h13220c.2.1
                            have p13220_2 := h13220c.2.2.1
                            have p13220_3 := h13220c.2.2.2
                            linarith only [h12751, hlam, p13220_0]
                          · have p13220_0 := h13220c.1
                            have p13220_1 := h13220c.2.1
                            have p13220_2 := h13220c.2.2.1
                            have p13220_3 := h13220c.2.2.2
                            linarith only [h13208, hlam, p13220_0]
                          · have p13220_0 := h13220c.1
                            have p13220_1 := h13220c.2.1
                            have p13220_2 := h13220c.2.2.1
                            have p13220_3 := h13220c.2.2.2
                            linarith only [h13214, hlam, p13220_0]
                          · have p13220_0 := h13220c.1
                            have p13220_1 := h13220c.2.1
                            have p13220_2 := h13220c.2.2.1
                            have p13220_3 := h13220c.2.2.2
                            linarith only [hlam, p13220_0]
                          · have p13220_0 := h13220c.1
                            have p13220_1 := h13220c.2.1
                            have p13220_2 := h13220c.2.2.1
                            have p13220_3 := h13220c.2.2.2
                            linarith only [h13216, hlam, p13220_0]
                          · have p13220_0 := h13220c.1
                            have p13220_1 := h13220c.2.1
                            have p13220_2 := h13220c.2.2.1
                            have p13220_3 := h13220c.2.2.2
                            linarith only [h12751, h13214, h13216, hc34, hc45, hlam, hphi, p13220_1]
                          · have p13220_0 := h13220c.1
                            have p13220_1 := h13220c.2.1
                            have p13220_2 := h13220c.2.2.1
                            have p13220_3 := h13220c.2.2.2
                            linarith only [h13208, h6874, hc01, hc25, hlam, hphi, ht12, p13220_1]
                          · have p13220_0 := h13220c.1
                            have p13220_1 := h13220c.2.1
                            have p13220_2 := h13220c.2.2.1
                            have p13220_3 := h13220c.2.2.2
                            linarith only [h13215, hlam, p13220_0]
                          · have p13220_0 := h13220c.1
                            have p13220_1 := h13220c.2.1
                            have p13220_2 := h13220c.2.2.1
                            have p13220_3 := h13220c.2.2.2
                            rcases p13220_3 (m.d 0 2) (by simp) with h13250 | h13250
                            · linarith only [h12752, h13250, hlam]
                            · linarith only [h12751, h13250, hlam]
                          · have p13220_0 := h13220c.1
                            have p13220_1 := h13220c.2.1
                            have p13220_2 := h13220c.2.2.1
                            have p13220_3 := h13220c.2.2.2
                            linarith only [hlam, p13220_0]
                    · linarith only [h13104, h13208, h13215, h6874, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h13104, h13208, h13214, h6874, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h0, h12751, h13101, h13104, h13211, hlam]
          · linarith only [h0, h12751, h13208, hlam]
    · linarith only [h12751, h13101, h8886, hlam]

end R2N4
