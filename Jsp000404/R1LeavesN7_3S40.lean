import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 19638000 in
set_option maxHeartbeats 19638000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s13_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h14799 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h14800 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h14801 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h14802 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14803 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h14804 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h14805 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  rcases m.htr 0 3 5 (by decide) (by decide) with h14806 | h14806
  · rcases m.htr 0 4 5 (by decide) (by decide) with h14807 | h14807
    · rcases m.htr 1 2 3 (by decide) (by decide) with h14808 | h14808
      · rcases m.htr 1 2 4 (by decide) (by decide) with h14809 | h14809
        · rcases m.htr 1 2 5 (by decide) (by decide) with h14810 | h14810
          · rcases m.htr 1 3 4 (by decide) (by decide) with h14811 | h14811
            · rcases m.htr 1 3 5 (by decide) (by decide) with h14812 | h14812
              · rcases m.htr 1 4 5 (by decide) (by decide) with h14813 | h14813
                · rcases m.htr 2 3 4 (by decide) (by decide) with h14814 | h14814
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h14815 | h14815
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h14816 | h14816
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h14817 | h14817
                        · linarith only [h0, h14799, h14808, h14814, h14817, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h0, h14799, h14811, h14813, h14817, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h14799, h14811, h14813, h14816, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h14799, h14812, h14815, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h14799, h14811, h14814, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h14823 | h14823
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h14824 | h14824
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h14825 | h14825
                      · linarith only [h14809, h14813, h14825, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h14827 | h14827
                        · linarith only [h14809, h14813, h14823, h14827, hlam]
                        · rcases h1bigk with h14829c | h14829c | h14829c | h14829c | h14829c | h14829c | h14829c | h14829c | h14829c | h14829c | h14829c | h14829c | h14829c | h14829c | h14829c | h14829c | h14829c | h14829c | h14829c | h14829c | h14829c | h14829c | h14829c | h14829c | h14829c
                          · have p14829_0 := h14829c.1
                            have p14829_1 := h14829c.2.1
                            have p14829_2 := h14829c.2.2.1
                            have p14829_3 := h14829c.2.2.2
                            linarith only [hlam, p14829_0]
                          · have p14829_0 := h14829c.1
                            have p14829_1 := h14829c.2.1
                            have p14829_2 := h14829c.2.2.1
                            have p14829_3 := h14829c.2.2.2
                            linarith only [h0, hlam, p14829_0]
                          · have p14829_0 := h14829c.1
                            have p14829_1 := h14829c.2.1
                            have p14829_2 := h14829c.2.2.1
                            have p14829_3 := h14829c.2.2.2
                            linarith only [h0, h14808, h14824, h14827, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14829_1]
                          · have p14829_0 := h14829c.1
                            have p14829_1 := h14829c.2.1
                            have p14829_2 := h14829c.2.2.1
                            have p14829_3 := h14829c.2.2.2
                            rcases p14829_3 (m.d 0 1) (by simp) with h14833 | h14833
                            · rcases p14829_3 (m.d 1 2) (by simp) with h14834 | h14834
                              · rcases p14829_3 (m.d 1 3) (by simp) with h14835 | h14835
                                · linarith only [h14799, h14835, hlam]
                                · linarith only [h14811, h14835, hlam]
                              · linarith only [h14809, h14834, hlam]
                            · linarith only [h14833, hlam, p14829_0]
                          · have p14829_0 := h14829c.1
                            have p14829_1 := h14829c.2.1
                            have p14829_2 := h14829c.2.2.1
                            have p14829_3 := h14829c.2.2.2
                            rcases p14829_3 (m.d 0 1) (by simp) with h14840 | h14840
                            · rcases p14829_3 (m.d 1 2) (by simp) with h14841 | h14841
                              · rcases p14829_3 (m.d 1 3) (by simp) with h14842 | h14842
                                · linarith only [h14799, h14842, hlam]
                                · linarith only [h14812, h14842, hlam]
                              · linarith only [h14810, h14841, hlam]
                            · linarith only [h14840, hlam, p14829_0]
                          · have p14829_0 := h14829c.1
                            have p14829_1 := h14829c.2.1
                            have p14829_2 := h14829c.2.2.1
                            have p14829_3 := h14829c.2.2.2
                            linarith only [h14799, h14805, h14807, h14813, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p14829_1]
                          · have p14829_0 := h14829c.1
                            have p14829_1 := h14829c.2.1
                            have p14829_2 := h14829c.2.2.1
                            have p14829_3 := h14829c.2.2.2
                            linarith only [hlam, p14829_0]
                          · have p14829_0 := h14829c.1
                            have p14829_1 := h14829c.2.1
                            have p14829_2 := h14829c.2.2.1
                            have p14829_3 := h14829c.2.2.2
                            rcases p14829_3 (m.d 0 1) (by simp) with h14849 | h14849
                            · linarith only [h0, h14849, hlam]
                            · linarith only [h14799, h14849, hlam]
                          · have p14829_0 := h14829c.1
                            have p14829_1 := h14829c.2.1
                            have p14829_2 := h14829c.2.2.1
                            have p14829_3 := h14829c.2.2.2
                            linarith only [h0, h14799, h14805, h14807, h14813, hlam, p14829_2]
                          · have p14829_0 := h14829c.1
                            have p14829_1 := h14829c.2.1
                            have p14829_2 := h14829c.2.2.1
                            have p14829_3 := h14829c.2.2.2
                            rcases p14829_3 (m.d 0 1) (by simp) with h14853 | h14853
                            · linarith only [h0, h14853, hlam]
                            · linarith only [h14801, h14853, hlam]
                          · have p14829_0 := h14829c.1
                            have p14829_1 := h14829c.2.1
                            have p14829_2 := h14829c.2.2.1
                            have p14829_3 := h14829c.2.2.2
                            linarith only [h14799, hlam, p14829_0]
                          · have p14829_0 := h14829c.1
                            have p14829_1 := h14829c.2.1
                            have p14829_2 := h14829c.2.2.1
                            have p14829_3 := h14829c.2.2.2
                            linarith only [h14808, hlam, p14829_1]
                          · have p14829_0 := h14829c.1
                            have p14829_1 := h14829c.2.1
                            have p14829_2 := h14829c.2.2.1
                            have p14829_3 := h14829c.2.2.2
                            linarith only [hlam, p14829_0]
                          · have p14829_0 := h14829c.1
                            have p14829_1 := h14829c.2.1
                            have p14829_2 := h14829c.2.2.1
                            have p14829_3 := h14829c.2.2.2
                            linarith only [h0, h14799, h14809, h14823, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14829_1]
                          · have p14829_0 := h14829c.1
                            have p14829_1 := h14829c.2.1
                            have p14829_2 := h14829c.2.2.1
                            have p14829_3 := h14829c.2.2.2
                            linarith only [h0, h14799, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p14829_1]
                          · have p14829_0 := h14829c.1
                            have p14829_1 := h14829c.2.1
                            have p14829_2 := h14829c.2.2.1
                            have p14829_3 := h14829c.2.2.2
                            linarith only [h14800, hlam, p14829_0]
                          · have p14829_0 := h14829c.1
                            have p14829_1 := h14829c.2.1
                            have p14829_2 := h14829c.2.2.1
                            have p14829_3 := h14829c.2.2.2
                            linarith only [h14809, hlam, p14829_1]
                          · have p14829_0 := h14829c.1
                            have p14829_1 := h14829c.2.1
                            have p14829_2 := h14829c.2.2.1
                            have p14829_3 := h14829c.2.2.2
                            linarith only [h14811, hlam, p14829_0]
                          · have p14829_0 := h14829c.1
                            have p14829_1 := h14829c.2.1
                            have p14829_2 := h14829c.2.2.1
                            have p14829_3 := h14829c.2.2.2
                            linarith only [hlam, p14829_0]
                          · have p14829_0 := h14829c.1
                            have p14829_1 := h14829c.2.1
                            have p14829_2 := h14829c.2.2.1
                            have p14829_3 := h14829c.2.2.2
                            linarith only [h14813, hlam, p14829_1]
                          · have p14829_0 := h14829c.1
                            have p14829_1 := h14829c.2.1
                            have p14829_2 := h14829c.2.2.1
                            have p14829_3 := h14829c.2.2.2
                            linarith only [h14801, hlam, p14829_0]
                          · have p14829_0 := h14829c.1
                            have p14829_1 := h14829c.2.1
                            have p14829_2 := h14829c.2.2.1
                            have p14829_3 := h14829c.2.2.2
                            linarith only [h14810, hlam, p14829_1]
                          · have p14829_0 := h14829c.1
                            have p14829_1 := h14829c.2.1
                            have p14829_2 := h14829c.2.2.1
                            have p14829_3 := h14829c.2.2.2
                            linarith only [h14812, hlam, p14829_0]
                          · have p14829_0 := h14829c.1
                            have p14829_1 := h14829c.2.1
                            have p14829_2 := h14829c.2.2.1
                            have p14829_3 := h14829c.2.2.2
                            linarith only [h0, h14801, h14809, h14823, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14829_1]
                          · have p14829_0 := h14829c.1
                            have p14829_1 := h14829c.2.1
                            have p14829_2 := h14829c.2.2.1
                            have p14829_3 := h14829c.2.2.2
                            linarith only [hlam, p14829_0]
                    · linarith only [h0, h14799, h14812, h14824, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h14799, h14811, h14823, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h14799, h14806, h14811, h14812, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h14874 | h14874
              · linarith only [h0, h14799, h14805, h14811, h14874, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h14876 | h14876
                · rcases m.htr 2 3 4 (by decide) (by decide) with h14877 | h14877
                  · linarith only [h0, h14799, h14808, h14811, h14876, h14877, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h14879 | h14879
                    · linarith only [h14808, h14874, h14879, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h14881 | h14881
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h14882 | h14882
                        · rcases h1bigk with h14883c | h14883c | h14883c | h14883c | h14883c | h14883c | h14883c | h14883c | h14883c | h14883c | h14883c | h14883c | h14883c | h14883c | h14883c | h14883c | h14883c | h14883c | h14883c | h14883c | h14883c | h14883c | h14883c | h14883c | h14883c
                          · have p14883_0 := h14883c.1
                            have p14883_1 := h14883c.2.1
                            have p14883_2 := h14883c.2.2.1
                            have p14883_3 := h14883c.2.2.2
                            linarith only [hlam, p14883_0]
                          · have p14883_0 := h14883c.1
                            have p14883_1 := h14883c.2.1
                            have p14883_2 := h14883c.2.2.1
                            have p14883_3 := h14883c.2.2.2
                            linarith only [h0, hlam, p14883_0]
                          · have p14883_0 := h14883c.1
                            have p14883_1 := h14883c.2.1
                            have p14883_2 := h14883c.2.2.1
                            have p14883_3 := h14883c.2.2.2
                            rcases p14883_3 (m.d 0 1) (by simp) with h14886 | h14886
                            · rcases p14883_3 (m.d 1 2) (by simp) with h14887 | h14887
                              · rcases p14883_3 (m.d 1 3) (by simp) with h14888 | h14888
                                · linarith only [h14888, hlam, p14883_0]
                                · rcases p14883_3 (m.d 1 4) (by simp) with h14890 | h14890
                                  · linarith only [h14800, h14890, hlam]
                                  · linarith only [h14811, h14890, hlam]
                              · linarith only [h14808, h14887, hlam]
                            · linarith only [h14886, hlam, p14883_0]
                          · have p14883_0 := h14883c.1
                            have p14883_1 := h14883c.2.1
                            have p14883_2 := h14883c.2.2.1
                            have p14883_3 := h14883c.2.2.2
                            linarith only [h0, h14809, h14881, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14883_1]
                          · have p14883_0 := h14883c.1
                            have p14883_1 := h14883c.2.1
                            have p14883_2 := h14883c.2.2.1
                            have p14883_3 := h14883c.2.2.2
                            rcases p14883_3 (m.d 0 1) (by simp) with h14896 | h14896
                            · rcases p14883_3 (m.d 1 2) (by simp) with h14897 | h14897
                              · rcases p14883_3 (m.d 1 3) (by simp) with h14898 | h14898
                                · linarith only [h14799, h14898, hlam]
                                · rcases p14883_3 (m.d 1 4) (by simp) with h14900 | h14900
                                  · linarith only [h14800, h14900, hlam]
                                  · linarith only [h14876, h14900, hlam]
                              · linarith only [h14810, h14897, hlam]
                            · linarith only [h14896, hlam, p14883_0]
                          · have p14883_0 := h14883c.1
                            have p14883_1 := h14883c.2.1
                            have p14883_2 := h14883c.2.2.1
                            have p14883_3 := h14883c.2.2.2
                            linarith only [h14799, h14805, h14874, h14882, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14883_1]
                          · have p14883_0 := h14883c.1
                            have p14883_1 := h14883c.2.1
                            have p14883_2 := h14883c.2.2.1
                            have p14883_3 := h14883c.2.2.2
                            linarith only [hlam, p14883_0]
                          · have p14883_0 := h14883c.1
                            have p14883_1 := h14883c.2.1
                            have p14883_2 := h14883c.2.2.1
                            have p14883_3 := h14883c.2.2.2
                            linarith only [h0, h14799, h14805, h14874, h14882, hlam, p14883_2]
                          · have p14883_0 := h14883c.1
                            have p14883_1 := h14883c.2.1
                            have p14883_2 := h14883c.2.2.1
                            have p14883_3 := h14883c.2.2.2
                            rcases p14883_3 (m.d 0 1) (by simp) with h14908 | h14908
                            · linarith only [h0, h14908, hlam]
                            · linarith only [h14800, h14908, hlam]
                          · have p14883_0 := h14883c.1
                            have p14883_1 := h14883c.2.1
                            have p14883_2 := h14883c.2.2.1
                            have p14883_3 := h14883c.2.2.2
                            rcases p14883_3 (m.d 0 1) (by simp) with h14911 | h14911
                            · linarith only [h0, h14911, hlam]
                            · linarith only [h14801, h14911, hlam]
                          · have p14883_0 := h14883c.1
                            have p14883_1 := h14883c.2.1
                            have p14883_2 := h14883c.2.2.1
                            have p14883_3 := h14883c.2.2.2
                            linarith only [h14799, hlam, p14883_0]
                          · have p14883_0 := h14883c.1
                            have p14883_1 := h14883c.2.1
                            have p14883_2 := h14883c.2.2.1
                            have p14883_3 := h14883c.2.2.2
                            linarith only [h14808, hlam, p14883_1]
                          · have p14883_0 := h14883c.1
                            have p14883_1 := h14883c.2.1
                            have p14883_2 := h14883c.2.2.1
                            have p14883_3 := h14883c.2.2.2
                            linarith only [hlam, p14883_0]
                          · have p14883_0 := h14883c.1
                            have p14883_1 := h14883c.2.1
                            have p14883_2 := h14883c.2.2.1
                            have p14883_3 := h14883c.2.2.2
                            linarith only [h14811, hlam, p14883_1]
                          · have p14883_0 := h14883c.1
                            have p14883_1 := h14883c.2.1
                            have p14883_2 := h14883c.2.2.1
                            have p14883_3 := h14883c.2.2.2
                            linarith only [h14874, hlam, p14883_1]
                          · have p14883_0 := h14883c.1
                            have p14883_1 := h14883c.2.1
                            have p14883_2 := h14883c.2.2.1
                            have p14883_3 := h14883c.2.2.2
                            linarith only [h14800, hlam, p14883_0]
                          · have p14883_0 := h14883c.1
                            have p14883_1 := h14883c.2.1
                            have p14883_2 := h14883c.2.2.1
                            have p14883_3 := h14883c.2.2.2
                            linarith only [h14809, hlam, p14883_1]
                          · have p14883_0 := h14883c.1
                            have p14883_1 := h14883c.2.1
                            have p14883_2 := h14883c.2.2.1
                            have p14883_3 := h14883c.2.2.2
                            linarith only [h0, h14800, h14808, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14883_1]
                          · have p14883_0 := h14883c.1
                            have p14883_1 := h14883c.2.1
                            have p14883_2 := h14883c.2.2.1
                            have p14883_3 := h14883c.2.2.2
                            linarith only [hlam, p14883_0]
                          · have p14883_0 := h14883c.1
                            have p14883_1 := h14883c.2.1
                            have p14883_2 := h14883c.2.2.1
                            have p14883_3 := h14883c.2.2.2
                            linarith only [h0, h14799, h14805, h14811, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p14883_1]
                          · have p14883_0 := h14883c.1
                            have p14883_1 := h14883c.2.1
                            have p14883_2 := h14883c.2.2.1
                            have p14883_3 := h14883c.2.2.2
                            linarith only [h14801, hlam, p14883_0]
                          · have p14883_0 := h14883c.1
                            have p14883_1 := h14883c.2.1
                            have p14883_2 := h14883c.2.2.1
                            have p14883_3 := h14883c.2.2.2
                            linarith only [h14810, hlam, p14883_1]
                          · have p14883_0 := h14883c.1
                            have p14883_1 := h14883c.2.1
                            have p14883_2 := h14883c.2.2.1
                            have p14883_3 := h14883c.2.2.2
                            linarith only [h0, h14801, h14808, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14883_1]
                          · have p14883_0 := h14883c.1
                            have p14883_1 := h14883c.2.1
                            have p14883_2 := h14883c.2.2.1
                            have p14883_3 := h14883c.2.2.2
                            linarith only [h14876, hlam, p14883_0]
                          · have p14883_0 := h14883c.1
                            have p14883_1 := h14883c.2.1
                            have p14883_2 := h14883c.2.2.1
                            have p14883_3 := h14883c.2.2.2
                            linarith only [hlam, p14883_0]
                        · linarith only [h14809, h14811, h14881, h14882, hlam]
                      · linarith only [h0, h14800, h14876, h14881, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h14931 | h14931
                  · linarith only [h14808, h14811, h14931, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h14933 | h14933
                    · linarith only [h0, h14799, h14805, h14807, h14808, h14811, h14876, h14933, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h14935 | h14935
                      · linarith only [h14809, h14876, h14935, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h14937 | h14937
                        · linarith only [h0, h14799, h14805, h14876, h14937, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h14799, h14805, h14807, h14808, h14811, h14937, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
          · linarith only [h0, h14804, h14810, hlam]
        · linarith only [h0, h14803, h14809, hlam]
      · linarith only [h0, h14802, h14808, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h14943 | h14943
      · rcases m.htr 1 2 4 (by decide) (by decide) with h14944 | h14944
        · rcases m.htr 1 2 5 (by decide) (by decide) with h14945 | h14945
          · rcases m.htr 1 3 4 (by decide) (by decide) with h14946 | h14946
            · rcases m.htr 1 3 5 (by decide) (by decide) with h14947 | h14947
              · rcases m.htr 1 4 5 (by decide) (by decide) with h14948 | h14948
                · linarith only [h0, h14800, h14807, h14948, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h14950 | h14950
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h14951 | h14951
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h14952 | h14952
                      · linarith only [h14800, h14807, h14944, h14952, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h14954 | h14954
                        · linarith only [h14800, h14807, h14944, h14950, h14954, hlam]
                        · rcases h1bigk with h14956c | h14956c | h14956c | h14956c | h14956c | h14956c | h14956c | h14956c | h14956c | h14956c | h14956c | h14956c | h14956c | h14956c | h14956c | h14956c | h14956c | h14956c | h14956c | h14956c | h14956c | h14956c | h14956c | h14956c | h14956c
                          · have p14956_0 := h14956c.1
                            have p14956_1 := h14956c.2.1
                            have p14956_2 := h14956c.2.2.1
                            have p14956_3 := h14956c.2.2.2
                            linarith only [hlam, p14956_0]
                          · have p14956_0 := h14956c.1
                            have p14956_1 := h14956c.2.1
                            have p14956_2 := h14956c.2.2.1
                            have p14956_3 := h14956c.2.2.2
                            linarith only [h0, hlam, p14956_0]
                          · have p14956_0 := h14956c.1
                            have p14956_1 := h14956c.2.1
                            have p14956_2 := h14956c.2.2.1
                            have p14956_3 := h14956c.2.2.2
                            linarith only [h0, h14943, h14951, h14954, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14956_1]
                          · have p14956_0 := h14956c.1
                            have p14956_1 := h14956c.2.1
                            have p14956_2 := h14956c.2.2.1
                            have p14956_3 := h14956c.2.2.2
                            rcases p14956_3 (m.d 0 1) (by simp) with h14960 | h14960
                            · rcases p14956_3 (m.d 1 2) (by simp) with h14961 | h14961
                              · rcases p14956_3 (m.d 1 3) (by simp) with h14962 | h14962
                                · linarith only [h14799, h14962, hlam]
                                · linarith only [h14946, h14962, hlam]
                              · linarith only [h14944, h14961, hlam]
                            · linarith only [h14960, hlam, p14956_0]
                          · have p14956_0 := h14956c.1
                            have p14956_1 := h14956c.2.1
                            have p14956_2 := h14956c.2.2.1
                            have p14956_3 := h14956c.2.2.2
                            rcases p14956_3 (m.d 0 1) (by simp) with h14967 | h14967
                            · rcases p14956_3 (m.d 1 2) (by simp) with h14968 | h14968
                              · rcases p14956_3 (m.d 1 3) (by simp) with h14969 | h14969
                                · linarith only [h14799, h14969, hlam]
                                · linarith only [h14947, h14969, hlam]
                              · linarith only [h14945, h14968, hlam]
                            · linarith only [h14967, hlam, p14956_0]
                          · have p14956_0 := h14956c.1
                            have p14956_1 := h14956c.2.1
                            have p14956_2 := h14956c.2.2.1
                            have p14956_3 := h14956c.2.2.2
                            linarith only [h14799, h14943, h14951, h14954, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14956_1]
                          · have p14956_0 := h14956c.1
                            have p14956_1 := h14956c.2.1
                            have p14956_2 := h14956c.2.2.1
                            have p14956_3 := h14956c.2.2.2
                            linarith only [hlam, p14956_0]
                          · have p14956_0 := h14956c.1
                            have p14956_1 := h14956c.2.1
                            have p14956_2 := h14956c.2.2.1
                            have p14956_3 := h14956c.2.2.2
                            rcases p14956_3 (m.d 0 1) (by simp) with h14976 | h14976
                            · linarith only [h0, h14976, hlam]
                            · linarith only [h14799, h14976, hlam]
                          · have p14956_0 := h14956c.1
                            have p14956_1 := h14956c.2.1
                            have p14956_2 := h14956c.2.2.1
                            have p14956_3 := h14956c.2.2.2
                            rcases p14956_3 (m.d 0 1) (by simp) with h14979 | h14979
                            · linarith only [h0, h14979, hlam]
                            · linarith only [h14800, h14979, hlam]
                          · have p14956_0 := h14956c.1
                            have p14956_1 := h14956c.2.1
                            have p14956_2 := h14956c.2.2.1
                            have p14956_3 := h14956c.2.2.2
                            rcases p14956_3 (m.d 0 1) (by simp) with h14982 | h14982
                            · linarith only [h0, h14982, hlam]
                            · linarith only [h14801, h14982, hlam]
                          · have p14956_0 := h14956c.1
                            have p14956_1 := h14956c.2.1
                            have p14956_2 := h14956c.2.2.1
                            have p14956_3 := h14956c.2.2.2
                            linarith only [h14799, hlam, p14956_0]
                          · have p14956_0 := h14956c.1
                            have p14956_1 := h14956c.2.1
                            have p14956_2 := h14956c.2.2.1
                            have p14956_3 := h14956c.2.2.2
                            linarith only [h14943, hlam, p14956_1]
                          · have p14956_0 := h14956c.1
                            have p14956_1 := h14956c.2.1
                            have p14956_2 := h14956c.2.2.1
                            have p14956_3 := h14956c.2.2.2
                            linarith only [hlam, p14956_0]
                          · have p14956_0 := h14956c.1
                            have p14956_1 := h14956c.2.1
                            have p14956_2 := h14956c.2.2.1
                            have p14956_3 := h14956c.2.2.2
                            linarith only [h0, h14799, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p14956_1]
                          · have p14956_0 := h14956c.1
                            have p14956_1 := h14956c.2.1
                            have p14956_2 := h14956c.2.2.1
                            have p14956_3 := h14956c.2.2.2
                            linarith only [h0, h14799, h14948, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p14956_1]
                          · have p14956_0 := h14956c.1
                            have p14956_1 := h14956c.2.1
                            have p14956_2 := h14956c.2.2.1
                            have p14956_3 := h14956c.2.2.2
                            linarith only [h14800, hlam, p14956_0]
                          · have p14956_0 := h14956c.1
                            have p14956_1 := h14956c.2.1
                            have p14956_2 := h14956c.2.2.1
                            have p14956_3 := h14956c.2.2.2
                            linarith only [h14944, hlam, p14956_1]
                          · have p14956_0 := h14956c.1
                            have p14956_1 := h14956c.2.1
                            have p14956_2 := h14956c.2.2.1
                            have p14956_3 := h14956c.2.2.2
                            linarith only [h14946, hlam, p14956_0]
                          · have p14956_0 := h14956c.1
                            have p14956_1 := h14956c.2.1
                            have p14956_2 := h14956c.2.2.1
                            have p14956_3 := h14956c.2.2.2
                            linarith only [hlam, p14956_0]
                          · have p14956_0 := h14956c.1
                            have p14956_1 := h14956c.2.1
                            have p14956_2 := h14956c.2.2.1
                            have p14956_3 := h14956c.2.2.2
                            linarith only [h14948, hlam, p14956_1]
                          · have p14956_0 := h14956c.1
                            have p14956_1 := h14956c.2.1
                            have p14956_2 := h14956c.2.2.1
                            have p14956_3 := h14956c.2.2.2
                            linarith only [h14801, hlam, p14956_0]
                          · have p14956_0 := h14956c.1
                            have p14956_1 := h14956c.2.1
                            have p14956_2 := h14956c.2.2.1
                            have p14956_3 := h14956c.2.2.2
                            linarith only [h14945, hlam, p14956_1]
                          · have p14956_0 := h14956c.1
                            have p14956_1 := h14956c.2.1
                            have p14956_2 := h14956c.2.2.1
                            have p14956_3 := h14956c.2.2.2
                            linarith only [h14947, hlam, p14956_0]
                          · have p14956_0 := h14956c.1
                            have p14956_1 := h14956c.2.1
                            have p14956_2 := h14956c.2.2.1
                            have p14956_3 := h14956c.2.2.2
                            linarith only [h0, h14801, h14944, h14950, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14956_1]
                          · have p14956_0 := h14956c.1
                            have p14956_1 := h14956c.2.1
                            have p14956_2 := h14956c.2.2.1
                            have p14956_3 := h14956c.2.2.2
                            linarith only [hlam, p14956_0]
                    · linarith only [h0, h14799, h14947, h14951, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h14799, h14946, h14950, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h14799, h14806, h14946, h14947, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h15003 | h15003
              · linarith only [h0, h14799, h14805, h14946, h15003, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15005 | h15005
                · linarith only [h0, h14800, h14807, h15005, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15007 | h15007
                  · linarith only [h14943, h14946, h15007, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15009 | h15009
                    · linarith only [h0, h14799, h14805, h14943, h14946, h15003, h15005, h15009, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h15011 | h15011
                      · linarith only [h14803, h14807, h15011, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h15013 | h15013
                        · linarith only [h0, h14799, h14805, h14806, h14807, h14943, h15003, h15013, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases h1bigk with h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c
                          · have p15015_0 := h15015c.1
                            have p15015_1 := h15015c.2.1
                            have p15015_2 := h15015c.2.2.1
                            have p15015_3 := h15015c.2.2.2
                            linarith only [hlam, p15015_0]
                          · have p15015_0 := h15015c.1
                            have p15015_1 := h15015c.2.1
                            have p15015_2 := h15015c.2.2.1
                            have p15015_3 := h15015c.2.2.2
                            linarith only [h0, hlam, p15015_0]
                          · have p15015_0 := h15015c.1
                            have p15015_1 := h15015c.2.1
                            have p15015_2 := h15015c.2.2.1
                            have p15015_3 := h15015c.2.2.2
                            rcases p15015_3 (m.d 0 1) (by simp) with h15018 | h15018
                            · rcases p15015_3 (m.d 1 2) (by simp) with h15019 | h15019
                              · rcases p15015_3 (m.d 1 3) (by simp) with h15020 | h15020
                                · linarith only [h15020, hlam, p15015_0]
                                · rcases p15015_3 (m.d 1 4) (by simp) with h15022 | h15022
                                  · linarith only [h14800, h15022, hlam]
                                  · linarith only [h14946, h15022, hlam]
                              · linarith only [h14943, h15019, hlam]
                            · linarith only [h15018, hlam, p15015_0]
                          · have p15015_0 := h15015c.1
                            have p15015_1 := h15015c.2.1
                            have p15015_2 := h15015c.2.2.1
                            have p15015_3 := h15015c.2.2.2
                            rcases p15015_3 (m.d 0 1) (by simp) with h15027 | h15027
                            · rcases p15015_3 (m.d 1 2) (by simp) with h15028 | h15028
                              · rcases p15015_3 (m.d 1 3) (by simp) with h15029 | h15029
                                · linarith only [h14799, h15029, hlam]
                                · rcases p15015_3 (m.d 1 4) (by simp) with h15031 | h15031
                                  · linarith only [h15031, hlam, p15015_0]
                                  · rcases p15015_3 (m.d 1 5) (by simp) with h15033 | h15033
                                    · linarith only [h14801, h15033, hlam]
                                    · linarith only [h15005, h15033, hlam]
                              · linarith only [h14944, h15028, hlam]
                            · linarith only [h15027, hlam, p15015_0]
                          · have p15015_0 := h15015c.1
                            have p15015_1 := h15015c.2.1
                            have p15015_2 := h15015c.2.2.1
                            have p15015_3 := h15015c.2.2.2
                            rcases p15015_3 (m.d 0 1) (by simp) with h15038 | h15038
                            · rcases p15015_3 (m.d 1 2) (by simp) with h15039 | h15039
                              · rcases p15015_3 (m.d 1 3) (by simp) with h15040 | h15040
                                · linarith only [h14799, h15040, hlam]
                                · rcases p15015_3 (m.d 1 4) (by simp) with h15042 | h15042
                                  · linarith only [h14800, h15042, hlam]
                                  · rcases p15015_3 (m.d 1 5) (by simp) with h15044 | h15044
                                    · linarith only [h15044, hlam, p15015_0]
                                    · rcases h3bigk with h15046c | h15046c | h15046c | h15046c | h15046c | h15046c | h15046c | h15046c | h15046c | h15046c | h15046c | h15046c | h15046c | h15046c | h15046c | h15046c | h15046c | h15046c | h15046c | h15046c | h15046c | h15046c | h15046c | h15046c | h15046c
                                      · have p15046_0 := h15046c.1
                                        have p15046_1 := h15046c.2.1
                                        have p15046_2 := h15046c.2.2.1
                                        have p15046_3 := h15046c.2.2.2
                                        linarith only [hlam, p15046_0]
                                      · have p15046_0 := h15046c.1
                                        have p15046_1 := h15046c.2.1
                                        have p15046_2 := h15046c.2.2.1
                                        have p15046_3 := h15046c.2.2.2
                                        rcases p15046_3 (m.d 0 3) (by simp) with h15048 | h15048
                                        · rcases p15046_3 (m.d 1 3) (by simp) with h15049 | h15049
                                          · linarith only [h14799, h15049, hlam]
                                          · rcases p15046_3 (m.d 2 3) (by simp) with h15051 | h15051
                                            · linarith only [h14802, h15051, hlam]
                                            · rcases p15046_3 (m.d 3 4) (by simp) with h15053 | h15053
                                              · linarith only [h14805, h15053, hlam]
                                              · linarith only [h14946, h15053, hlam]
                                        · linarith only [h14799, h15048, hlam]
                                      · have p15046_0 := h15046c.1
                                        have p15046_1 := h15046c.2.1
                                        have p15046_2 := h15046c.2.2.1
                                        have p15046_3 := h15046c.2.2.2
                                        rcases p15046_3 (m.d 0 3) (by simp) with h15057 | h15057
                                        · rcases p15046_3 (m.d 1 3) (by simp) with h15058 | h15058
                                          · linarith only [h14799, h15058, hlam]
                                          · linarith only [h14943, h15058, hlam]
                                        · linarith only [h14802, h15057, hlam]
                                      · have p15046_0 := h15046c.1
                                        have p15046_1 := h15046c.2.1
                                        have p15046_2 := h15046c.2.2.1
                                        have p15046_3 := h15046c.2.2.2
                                        linarith only [h0, h14799, h14943, h14946, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15046_1]
                                      · have p15046_0 := h15046c.1
                                        have p15046_1 := h15046c.2.1
                                        have p15046_2 := h15046c.2.2.1
                                        have p15046_3 := h15046c.2.2.2
                                        linarith only [h0, h14799, h14943, h15003, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15046_1]
                                      · have p15046_0 := h15046c.1
                                        have p15046_1 := h15046c.2.1
                                        have p15046_2 := h15046c.2.2.1
                                        have p15046_3 := h15046c.2.2.2
                                        linarith only [h14799, hlam, p15046_0]
                                      · have p15046_0 := h15046c.1
                                        have p15046_1 := h15046c.2.1
                                        have p15046_2 := h15046c.2.2.1
                                        have p15046_3 := h15046c.2.2.2
                                        linarith only [hlam, p15046_0]
                                      · have p15046_0 := h15046c.1
                                        have p15046_1 := h15046c.2.1
                                        have p15046_2 := h15046c.2.2.1
                                        have p15046_3 := h15046c.2.2.2
                                        linarith only [h14946, hc23, hc34, hlam, hphi, p15046_1]
                                      · have p15046_0 := h15046c.1
                                        have p15046_1 := h15046c.2.1
                                        have p15046_2 := h15046c.2.2.1
                                        have p15046_3 := h15046c.2.2.2
                                        linarith only [h14946, hlam, p15046_0]
                                      · have p15046_0 := h15046c.1
                                        have p15046_1 := h15046c.2.1
                                        have p15046_2 := h15046c.2.2.1
                                        have p15046_3 := h15046c.2.2.2
                                        linarith only [h15003, hlam, p15046_0]
                                      · have p15046_0 := h15046c.1
                                        have p15046_1 := h15046c.2.1
                                        have p15046_2 := h15046c.2.2.1
                                        have p15046_3 := h15046c.2.2.2
                                        linarith only [h14802, hlam, p15046_0]
                                      · have p15046_0 := h15046c.1
                                        have p15046_1 := h15046c.2.1
                                        have p15046_2 := h15046c.2.2.1
                                        have p15046_3 := h15046c.2.2.2
                                        linarith only [h14943, hlam, p15046_0]
                                      · have p15046_0 := h15046c.1
                                        have p15046_1 := h15046c.2.1
                                        have p15046_2 := h15046c.2.2.1
                                        have p15046_3 := h15046c.2.2.2
                                        linarith only [hlam, p15046_0]
                                      · have p15046_0 := h15046c.1
                                        have p15046_1 := h15046c.2.1
                                        have p15046_2 := h15046c.2.2.1
                                        have p15046_3 := h15046c.2.2.2
                                        linarith only [h15007, hlam, p15046_0]
                                      · have p15046_0 := h15046c.1
                                        have p15046_1 := h15046c.2.1
                                        have p15046_2 := h15046c.2.2.1
                                        have p15046_3 := h15046c.2.2.2
                                        linarith only [h15009, hlam, p15046_0]
                                      · have p15046_0 := h15046c.1
                                        have p15046_1 := h15046c.2.1
                                        have p15046_2 := h15046c.2.2.1
                                        have p15046_3 := h15046c.2.2.2
                                        linarith only [h14805, hlam, p15046_0]
                                      · have p15046_0 := h15046c.1
                                        have p15046_1 := h15046c.2.1
                                        have p15046_2 := h15046c.2.2.1
                                        have p15046_3 := h15046c.2.2.2
                                        linarith only [h0, h14799, h14805, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15046_1]
                                      · have p15046_0 := h15046c.1
                                        have p15046_1 := h15046c.2.1
                                        have p15046_2 := h15046c.2.2.1
                                        have p15046_3 := h15046c.2.2.2
                                        linarith only [h0, h14799, h14805, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15046_1]
                                      · have p15046_0 := h15046c.1
                                        have p15046_1 := h15046c.2.1
                                        have p15046_2 := h15046c.2.2.1
                                        have p15046_3 := h15046c.2.2.2
                                        linarith only [hlam, p15046_0]
                                      · have p15046_0 := h15046c.1
                                        have p15046_1 := h15046c.2.1
                                        have p15046_2 := h15046c.2.2.1
                                        have p15046_3 := h15046c.2.2.2
                                        linarith only [h15013, hlam, p15046_1]
                                      · have p15046_0 := h15046c.1
                                        have p15046_1 := h15046c.2.1
                                        have p15046_2 := h15046c.2.2.1
                                        have p15046_3 := h15046c.2.2.2
                                        linarith only [h14806, hlam, p15046_0]
                                      · have p15046_0 := h15046c.1
                                        have p15046_1 := h15046c.2.1
                                        have p15046_2 := h15046c.2.2.1
                                        have p15046_3 := h15046c.2.2.2
                                        linarith only [h0, h14799, h14806, h14943, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15046_1]
                                      · have p15046_0 := h15046c.1
                                        have p15046_1 := h15046c.2.1
                                        have p15046_2 := h15046c.2.2.1
                                        have p15046_3 := h15046c.2.2.2
                                        linarith only [h0, h14799, h14806, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15046_1]
                                      · have p15046_0 := h15046c.1
                                        have p15046_1 := h15046c.2.1
                                        have p15046_2 := h15046c.2.2.1
                                        have p15046_3 := h15046c.2.2.2
                                        linarith only [h0, h14799, h14806, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15046_1]
                                      · have p15046_0 := h15046c.1
                                        have p15046_1 := h15046c.2.1
                                        have p15046_2 := h15046c.2.2.1
                                        have p15046_3 := h15046c.2.2.2
                                        linarith only [hlam, p15046_0]
                              · linarith only [h14945, h15039, hlam]
                            · linarith only [h15038, hlam, p15015_0]
                          · have p15015_0 := h15015c.1
                            have p15015_1 := h15015c.2.1
                            have p15015_2 := h15015c.2.2.1
                            have p15015_3 := h15015c.2.2.2
                            linarith only [h14799, h14805, h14943, h14946, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15015_1]
                          · have p15015_0 := h15015c.1
                            have p15015_1 := h15015c.2.1
                            have p15015_2 := h15015c.2.2.1
                            have p15015_3 := h15015c.2.2.2
                            linarith only [hlam, p15015_0]
                          · have p15015_0 := h15015c.1
                            have p15015_1 := h15015c.2.1
                            have p15015_2 := h15015c.2.2.1
                            have p15015_3 := h15015c.2.2.2
                            linarith only [h0, h14799, h14805, h14946, hlam, p15015_2]
                          · have p15015_0 := h15015c.1
                            have p15015_1 := h15015c.2.1
                            have p15015_2 := h15015c.2.2.1
                            have p15015_3 := h15015c.2.2.2
                            rcases p15015_3 (m.d 0 1) (by simp) with h15089 | h15089
                            · linarith only [h0, h15089, hlam]
                            · linarith only [h14800, h15089, hlam]
                          · have p15015_0 := h15015c.1
                            have p15015_1 := h15015c.2.1
                            have p15015_2 := h15015c.2.2.1
                            have p15015_3 := h15015c.2.2.2
                            rcases p15015_3 (m.d 0 1) (by simp) with h15092 | h15092
                            · linarith only [h0, h15092, hlam]
                            · linarith only [h14801, h15092, hlam]
                          · have p15015_0 := h15015c.1
                            have p15015_1 := h15015c.2.1
                            have p15015_2 := h15015c.2.2.1
                            have p15015_3 := h15015c.2.2.2
                            linarith only [h14799, hlam, p15015_0]
                          · have p15015_0 := h15015c.1
                            have p15015_1 := h15015c.2.1
                            have p15015_2 := h15015c.2.2.1
                            have p15015_3 := h15015c.2.2.2
                            linarith only [h14943, hlam, p15015_1]
                          · have p15015_0 := h15015c.1
                            have p15015_1 := h15015c.2.1
                            have p15015_2 := h15015c.2.2.1
                            have p15015_3 := h15015c.2.2.2
                            linarith only [hlam, p15015_0]
                          · have p15015_0 := h15015c.1
                            have p15015_1 := h15015c.2.1
                            have p15015_2 := h15015c.2.2.1
                            have p15015_3 := h15015c.2.2.2
                            linarith only [h14946, hlam, p15015_1]
                          · have p15015_0 := h15015c.1
                            have p15015_1 := h15015c.2.1
                            have p15015_2 := h15015c.2.2.1
                            have p15015_3 := h15015c.2.2.2
                            linarith only [h15003, hlam, p15015_1]
                          · have p15015_0 := h15015c.1
                            have p15015_1 := h15015c.2.1
                            have p15015_2 := h15015c.2.2.1
                            have p15015_3 := h15015c.2.2.2
                            linarith only [h14800, hlam, p15015_0]
                          · have p15015_0 := h15015c.1
                            have p15015_1 := h15015c.2.1
                            have p15015_2 := h15015c.2.2.1
                            have p15015_3 := h15015c.2.2.2
                            linarith only [h14944, hlam, p15015_1]
                          · have p15015_0 := h15015c.1
                            have p15015_1 := h15015c.2.1
                            have p15015_2 := h15015c.2.2.1
                            have p15015_3 := h15015c.2.2.2
                            linarith only [h0, h14800, h14943, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15015_1]
                          · have p15015_0 := h15015c.1
                            have p15015_1 := h15015c.2.1
                            have p15015_2 := h15015c.2.2.1
                            have p15015_3 := h15015c.2.2.2
                            linarith only [hlam, p15015_0]
                          · have p15015_0 := h15015c.1
                            have p15015_1 := h15015c.2.1
                            have p15015_2 := h15015c.2.2.1
                            have p15015_3 := h15015c.2.2.2
                            linarith only [h15005, hlam, p15015_1]
                          · have p15015_0 := h15015c.1
                            have p15015_1 := h15015c.2.1
                            have p15015_2 := h15015c.2.2.1
                            have p15015_3 := h15015c.2.2.2
                            linarith only [h14801, hlam, p15015_0]
                          · have p15015_0 := h15015c.1
                            have p15015_1 := h15015c.2.1
                            have p15015_2 := h15015c.2.2.1
                            have p15015_3 := h15015c.2.2.2
                            linarith only [h14945, hlam, p15015_1]
                          · have p15015_0 := h15015c.1
                            have p15015_1 := h15015c.2.1
                            have p15015_2 := h15015c.2.2.1
                            have p15015_3 := h15015c.2.2.2
                            linarith only [h0, h14799, h14806, h14943, h15003, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15015_1]
                          · have p15015_0 := h15015c.1
                            have p15015_1 := h15015c.2.1
                            have p15015_2 := h15015c.2.2.1
                            have p15015_3 := h15015c.2.2.2
                            linarith only [h0, h14799, h14806, h15003, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p15015_1]
                          · have p15015_0 := h15015c.1
                            have p15015_1 := h15015c.2.1
                            have p15015_2 := h15015c.2.2.1
                            have p15015_3 := h15015c.2.2.2
                            linarith only [hlam, p15015_0]
          · linarith only [h0, h14804, h14945, hlam]
        · linarith only [h0, h14803, h14944, hlam]
      · linarith only [h0, h14802, h14943, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h15113 | h15113
    · linarith only [h14805, h14806, h15113, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h15115 | h15115
      · rcases m.htr 1 2 4 (by decide) (by decide) with h15116 | h15116
        · rcases m.htr 1 2 5 (by decide) (by decide) with h15117 | h15117
          · rcases m.htr 1 3 4 (by decide) (by decide) with h15118 | h15118
            · rcases m.htr 1 3 5 (by decide) (by decide) with h15119 | h15119
              · linarith only [h14799, h14806, h15119, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15121 | h15121
                · linarith only [h14800, h15113, h15121, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15123 | h15123
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15124 | h15124
                    · linarith only [h14799, h14806, h15115, h15124, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h15126 | h15126
                      · linarith only [h14800, h15113, h15116, h15126, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h15128 | h15128
                        · linarith only [h14801, h15113, h15115, h15119, h15123, h15128, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h1bigk with h15130c | h15130c | h15130c | h15130c | h15130c | h15130c | h15130c | h15130c | h15130c | h15130c | h15130c | h15130c | h15130c | h15130c | h15130c | h15130c | h15130c | h15130c | h15130c | h15130c | h15130c | h15130c | h15130c | h15130c | h15130c
                          · have p15130_0 := h15130c.1
                            have p15130_1 := h15130c.2.1
                            have p15130_2 := h15130c.2.2.1
                            have p15130_3 := h15130c.2.2.2
                            linarith only [hlam, p15130_0]
                          · have p15130_0 := h15130c.1
                            have p15130_1 := h15130c.2.1
                            have p15130_2 := h15130c.2.2.1
                            have p15130_3 := h15130c.2.2.2
                            linarith only [h0, hlam, p15130_0]
                          · have p15130_0 := h15130c.1
                            have p15130_1 := h15130c.2.1
                            have p15130_2 := h15130c.2.2.1
                            have p15130_3 := h15130c.2.2.2
                            linarith only [h0, h15118, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15130_1]
                          · have p15130_0 := h15130c.1
                            have p15130_1 := h15130c.2.1
                            have p15130_2 := h15130c.2.2.1
                            have p15130_3 := h15130c.2.2.2
                            rcases p15130_3 (m.d 0 1) (by simp) with h15134 | h15134
                            · rcases p15130_3 (m.d 1 2) (by simp) with h15135 | h15135
                              · rcases p15130_3 (m.d 1 3) (by simp) with h15136 | h15136
                                · linarith only [h14799, h15136, hlam]
                                · linarith only [h15118, h15136, hlam]
                              · linarith only [h15116, h15135, hlam]
                            · linarith only [h15134, hlam, p15130_0]
                          · have p15130_0 := h15130c.1
                            have p15130_1 := h15130c.2.1
                            have p15130_2 := h15130c.2.2.1
                            have p15130_3 := h15130c.2.2.2
                            linarith only [h0, h15117, h15123, h15124, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15130_1]
                          · have p15130_0 := h15130c.1
                            have p15130_1 := h15130c.2.1
                            have p15130_2 := h15130c.2.2.1
                            have p15130_3 := h15130c.2.2.2
                            linarith only [h14799, h15115, h15123, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15130_1]
                          · have p15130_0 := h15130c.1
                            have p15130_1 := h15130c.2.1
                            have p15130_2 := h15130c.2.2.1
                            have p15130_3 := h15130c.2.2.2
                            linarith only [hlam, p15130_0]
                          · have p15130_0 := h15130c.1
                            have p15130_1 := h15130c.2.1
                            have p15130_2 := h15130c.2.2.1
                            have p15130_3 := h15130c.2.2.2
                            rcases p15130_3 (m.d 0 1) (by simp) with h15144 | h15144
                            · linarith only [h0, h15144, hlam]
                            · linarith only [h14799, h15144, hlam]
                          · have p15130_0 := h15130c.1
                            have p15130_1 := h15130c.2.1
                            have p15130_2 := h15130c.2.2.1
                            have p15130_3 := h15130c.2.2.2
                            rcases p15130_3 (m.d 0 1) (by simp) with h15147 | h15147
                            · linarith only [h0, h15147, hlam]
                            · linarith only [h14800, h15147, hlam]
                          · have p15130_0 := h15130c.1
                            have p15130_1 := h15130c.2.1
                            have p15130_2 := h15130c.2.2.1
                            have p15130_3 := h15130c.2.2.2
                            rcases p15130_3 (m.d 0 1) (by simp) with h15150 | h15150
                            · linarith only [h0, h15150, hlam]
                            · linarith only [h14801, h15150, hlam]
                          · have p15130_0 := h15130c.1
                            have p15130_1 := h15130c.2.1
                            have p15130_2 := h15130c.2.2.1
                            have p15130_3 := h15130c.2.2.2
                            linarith only [h14799, hlam, p15130_0]
                          · have p15130_0 := h15130c.1
                            have p15130_1 := h15130c.2.1
                            have p15130_2 := h15130c.2.2.1
                            have p15130_3 := h15130c.2.2.2
                            linarith only [h15115, hlam, p15130_1]
                          · have p15130_0 := h15130c.1
                            have p15130_1 := h15130c.2.1
                            have p15130_2 := h15130c.2.2.1
                            have p15130_3 := h15130c.2.2.2
                            linarith only [hlam, p15130_0]
                          · have p15130_0 := h15130c.1
                            have p15130_1 := h15130c.2.1
                            have p15130_2 := h15130c.2.2.1
                            have p15130_3 := h15130c.2.2.2
                            linarith only [h14799, h14806, h15128, hc14, hc45, hlam, hphi, p15130_1]
                          · have p15130_0 := h15130c.1
                            have p15130_1 := h15130c.2.1
                            have p15130_2 := h15130c.2.2.1
                            have p15130_3 := h15130c.2.2.2
                            linarith only [h15119, hlam, p15130_1]
                          · have p15130_0 := h15130c.1
                            have p15130_1 := h15130c.2.1
                            have p15130_2 := h15130c.2.2.1
                            have p15130_3 := h15130c.2.2.2
                            linarith only [h14800, hlam, p15130_0]
                          · have p15130_0 := h15130c.1
                            have p15130_1 := h15130c.2.1
                            have p15130_2 := h15130c.2.2.1
                            have p15130_3 := h15130c.2.2.2
                            linarith only [h15116, hlam, p15130_1]
                          · have p15130_0 := h15130c.1
                            have p15130_1 := h15130c.2.1
                            have p15130_2 := h15130c.2.2.1
                            have p15130_3 := h15130c.2.2.2
                            linarith only [h15118, hlam, p15130_0]
                          · have p15130_0 := h15130c.1
                            have p15130_1 := h15130c.2.1
                            have p15130_2 := h15130c.2.2.1
                            have p15130_3 := h15130c.2.2.2
                            linarith only [hlam, p15130_0]
                          · have p15130_0 := h15130c.1
                            have p15130_1 := h15130c.2.1
                            have p15130_2 := h15130c.2.2.1
                            have p15130_3 := h15130c.2.2.2
                            linarith only [h15121, hlam, p15130_1]
                          · have p15130_0 := h15130c.1
                            have p15130_1 := h15130c.2.1
                            have p15130_2 := h15130c.2.2.1
                            have p15130_3 := h15130c.2.2.2
                            linarith only [h14801, hlam, p15130_0]
                          · have p15130_0 := h15130c.1
                            have p15130_1 := h15130c.2.1
                            have p15130_2 := h15130c.2.2.1
                            have p15130_3 := h15130c.2.2.2
                            linarith only [h15117, hlam, p15130_1]
                          · have p15130_0 := h15130c.1
                            have p15130_1 := h15130c.2.1
                            have p15130_2 := h15130c.2.2.1
                            have p15130_3 := h15130c.2.2.2
                            linarith only [h0, h14801, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15130_1]
                          · have p15130_0 := h15130c.1
                            have p15130_1 := h15130c.2.1
                            have p15130_2 := h15130c.2.2.1
                            have p15130_3 := h15130c.2.2.2
                            linarith only [h0, h14801, h15116, h15123, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15130_1]
                          · have p15130_0 := h15130c.1
                            have p15130_1 := h15130c.2.1
                            have p15130_2 := h15130c.2.2.1
                            have p15130_3 := h15130c.2.2.2
                            linarith only [hlam, p15130_0]
                  · linarith only [h14805, h14806, h15123, hc23, hc35, hlam, hphi]
            · linarith only [h14805, h14806, h15118, hc13, hc35, hlam, hphi]
          · linarith only [h0, h14804, h15117, hlam]
        · linarith only [h0, h14803, h15116, hlam]
      · linarith only [h0, h14802, h15115, hlam]

end R2N4
