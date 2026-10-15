import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 19848000 in
set_option maxHeartbeats 19848000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s17_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h18815 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18816 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18817 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h18818 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h18819 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  rcases m.htr 0 3 5 (by decide) (by decide) with h18820 | h18820
  · rcases m.htr 0 4 5 (by decide) (by decide) with h18821 | h18821
    · rcases m.htr 1 2 3 (by decide) (by decide) with h18822 | h18822
      · rcases m.htr 1 2 4 (by decide) (by decide) with h18823 | h18823
        · rcases m.htr 1 2 5 (by decide) (by decide) with h18824 | h18824
          · rcases m.htr 1 3 4 (by decide) (by decide) with h18825 | h18825
            · rcases m.htr 1 3 5 (by decide) (by decide) with h18826 | h18826
              · rcases m.htr 1 4 5 (by decide) (by decide) with h18827 | h18827
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18828 | h18828
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h18829 | h18829
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h18830 | h18830
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h18831 | h18831
                        · rcases h0bigk with h18832c | h18832c | h18832c | h18832c | h18832c | h18832c | h18832c | h18832c | h18832c | h18832c | h18832c | h18832c | h18832c | h18832c | h18832c | h18832c | h18832c | h18832c | h18832c | h18832c | h18832c | h18832c | h18832c | h18832c | h18832c
                          · have p18832_0 := h18832c.1
                            have p18832_1 := h18832c.2.1
                            have p18832_2 := h18832c.2.2.1
                            have p18832_3 := h18832c.2.2.2
                            linarith only [hlam, p18832_0]
                          · have p18832_0 := h18832c.1
                            have p18832_1 := h18832c.2.1
                            have p18832_2 := h18832c.2.2.1
                            have p18832_3 := h18832c.2.2.2
                            linarith only [h0, hlam, p18832_1]
                          · have p18832_0 := h18832c.1
                            have p18832_1 := h18832c.2.1
                            have p18832_2 := h18832c.2.2.1
                            have p18832_3 := h18832c.2.2.2
                            linarith only [h14396, hlam, p18832_0]
                          · have p18832_0 := h18832c.1
                            have p18832_1 := h18832c.2.1
                            have p18832_2 := h18832c.2.2.1
                            have p18832_3 := h18832c.2.2.2
                            linarith only [h16915, hlam, p18832_1]
                          · have p18832_0 := h18832c.1
                            have p18832_1 := h18832c.2.1
                            have p18832_2 := h18832c.2.2.1
                            have p18832_3 := h18832c.2.2.2
                            rcases p18832_3 (m.d 0 1) (by simp) with h18837 | h18837
                            · rcases p18832_3 (m.d 0 2) (by simp) with h18838 | h18838
                              · rcases p18832_3 (m.d 0 3) (by simp) with h18839 | h18839
                                · rcases p18832_3 (m.d 0 4) (by simp) with h18840 | h18840
                                  · rcases p18832_3 (m.d 0 5) (by simp) with h18841 | h18841
                                    · linarith only [h18815, h18841, hlam]
                                    · rcases h2bigk with h18843c | h18843c | h18843c | h18843c | h18843c | h18843c | h18843c | h18843c | h18843c | h18843c | h18843c | h18843c | h18843c | h18843c | h18843c | h18843c | h18843c | h18843c | h18843c | h18843c | h18843c | h18843c | h18843c | h18843c | h18843c
                                      · have p18843_0 := h18843c.1
                                        have p18843_1 := h18843c.2.1
                                        have p18843_2 := h18843c.2.2.1
                                        have p18843_3 := h18843c.2.2.2
                                        linarith only [hlam, p18843_0]
                                      · have p18843_0 := h18843c.1
                                        have p18843_1 := h18843c.2.1
                                        have p18843_2 := h18843c.2.2.1
                                        have p18843_3 := h18843c.2.2.2
                                        linarith only [h0, hlam, p18843_1]
                                      · have p18843_0 := h18843c.1
                                        have p18843_1 := h18843c.2.1
                                        have p18843_2 := h18843c.2.2.1
                                        have p18843_3 := h18843c.2.2.2
                                        linarith only [h0, h18828, h18831, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18843_1]
                                      · have p18843_0 := h18843c.1
                                        have p18843_1 := h18843c.2.1
                                        have p18843_2 := h18843c.2.2.1
                                        have p18843_3 := h18843c.2.2.2
                                        rcases p18843_3 (m.d 0 2) (by simp) with h18847 | h18847
                                        · rcases p18843_3 (m.d 1 2) (by simp) with h18848 | h18848
                                          · rcases p18843_3 (m.d 2 3) (by simp) with h18849 | h18849
                                            · linarith only [h18816, h18849, hlam]
                                            · linarith only [h18828, h18849, hlam]
                                          · linarith only [h18823, h18848, hlam]
                                        · linarith only [h18847, hlam, p18843_0]
                                      · have p18843_0 := h18843c.1
                                        have p18843_1 := h18843c.2.1
                                        have p18843_2 := h18843c.2.2.1
                                        have p18843_3 := h18843c.2.2.2
                                        rcases p18843_3 (m.d 0 2) (by simp) with h18854 | h18854
                                        · rcases p18843_3 (m.d 1 2) (by simp) with h18855 | h18855
                                          · rcases p18843_3 (m.d 2 3) (by simp) with h18856 | h18856
                                            · linarith only [h18816, h18856, hlam]
                                            · linarith only [h18829, h18856, hlam]
                                          · linarith only [h18824, h18855, hlam]
                                        · linarith only [h18854, hlam, p18843_0]
                                      · have p18843_0 := h18843c.1
                                        have p18843_1 := h18843c.2.1
                                        have p18843_2 := h18843c.2.2.1
                                        have p18843_3 := h18843c.2.2.2
                                        linarith only [h0, h18815, h18824, h18829, h18831, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18832_1, p18843_1]
                                      · have p18843_0 := h18843c.1
                                        have p18843_1 := h18843c.2.1
                                        have p18843_2 := h18843c.2.2.1
                                        have p18843_3 := h18843c.2.2.2
                                        linarith only [hlam, p18843_0]
                                      · have p18843_0 := h18843c.1
                                        have p18843_1 := h18843c.2.1
                                        have p18843_2 := h18843c.2.2.1
                                        have p18843_3 := h18843c.2.2.2
                                        linarith only [h18828, h18831, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18843_1]
                                      · have p18843_0 := h18843c.1
                                        have p18843_1 := h18843c.2.1
                                        have p18843_2 := h18843c.2.2.1
                                        have p18843_3 := h18843c.2.2.2
                                        rcases p18843_3 (m.d 0 2) (by simp) with h18864 | h18864
                                        · linarith only [h0, h18864, hlam]
                                        · linarith only [h18817, h18864, hlam]
                                      · have p18843_0 := h18843c.1
                                        have p18843_1 := h18843c.2.1
                                        have p18843_2 := h18843c.2.2.1
                                        have p18843_3 := h18843c.2.2.2
                                        linarith only [h16915, h18815, h18822, h18824, h18825, hlam, p18832_1, p18843_2]
                                      · have p18843_0 := h18843c.1
                                        have p18843_1 := h18843c.2.1
                                        have p18843_2 := h18843c.2.2.1
                                        have p18843_3 := h18843c.2.2.2
                                        linarith only [h18816, hlam, p18843_0]
                                      · have p18843_0 := h18843c.1
                                        have p18843_1 := h18843c.2.1
                                        have p18843_2 := h18843c.2.2.1
                                        have p18843_3 := h18843c.2.2.2
                                        linarith only [h18822, hlam, p18843_0]
                                      · have p18843_0 := h18843c.1
                                        have p18843_1 := h18843c.2.1
                                        have p18843_2 := h18843c.2.2.1
                                        have p18843_3 := h18843c.2.2.2
                                        linarith only [hlam, p18843_0]
                                      · have p18843_0 := h18843c.1
                                        have p18843_1 := h18843c.2.1
                                        have p18843_2 := h18843c.2.2.1
                                        have p18843_3 := h18843c.2.2.2
                                        linarith only [h18816, h18828, h18831, hc02, hc45, hlam, hphi, ht0b, ht5b, p18843_1]
                                      · have p18843_0 := h18843c.1
                                        have p18843_1 := h18843c.2.1
                                        have p18843_2 := h18843c.2.2.1
                                        have p18843_3 := h18843c.2.2.2
                                        rcases p18843_3 (m.d 0 2) (by simp) with h18872 | h18872
                                        · rcases p18843_3 (m.d 1 2) (by simp) with h18873 | h18873
                                          · rcases p18843_3 (m.d 2 3) (by simp) with h18874 | h18874
                                            · rcases p18843_3 (m.d 2 4) (by simp) with h18875 | h18875
                                              · linarith only [h18828, h18875, hlam]
                                              · linarith only [h18830, h18875, hlam]
                                            · linarith only [h18829, h18874, hlam]
                                          · linarith only [h18824, h18873, hlam]
                                        · linarith only [h18818, h18872, hlam]
                                      · have p18843_0 := h18843c.1
                                        have p18843_1 := h18843c.2.1
                                        have p18843_2 := h18843c.2.2.1
                                        have p18843_3 := h18843c.2.2.2
                                        linarith only [h18817, hlam, p18843_0]
                                      · have p18843_0 := h18843c.1
                                        have p18843_1 := h18843c.2.1
                                        have p18843_2 := h18843c.2.2.1
                                        have p18843_3 := h18843c.2.2.2
                                        linarith only [h18823, hlam, p18843_0]
                                      · have p18843_0 := h18843c.1
                                        have p18843_1 := h18843c.2.1
                                        have p18843_2 := h18843c.2.2.1
                                        have p18843_3 := h18843c.2.2.2
                                        linarith only [h18828, hlam, p18843_1]
                                      · have p18843_0 := h18843c.1
                                        have p18843_1 := h18843c.2.1
                                        have p18843_2 := h18843c.2.2.1
                                        have p18843_3 := h18843c.2.2.2
                                        linarith only [hlam, p18843_0]
                                      · have p18843_0 := h18843c.1
                                        have p18843_1 := h18843c.2.1
                                        have p18843_2 := h18843c.2.2.1
                                        have p18843_3 := h18843c.2.2.2
                                        rcases p18843_3 (m.d 0 2) (by simp) with h18885 | h18885
                                        · rcases p18843_3 (m.d 1 2) (by simp) with h18886 | h18886
                                          · rcases p18843_3 (m.d 2 3) (by simp) with h18887 | h18887
                                            · rcases p18843_3 (m.d 2 4) (by simp) with h18888 | h18888
                                              · rcases p18843_3 (m.d 2 5) (by simp) with h18889 | h18889
                                                · linarith only [h18830, h18889, hlam]
                                                · rcases h3bigk with h18891c | h18891c | h18891c | h18891c | h18891c | h18891c | h18891c | h18891c | h18891c | h18891c | h18891c | h18891c | h18891c | h18891c | h18891c | h18891c | h18891c | h18891c | h18891c | h18891c | h18891c | h18891c | h18891c | h18891c | h18891c
                                                  · have p18891_0 := h18891c.1
                                                    have p18891_1 := h18891c.2.1
                                                    have p18891_2 := h18891c.2.2.1
                                                    have p18891_3 := h18891c.2.2.2
                                                    linarith only [hlam, p18891_0]
                                                  · have p18891_0 := h18891c.1
                                                    have p18891_1 := h18891c.2.1
                                                    have p18891_2 := h18891c.2.2.1
                                                    have p18891_3 := h18891c.2.2.2
                                                    linarith only [h14396, hlam, p18891_1]
                                                  · have p18891_0 := h18891c.1
                                                    have p18891_1 := h18891c.2.1
                                                    have p18891_2 := h18891c.2.2.1
                                                    have p18891_3 := h18891c.2.2.2
                                                    linarith only [h0, h18816, h18828, h18831, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18891_1]
                                                  · have p18891_0 := h18891c.1
                                                    have p18891_1 := h18891c.2.1
                                                    have p18891_2 := h18891c.2.2.1
                                                    have p18891_3 := h18891c.2.2.2
                                                    linarith only [h0, h18816, h18831, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18891_1]
                                                  · have p18891_0 := h18891c.1
                                                    have p18891_1 := h18891c.2.1
                                                    have p18891_2 := h18891c.2.2.1
                                                    have p18891_3 := h18891c.2.2.2
                                                    rcases p18891_3 (m.d 0 3) (by simp) with h18896 | h18896
                                                    · rcases p18891_3 (m.d 1 3) (by simp) with h18897 | h18897
                                                      · rcases p18891_3 (m.d 2 3) (by simp) with h18898 | h18898
                                                        · linarith only [h18816, h18898, hlam]
                                                        · linarith only [h18829, h18898, hlam]
                                                      · linarith only [h18826, h18897, hlam]
                                                    · linarith only [h18896, hlam, p18891_0]
                                                  · have p18891_0 := h18891c.1
                                                    have p18891_1 := h18891c.2.1
                                                    have p18891_2 := h18891c.2.2.1
                                                    have p18891_3 := h18891c.2.2.2
                                                    linarith only [h14396, h18815, h18822, h18824, h18829, h18831, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18832_1, p18891_1]
                                                  · have p18891_0 := h18891c.1
                                                    have p18891_1 := h18891c.2.1
                                                    have p18891_2 := h18891c.2.2.1
                                                    have p18891_3 := h18891c.2.2.2
                                                    linarith only [hlam, p18891_0]
                                                  · have p18891_0 := h18891c.1
                                                    have p18891_1 := h18891c.2.1
                                                    have p18891_2 := h18891c.2.2.1
                                                    have p18891_3 := h18891c.2.2.2
                                                    linarith only [h18822, h18828, h18829, h18831, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18843_1, p18891_1]
                                                  · have p18891_0 := h18891c.1
                                                    have p18891_1 := h18891c.2.1
                                                    have p18891_2 := h18891c.2.2.1
                                                    have p18891_3 := h18891c.2.2.2
                                                    linarith only [h18822, h18831, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18891_1]
                                                  · have p18891_0 := h18891c.1
                                                    have p18891_1 := h18891c.2.1
                                                    have p18891_2 := h18891c.2.2.1
                                                    have p18891_3 := h18891c.2.2.2
                                                    rcases p18891_3 (m.d 0 3) (by simp) with h18907 | h18907
                                                    · linarith only [h14396, h18907, hlam]
                                                    · linarith only [h18820, h18907, hlam]
                                                  · have p18891_0 := h18891c.1
                                                    have p18891_1 := h18891c.2.1
                                                    have p18891_2 := h18891c.2.2.1
                                                    have p18891_3 := h18891c.2.2.2
                                                    linarith only [h18816, hlam, p18891_0]
                                                  · have p18891_0 := h18891c.1
                                                    have p18891_1 := h18891c.2.1
                                                    have p18891_2 := h18891c.2.2.1
                                                    have p18891_3 := h18891c.2.2.2
                                                    linarith only [h18822, hlam, p18891_0]
                                                  · have p18891_0 := h18891c.1
                                                    have p18891_1 := h18891c.2.1
                                                    have p18891_2 := h18891c.2.2.1
                                                    have p18891_3 := h18891c.2.2.2
                                                    linarith only [hlam, p18891_0]
                                                  · have p18891_0 := h18891c.1
                                                    have p18891_1 := h18891c.2.1
                                                    have p18891_2 := h18891c.2.2.1
                                                    have p18891_3 := h18891c.2.2.2
                                                    linarith only [h18831, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p18891_1]
                                                  · have p18891_0 := h18891c.1
                                                    have p18891_1 := h18891c.2.1
                                                    have p18891_2 := h18891c.2.2.1
                                                    have p18891_3 := h18891c.2.2.2
                                                    linarith only [h0, h18816, h18831, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18891_1]
                                                  · have p18891_0 := h18891c.1
                                                    have p18891_1 := h18891c.2.1
                                                    have p18891_2 := h18891c.2.2.1
                                                    have p18891_3 := h18891c.2.2.2
                                                    linarith only [h18819, hlam, p18891_0]
                                                  · have p18891_0 := h18891c.1
                                                    have p18891_1 := h18891c.2.1
                                                    have p18891_2 := h18891c.2.2.1
                                                    have p18891_3 := h18891c.2.2.2
                                                    linarith only [h18825, hlam, p18891_0]
                                                  · have p18891_0 := h18891c.1
                                                    have p18891_1 := h18891c.2.1
                                                    have p18891_2 := h18891c.2.2.1
                                                    have p18891_3 := h18891c.2.2.2
                                                    linarith only [h18828, hlam, p18891_0]
                                                  · have p18891_0 := h18891c.1
                                                    have p18891_1 := h18891c.2.1
                                                    have p18891_2 := h18891c.2.2.1
                                                    have p18891_3 := h18891c.2.2.2
                                                    linarith only [hlam, p18891_0]
                                                  · have p18891_0 := h18891c.1
                                                    have p18891_1 := h18891c.2.1
                                                    have p18891_2 := h18891c.2.2.1
                                                    have p18891_3 := h18891c.2.2.2
                                                    linarith only [h18819, h18831, hc03, hc45, hlam, hphi, ht0b, ht5b, p18891_1]
                                                  · have p18891_0 := h18891c.1
                                                    have p18891_1 := h18891c.2.1
                                                    have p18891_2 := h18891c.2.2.1
                                                    have p18891_3 := h18891c.2.2.2
                                                    linarith only [h18820, hlam, p18891_0]
                                                  · have p18891_0 := h18891c.1
                                                    have p18891_1 := h18891c.2.1
                                                    have p18891_2 := h18891c.2.2.1
                                                    have p18891_3 := h18891c.2.2.2
                                                    linarith only [h18826, hlam, p18891_0]
                                                  · have p18891_0 := h18891c.1
                                                    have p18891_1 := h18891c.2.1
                                                    have p18891_2 := h18891c.2.2.1
                                                    have p18891_3 := h18891c.2.2.2
                                                    linarith only [h18829, hlam, p18891_0]
                                                  · have p18891_0 := h18891c.1
                                                    have p18891_1 := h18891c.2.1
                                                    have p18891_2 := h18891c.2.2.1
                                                    have p18891_3 := h18891c.2.2.2
                                                    linarith only [h18831, hlam, p18891_0]
                                                  · have p18891_0 := h18891c.1
                                                    have p18891_1 := h18891c.2.1
                                                    have p18891_2 := h18891c.2.2.1
                                                    have p18891_3 := h18891c.2.2.2
                                                    linarith only [hlam, p18891_0]
                                              · linarith only [h18830, h18888, hlam]
                                            · linarith only [h18829, h18887, hlam]
                                          · linarith only [h18824, h18886, hlam]
                                        · linarith only [h18818, h18885, hlam]
                                      · have p18843_0 := h18843c.1
                                        have p18843_1 := h18843c.2.1
                                        have p18843_2 := h18843c.2.2.1
                                        have p18843_3 := h18843c.2.2.2
                                        linarith only [h18818, hlam, p18843_0]
                                      · have p18843_0 := h18843c.1
                                        have p18843_1 := h18843c.2.1
                                        have p18843_2 := h18843c.2.2.1
                                        have p18843_3 := h18843c.2.2.2
                                        linarith only [h18824, hlam, p18843_0]
                                      · have p18843_0 := h18843c.1
                                        have p18843_1 := h18843c.2.1
                                        have p18843_2 := h18843c.2.2.1
                                        have p18843_3 := h18843c.2.2.2
                                        linarith only [h18829, hlam, p18843_1]
                                      · have p18843_0 := h18843c.1
                                        have p18843_1 := h18843c.2.1
                                        have p18843_2 := h18843c.2.2.1
                                        have p18843_3 := h18843c.2.2.2
                                        linarith only [h18830, hlam, p18843_0]
                                      · have p18843_0 := h18843c.1
                                        have p18843_1 := h18843c.2.1
                                        have p18843_2 := h18843c.2.2.1
                                        have p18843_3 := h18843c.2.2.2
                                        linarith only [hlam, p18843_0]
                                  · linarith only [h18821, h18840, hlam]
                                · linarith only [h18820, h18839, hlam]
                              · linarith only [h18818, h18838, hlam]
                            · linarith only [h18815, h18837, hlam]
                          · have p18832_0 := h18832c.1
                            have p18832_1 := h18832c.2.1
                            have p18832_2 := h18832c.2.2.1
                            have p18832_3 := h18832c.2.2.2
                            rcases p18832_3 (m.d 0 1) (by simp) with h18938 | h18938
                            · linarith only [h0, h18938, hlam]
                            · rcases p18832_3 (m.d 0 2) (by simp) with h18940 | h18940
                              · rcases p18832_3 (m.d 0 3) (by simp) with h18941 | h18941
                                · linarith only [h18816, h18941, hlam]
                                · linarith only [h14396, h18941, hlam]
                              · linarith only [h0, h18940, hlam]
                          · have p18832_0 := h18832c.1
                            have p18832_1 := h18832c.2.1
                            have p18832_2 := h18832c.2.2.1
                            have p18832_3 := h18832c.2.2.2
                            linarith only [hlam, p18832_0]
                          · have p18832_0 := h18832c.1
                            have p18832_1 := h18832c.2.1
                            have p18832_2 := h18832c.2.2.1
                            have p18832_3 := h18832c.2.2.2
                            linarith only [h0, h18816, h18828, h18831, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18832_1]
                          · have p18832_0 := h18832c.1
                            have p18832_1 := h18832c.2.1
                            have p18832_2 := h18832c.2.2.1
                            have p18832_3 := h18832c.2.2.2
                            rcases p18832_3 (m.d 0 1) (by simp) with h18947 | h18947
                            · linarith only [h0, h18947, hlam]
                            · rcases p18832_3 (m.d 0 2) (by simp) with h18949 | h18949
                              · rcases p18832_3 (m.d 0 3) (by simp) with h18950 | h18950
                                · linarith only [h18816, h18950, hlam]
                                · linarith only [h18819, h18950, hlam]
                              · linarith only [h18817, h18949, hlam]
                          · have p18832_0 := h18832c.1
                            have p18832_1 := h18832c.2.1
                            have p18832_2 := h18832c.2.2.1
                            have p18832_3 := h18832c.2.2.2
                            rcases p18832_3 (m.d 0 1) (by simp) with h18954 | h18954
                            · linarith only [h0, h18954, hlam]
                            · linarith only [h18815, h18954, hlam]
                          · have p18832_0 := h18832c.1
                            have p18832_1 := h18832c.2.1
                            have p18832_2 := h18832c.2.2.1
                            have p18832_3 := h18832c.2.2.2
                            rcases p18832_3 (m.d 0 1) (by simp) with h18957 | h18957
                            · linarith only [h14396, h18957, hlam]
                            · rcases p18832_3 (m.d 0 2) (by simp) with h18959 | h18959
                              · rcases p18832_3 (m.d 0 3) (by simp) with h18960 | h18960
                                · rcases p18832_3 (m.d 0 4) (by simp) with h18961 | h18961
                                  · linarith only [h18819, h18961, hlam]
                                  · linarith only [h16915, h18961, hlam]
                                · linarith only [h14396, h18960, hlam]
                              · linarith only [h0, h18959, hlam]
                          · have p18832_0 := h18832c.1
                            have p18832_1 := h18832c.2.1
                            have p18832_2 := h18832c.2.2.1
                            have p18832_3 := h18832c.2.2.2
                            linarith only [h18816, hlam, p18832_1]
                          · have p18832_0 := h18832c.1
                            have p18832_1 := h18832c.2.1
                            have p18832_2 := h18832c.2.2.1
                            have p18832_3 := h18832c.2.2.2
                            linarith only [hlam, p18832_0]
                          · have p18832_0 := h18832c.1
                            have p18832_1 := h18832c.2.1
                            have p18832_2 := h18832c.2.2.1
                            have p18832_3 := h18832c.2.2.2
                            rcases p18832_3 (m.d 0 1) (by simp) with h18968 | h18968
                            · linarith only [h14396, h18968, hlam]
                            · rcases p18832_3 (m.d 0 2) (by simp) with h18970 | h18970
                              · rcases p18832_3 (m.d 0 3) (by simp) with h18971 | h18971
                                · rcases p18832_3 (m.d 0 4) (by simp) with h18972 | h18972
                                  · linarith only [h18819, h18972, hlam]
                                  · rcases p18832_3 (m.d 0 5) (by simp) with h18974 | h18974
                                    · linarith only [h18820, h18974, hlam]
                                    · rcases h2bigk with h18976c | h18976c | h18976c | h18976c | h18976c | h18976c | h18976c | h18976c | h18976c | h18976c | h18976c | h18976c | h18976c | h18976c | h18976c | h18976c | h18976c | h18976c | h18976c | h18976c | h18976c | h18976c | h18976c | h18976c | h18976c
                                      · have p18976_0 := h18976c.1
                                        have p18976_1 := h18976c.2.1
                                        have p18976_2 := h18976c.2.2.1
                                        have p18976_3 := h18976c.2.2.2
                                        linarith only [hlam, p18976_0]
                                      · have p18976_0 := h18976c.1
                                        have p18976_1 := h18976c.2.1
                                        have p18976_2 := h18976c.2.2.1
                                        have p18976_3 := h18976c.2.2.2
                                        linarith only [h0, hlam, p18976_1]
                                      · have p18976_0 := h18976c.1
                                        have p18976_1 := h18976c.2.1
                                        have p18976_2 := h18976c.2.2.1
                                        have p18976_3 := h18976c.2.2.2
                                        linarith only [h0, h18828, h18831, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18976_1]
                                      · have p18976_0 := h18976c.1
                                        have p18976_1 := h18976c.2.1
                                        have p18976_2 := h18976c.2.2.1
                                        have p18976_3 := h18976c.2.2.2
                                        rcases p18976_3 (m.d 0 2) (by simp) with h18980 | h18980
                                        · rcases p18976_3 (m.d 1 2) (by simp) with h18981 | h18981
                                          · rcases p18976_3 (m.d 2 3) (by simp) with h18982 | h18982
                                            · linarith only [h18816, h18982, hlam]
                                            · linarith only [h18828, h18982, hlam]
                                          · linarith only [h18823, h18981, hlam]
                                        · linarith only [h18980, hlam, p18976_0]
                                      · have p18976_0 := h18976c.1
                                        have p18976_1 := h18976c.2.1
                                        have p18976_2 := h18976c.2.2.1
                                        have p18976_3 := h18976c.2.2.2
                                        linarith only [h16915, h18815, h18816, h18824, hlam, p18832_1, p18976_2]
                                      · have p18976_0 := h18976c.1
                                        have p18976_1 := h18976c.2.1
                                        have p18976_2 := h18976c.2.2.1
                                        have p18976_3 := h18976c.2.2.2
                                        linarith only [h18816, h18828, h18831, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18976_1]
                                      · have p18976_0 := h18976c.1
                                        have p18976_1 := h18976c.2.1
                                        have p18976_2 := h18976c.2.2.1
                                        have p18976_3 := h18976c.2.2.2
                                        linarith only [hlam, p18976_0]
                                      · have p18976_0 := h18976c.1
                                        have p18976_1 := h18976c.2.1
                                        have p18976_2 := h18976c.2.2.1
                                        have p18976_3 := h18976c.2.2.2
                                        linarith only [h18828, h18831, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18976_1]
                                      · have p18976_0 := h18976c.1
                                        have p18976_1 := h18976c.2.1
                                        have p18976_2 := h18976c.2.2.1
                                        have p18976_3 := h18976c.2.2.2
                                        rcases p18976_3 (m.d 0 2) (by simp) with h18991 | h18991
                                        · linarith only [h0, h18991, hlam]
                                        · linarith only [h18817, h18991, hlam]
                                      · have p18976_0 := h18976c.1
                                        have p18976_1 := h18976c.2.1
                                        have p18976_2 := h18976c.2.2.1
                                        have p18976_3 := h18976c.2.2.2
                                        linarith only [h14396, h16915, h18815, h18822, h18824, hlam, p18832_1, p18976_2]
                                      · have p18976_0 := h18976c.1
                                        have p18976_1 := h18976c.2.1
                                        have p18976_2 := h18976c.2.2.1
                                        have p18976_3 := h18976c.2.2.2
                                        linarith only [h18816, hlam, p18976_0]
                                      · have p18976_0 := h18976c.1
                                        have p18976_1 := h18976c.2.1
                                        have p18976_2 := h18976c.2.2.1
                                        have p18976_3 := h18976c.2.2.2
                                        linarith only [h18822, hlam, p18976_0]
                                      · have p18976_0 := h18976c.1
                                        have p18976_1 := h18976c.2.1
                                        have p18976_2 := h18976c.2.2.1
                                        have p18976_3 := h18976c.2.2.2
                                        linarith only [hlam, p18976_0]
                                      · have p18976_0 := h18976c.1
                                        have p18976_1 := h18976c.2.1
                                        have p18976_2 := h18976c.2.2.1
                                        have p18976_3 := h18976c.2.2.2
                                        linarith only [h0, h18816, h18828, h18831, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18976_1]
                                      · have p18976_0 := h18976c.1
                                        have p18976_1 := h18976c.2.1
                                        have p18976_2 := h18976c.2.2.1
                                        have p18976_3 := h18976c.2.2.2
                                        rcases p18976_3 (m.d 0 2) (by simp) with h18999 | h18999
                                        · rcases p18976_3 (m.d 1 2) (by simp) with h19000 | h19000
                                          · rcases p18976_3 (m.d 2 3) (by simp) with h19001 | h19001
                                            · rcases p18976_3 (m.d 2 4) (by simp) with h19002 | h19002
                                              · linarith only [h18828, h19002, hlam]
                                              · linarith only [h18830, h19002, hlam]
                                            · linarith only [h18829, h19001, hlam]
                                          · linarith only [h18824, h19000, hlam]
                                        · linarith only [h18818, h18999, hlam]
                                      · have p18976_0 := h18976c.1
                                        have p18976_1 := h18976c.2.1
                                        have p18976_2 := h18976c.2.2.1
                                        have p18976_3 := h18976c.2.2.2
                                        linarith only [h18817, hlam, p18976_0]
                                      · have p18976_0 := h18976c.1
                                        have p18976_1 := h18976c.2.1
                                        have p18976_2 := h18976c.2.2.1
                                        have p18976_3 := h18976c.2.2.2
                                        linarith only [h18823, hlam, p18976_0]
                                      · have p18976_0 := h18976c.1
                                        have p18976_1 := h18976c.2.1
                                        have p18976_2 := h18976c.2.2.1
                                        have p18976_3 := h18976c.2.2.2
                                        linarith only [h18828, hlam, p18976_1]
                                      · have p18976_0 := h18976c.1
                                        have p18976_1 := h18976c.2.1
                                        have p18976_2 := h18976c.2.2.1
                                        have p18976_3 := h18976c.2.2.2
                                        linarith only [hlam, p18976_0]
                                      · have p18976_0 := h18976c.1
                                        have p18976_1 := h18976c.2.1
                                        have p18976_2 := h18976c.2.2.1
                                        have p18976_3 := h18976c.2.2.2
                                        linarith only [h14396, h18817, h18822, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p18832_1, p18976_1]
                                      · have p18976_0 := h18976c.1
                                        have p18976_1 := h18976c.2.1
                                        have p18976_2 := h18976c.2.2.1
                                        have p18976_3 := h18976c.2.2.2
                                        linarith only [h18818, hlam, p18976_0]
                                      · have p18976_0 := h18976c.1
                                        have p18976_1 := h18976c.2.1
                                        have p18976_2 := h18976c.2.2.1
                                        have p18976_3 := h18976c.2.2.2
                                        linarith only [h18824, hlam, p18976_0]
                                      · have p18976_0 := h18976c.1
                                        have p18976_1 := h18976c.2.1
                                        have p18976_2 := h18976c.2.2.1
                                        have p18976_3 := h18976c.2.2.2
                                        linarith only [h18829, hlam, p18976_1]
                                      · have p18976_0 := h18976c.1
                                        have p18976_1 := h18976c.2.1
                                        have p18976_2 := h18976c.2.2.1
                                        have p18976_3 := h18976c.2.2.2
                                        linarith only [h18830, hlam, p18976_0]
                                      · have p18976_0 := h18976c.1
                                        have p18976_1 := h18976c.2.1
                                        have p18976_2 := h18976c.2.2.1
                                        have p18976_3 := h18976c.2.2.2
                                        linarith only [hlam, p18976_0]
                                · linarith only [h18819, h18971, hlam]
                              · linarith only [h18817, h18970, hlam]
                          · have p18832_0 := h18832c.1
                            have p18832_1 := h18832c.2.1
                            have p18832_2 := h18832c.2.2.1
                            have p18832_3 := h18832c.2.2.2
                            rcases p18832_3 (m.d 0 1) (by simp) with h19020 | h19020
                            · linarith only [h14396, h19020, hlam]
                            · linarith only [h18815, h19020, hlam]
                          · have p18832_0 := h18832c.1
                            have p18832_1 := h18832c.2.1
                            have p18832_2 := h18832c.2.2.1
                            have p18832_3 := h18832c.2.2.2
                            rcases p18832_3 (m.d 0 1) (by simp) with h19023 | h19023
                            · linarith only [h16915, h19023, hlam]
                            · rcases p18832_3 (m.d 0 2) (by simp) with h19025 | h19025
                              · rcases p18832_3 (m.d 0 3) (by simp) with h19026 | h19026
                                · rcases p18832_3 (m.d 0 4) (by simp) with h19027 | h19027
                                  · rcases p18832_3 (m.d 0 5) (by simp) with h19028 | h19028
                                    · linarith only [h18821, h19028, hlam]
                                    · rcases h2bigk with h19030c | h19030c | h19030c | h19030c | h19030c | h19030c | h19030c | h19030c | h19030c | h19030c | h19030c | h19030c | h19030c | h19030c | h19030c | h19030c | h19030c | h19030c | h19030c | h19030c | h19030c | h19030c | h19030c | h19030c | h19030c
                                      · have p19030_0 := h19030c.1
                                        have p19030_1 := h19030c.2.1
                                        have p19030_2 := h19030c.2.2.1
                                        have p19030_3 := h19030c.2.2.2
                                        linarith only [hlam, p19030_0]
                                      · have p19030_0 := h19030c.1
                                        have p19030_1 := h19030c.2.1
                                        have p19030_2 := h19030c.2.2.1
                                        have p19030_3 := h19030c.2.2.2
                                        linarith only [h0, hlam, p19030_1]
                                      · have p19030_0 := h19030c.1
                                        have p19030_1 := h19030c.2.1
                                        have p19030_2 := h19030c.2.2.1
                                        have p19030_3 := h19030c.2.2.2
                                        linarith only [h0, h18828, h18831, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19030_1]
                                      · have p19030_0 := h19030c.1
                                        have p19030_1 := h19030c.2.1
                                        have p19030_2 := h19030c.2.2.1
                                        have p19030_3 := h19030c.2.2.2
                                        rcases p19030_3 (m.d 0 2) (by simp) with h19034 | h19034
                                        · rcases p19030_3 (m.d 1 2) (by simp) with h19035 | h19035
                                          · rcases p19030_3 (m.d 2 3) (by simp) with h19036 | h19036
                                            · linarith only [h18816, h19036, hlam]
                                            · linarith only [h18828, h19036, hlam]
                                          · linarith only [h18823, h19035, hlam]
                                        · linarith only [h19034, hlam, p19030_0]
                                      · have p19030_0 := h19030c.1
                                        have p19030_1 := h19030c.2.1
                                        have p19030_2 := h19030c.2.2.1
                                        have p19030_3 := h19030c.2.2.2
                                        linarith only [h18815, h18817, h18824, hlam, p18832_1, p19030_2]
                                      · have p19030_0 := h19030c.1
                                        have p19030_1 := h19030c.2.1
                                        have p19030_2 := h19030c.2.2.1
                                        have p19030_3 := h19030c.2.2.2
                                        linarith only [h18816, h18828, h18831, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19030_1]
                                      · have p19030_0 := h19030c.1
                                        have p19030_1 := h19030c.2.1
                                        have p19030_2 := h19030c.2.2.1
                                        have p19030_3 := h19030c.2.2.2
                                        linarith only [hlam, p19030_0]
                                      · have p19030_0 := h19030c.1
                                        have p19030_1 := h19030c.2.1
                                        have p19030_2 := h19030c.2.2.1
                                        have p19030_3 := h19030c.2.2.2
                                        linarith only [h18828, h18831, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19030_1]
                                      · have p19030_0 := h19030c.1
                                        have p19030_1 := h19030c.2.1
                                        have p19030_2 := h19030c.2.2.1
                                        have p19030_3 := h19030c.2.2.2
                                        rcases p19030_3 (m.d 0 2) (by simp) with h19045 | h19045
                                        · linarith only [h0, h19045, hlam]
                                        · linarith only [h18817, h19045, hlam]
                                      · have p19030_0 := h19030c.1
                                        have p19030_1 := h19030c.2.1
                                        have p19030_2 := h19030c.2.2.1
                                        have p19030_3 := h19030c.2.2.2
                                        linarith only [h0, h18815, h18816, h18819, h18824, hlam, p18832_1, p19030_2]
                                      · have p19030_0 := h19030c.1
                                        have p19030_1 := h19030c.2.1
                                        have p19030_2 := h19030c.2.2.1
                                        have p19030_3 := h19030c.2.2.2
                                        linarith only [h18816, hlam, p19030_0]
                                      · have p19030_0 := h19030c.1
                                        have p19030_1 := h19030c.2.1
                                        have p19030_2 := h19030c.2.2.1
                                        have p19030_3 := h19030c.2.2.2
                                        linarith only [h18822, hlam, p19030_0]
                                      · have p19030_0 := h19030c.1
                                        have p19030_1 := h19030c.2.1
                                        have p19030_2 := h19030c.2.2.1
                                        have p19030_3 := h19030c.2.2.2
                                        linarith only [hlam, p19030_0]
                                      · have p19030_0 := h19030c.1
                                        have p19030_1 := h19030c.2.1
                                        have p19030_2 := h19030c.2.2.1
                                        have p19030_3 := h19030c.2.2.2
                                        linarith only [h18816, h18828, h18831, hc02, hc45, hlam, hphi, ht0b, ht5b, p19030_1]
                                      · have p19030_0 := h19030c.1
                                        have p19030_1 := h19030c.2.1
                                        have p19030_2 := h19030c.2.2.1
                                        have p19030_3 := h19030c.2.2.2
                                        rcases p19030_3 (m.d 0 2) (by simp) with h19053 | h19053
                                        · rcases p19030_3 (m.d 1 2) (by simp) with h19054 | h19054
                                          · rcases p19030_3 (m.d 2 3) (by simp) with h19055 | h19055
                                            · rcases p19030_3 (m.d 2 4) (by simp) with h19056 | h19056
                                              · linarith only [h18828, h19056, hlam]
                                              · linarith only [h18830, h19056, hlam]
                                            · linarith only [h18829, h19055, hlam]
                                          · linarith only [h18824, h19054, hlam]
                                        · linarith only [h18818, h19053, hlam]
                                      · have p19030_0 := h19030c.1
                                        have p19030_1 := h19030c.2.1
                                        have p19030_2 := h19030c.2.2.1
                                        have p19030_3 := h19030c.2.2.2
                                        linarith only [h18817, hlam, p19030_0]
                                      · have p19030_0 := h19030c.1
                                        have p19030_1 := h19030c.2.1
                                        have p19030_2 := h19030c.2.2.1
                                        have p19030_3 := h19030c.2.2.2
                                        linarith only [h18823, hlam, p19030_0]
                                      · have p19030_0 := h19030c.1
                                        have p19030_1 := h19030c.2.1
                                        have p19030_2 := h19030c.2.2.1
                                        have p19030_3 := h19030c.2.2.2
                                        linarith only [h18828, hlam, p19030_1]
                                      · have p19030_0 := h19030c.1
                                        have p19030_1 := h19030c.2.1
                                        have p19030_2 := h19030c.2.2.1
                                        have p19030_3 := h19030c.2.2.2
                                        linarith only [hlam, p19030_0]
                                      · have p19030_0 := h19030c.1
                                        have p19030_1 := h19030c.2.1
                                        have p19030_2 := h19030c.2.2.1
                                        have p19030_3 := h19030c.2.2.2
                                        rcases p19030_3 (m.d 0 2) (by simp) with h19066 | h19066
                                        · rcases p19030_3 (m.d 1 2) (by simp) with h19067 | h19067
                                          · rcases p19030_3 (m.d 2 3) (by simp) with h19068 | h19068
                                            · rcases p19030_3 (m.d 2 4) (by simp) with h19069 | h19069
                                              · rcases p19030_3 (m.d 2 5) (by simp) with h19070 | h19070
                                                · linarith only [h18830, h19070, hlam]
                                                · rcases h3bigk with h19072c | h19072c | h19072c | h19072c | h19072c | h19072c | h19072c | h19072c | h19072c | h19072c | h19072c | h19072c | h19072c | h19072c | h19072c | h19072c | h19072c | h19072c | h19072c | h19072c | h19072c | h19072c | h19072c | h19072c | h19072c
                                                  · have p19072_0 := h19072c.1
                                                    have p19072_1 := h19072c.2.1
                                                    have p19072_2 := h19072c.2.2.1
                                                    have p19072_3 := h19072c.2.2.2
                                                    linarith only [hlam, p19072_0]
                                                  · have p19072_0 := h19072c.1
                                                    have p19072_1 := h19072c.2.1
                                                    have p19072_2 := h19072c.2.2.1
                                                    have p19072_3 := h19072c.2.2.2
                                                    linarith only [h14396, hlam, p19072_1]
                                                  · have p19072_0 := h19072c.1
                                                    have p19072_1 := h19072c.2.1
                                                    have p19072_2 := h19072c.2.2.1
                                                    have p19072_3 := h19072c.2.2.2
                                                    linarith only [h14396, h18822, h18828, h18831, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19072_1]
                                                  · have p19072_0 := h19072c.1
                                                    have p19072_1 := h19072c.2.1
                                                    have p19072_2 := h19072c.2.2.1
                                                    have p19072_3 := h19072c.2.2.2
                                                    linarith only [h14396, h18822, h18831, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19072_1]
                                                  · have p19072_0 := h19072c.1
                                                    have p19072_1 := h19072c.2.1
                                                    have p19072_2 := h19072c.2.2.1
                                                    have p19072_3 := h19072c.2.2.2
                                                    rcases p19072_3 (m.d 0 3) (by simp) with h19077 | h19077
                                                    · rcases p19072_3 (m.d 1 3) (by simp) with h19078 | h19078
                                                      · rcases p19072_3 (m.d 2 3) (by simp) with h19079 | h19079
                                                        · linarith only [h18816, h19079, hlam]
                                                        · linarith only [h18829, h19079, hlam]
                                                      · linarith only [h18826, h19078, hlam]
                                                    · linarith only [h19077, hlam, p19072_0]
                                                  · have p19072_0 := h19072c.1
                                                    have p19072_1 := h19072c.2.1
                                                    have p19072_2 := h19072c.2.2.1
                                                    have p19072_3 := h19072c.2.2.2
                                                    linarith only [h14396, h18815, h18822, h18824, h18829, h18831, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19072_1]
                                                  · have p19072_0 := h19072c.1
                                                    have p19072_1 := h19072c.2.1
                                                    have p19072_2 := h19072c.2.2.1
                                                    have p19072_3 := h19072c.2.2.2
                                                    linarith only [hlam, p19072_0]
                                                  · have p19072_0 := h19072c.1
                                                    have p19072_1 := h19072c.2.1
                                                    have p19072_2 := h19072c.2.2.1
                                                    have p19072_3 := h19072c.2.2.2
                                                    linarith only [h18822, h18828, h18829, h18831, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19030_1, p19072_1]
                                                  · have p19072_0 := h19072c.1
                                                    have p19072_1 := h19072c.2.1
                                                    have p19072_2 := h19072c.2.2.1
                                                    have p19072_3 := h19072c.2.2.2
                                                    linarith only [h18822, h18831, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19072_1]
                                                  · have p19072_0 := h19072c.1
                                                    have p19072_1 := h19072c.2.1
                                                    have p19072_2 := h19072c.2.2.1
                                                    have p19072_3 := h19072c.2.2.2
                                                    rcases p19072_3 (m.d 0 3) (by simp) with h19088 | h19088
                                                    · linarith only [h14396, h19088, hlam]
                                                    · linarith only [h18820, h19088, hlam]
                                                  · have p19072_0 := h19072c.1
                                                    have p19072_1 := h19072c.2.1
                                                    have p19072_2 := h19072c.2.2.1
                                                    have p19072_3 := h19072c.2.2.2
                                                    linarith only [h18816, hlam, p19072_0]
                                                  · have p19072_0 := h19072c.1
                                                    have p19072_1 := h19072c.2.1
                                                    have p19072_2 := h19072c.2.2.1
                                                    have p19072_3 := h19072c.2.2.2
                                                    linarith only [h18822, hlam, p19072_0]
                                                  · have p19072_0 := h19072c.1
                                                    have p19072_1 := h19072c.2.1
                                                    have p19072_2 := h19072c.2.2.1
                                                    have p19072_3 := h19072c.2.2.2
                                                    linarith only [hlam, p19072_0]
                                                  · have p19072_0 := h19072c.1
                                                    have p19072_1 := h19072c.2.1
                                                    have p19072_2 := h19072c.2.2.1
                                                    have p19072_3 := h19072c.2.2.2
                                                    linarith only [h18831, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p19072_1]
                                                  · have p19072_0 := h19072c.1
                                                    have p19072_1 := h19072c.2.1
                                                    have p19072_2 := h19072c.2.2.1
                                                    have p19072_3 := h19072c.2.2.2
                                                    linarith only [h0, h18816, h18831, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19072_1]
                                                  · have p19072_0 := h19072c.1
                                                    have p19072_1 := h19072c.2.1
                                                    have p19072_2 := h19072c.2.2.1
                                                    have p19072_3 := h19072c.2.2.2
                                                    linarith only [h18819, hlam, p19072_0]
                                                  · have p19072_0 := h19072c.1
                                                    have p19072_1 := h19072c.2.1
                                                    have p19072_2 := h19072c.2.2.1
                                                    have p19072_3 := h19072c.2.2.2
                                                    linarith only [h18825, hlam, p19072_0]
                                                  · have p19072_0 := h19072c.1
                                                    have p19072_1 := h19072c.2.1
                                                    have p19072_2 := h19072c.2.2.1
                                                    have p19072_3 := h19072c.2.2.2
                                                    linarith only [h18828, hlam, p19072_0]
                                                  · have p19072_0 := h19072c.1
                                                    have p19072_1 := h19072c.2.1
                                                    have p19072_2 := h19072c.2.2.1
                                                    have p19072_3 := h19072c.2.2.2
                                                    linarith only [hlam, p19072_0]
                                                  · have p19072_0 := h19072c.1
                                                    have p19072_1 := h19072c.2.1
                                                    have p19072_2 := h19072c.2.2.1
                                                    have p19072_3 := h19072c.2.2.2
                                                    linarith only [h18819, h18831, hc03, hc45, hlam, hphi, ht0b, ht5b, p19072_1]
                                                  · have p19072_0 := h19072c.1
                                                    have p19072_1 := h19072c.2.1
                                                    have p19072_2 := h19072c.2.2.1
                                                    have p19072_3 := h19072c.2.2.2
                                                    linarith only [h18820, hlam, p19072_0]
                                                  · have p19072_0 := h19072c.1
                                                    have p19072_1 := h19072c.2.1
                                                    have p19072_2 := h19072c.2.2.1
                                                    have p19072_3 := h19072c.2.2.2
                                                    linarith only [h18826, hlam, p19072_0]
                                                  · have p19072_0 := h19072c.1
                                                    have p19072_1 := h19072c.2.1
                                                    have p19072_2 := h19072c.2.2.1
                                                    have p19072_3 := h19072c.2.2.2
                                                    linarith only [h18829, hlam, p19072_0]
                                                  · have p19072_0 := h19072c.1
                                                    have p19072_1 := h19072c.2.1
                                                    have p19072_2 := h19072c.2.2.1
                                                    have p19072_3 := h19072c.2.2.2
                                                    linarith only [h18831, hlam, p19072_0]
                                                  · have p19072_0 := h19072c.1
                                                    have p19072_1 := h19072c.2.1
                                                    have p19072_2 := h19072c.2.2.1
                                                    have p19072_3 := h19072c.2.2.2
                                                    linarith only [hlam, p19072_0]
                                              · linarith only [h18830, h19069, hlam]
                                            · linarith only [h18829, h19068, hlam]
                                          · linarith only [h18824, h19067, hlam]
                                        · linarith only [h18818, h19066, hlam]
                                      · have p19030_0 := h19030c.1
                                        have p19030_1 := h19030c.2.1
                                        have p19030_2 := h19030c.2.2.1
                                        have p19030_3 := h19030c.2.2.2
                                        linarith only [h18818, hlam, p19030_0]
                                      · have p19030_0 := h19030c.1
                                        have p19030_1 := h19030c.2.1
                                        have p19030_2 := h19030c.2.2.1
                                        have p19030_3 := h19030c.2.2.2
                                        linarith only [h18824, hlam, p19030_0]
                                      · have p19030_0 := h19030c.1
                                        have p19030_1 := h19030c.2.1
                                        have p19030_2 := h19030c.2.2.1
                                        have p19030_3 := h19030c.2.2.2
                                        linarith only [h18829, hlam, p19030_1]
                                      · have p19030_0 := h19030c.1
                                        have p19030_1 := h19030c.2.1
                                        have p19030_2 := h19030c.2.2.1
                                        have p19030_3 := h19030c.2.2.2
                                        linarith only [h18830, hlam, p19030_0]
                                      · have p19030_0 := h19030c.1
                                        have p19030_1 := h19030c.2.1
                                        have p19030_2 := h19030c.2.2.1
                                        have p19030_3 := h19030c.2.2.2
                                        linarith only [hlam, p19030_0]
                                  · linarith only [h16915, h19027, hlam]
                                · linarith only [h14396, h19026, hlam]
                              · linarith only [h0, h19025, hlam]
                          · have p18832_0 := h18832c.1
                            have p18832_1 := h18832c.2.1
                            have p18832_2 := h18832c.2.2.1
                            have p18832_3 := h18832c.2.2.2
                            linarith only [h18817, hlam, p18832_0]
                          · have p18832_0 := h18832c.1
                            have p18832_1 := h18832c.2.1
                            have p18832_2 := h18832c.2.2.1
                            have p18832_3 := h18832c.2.2.2
                            linarith only [h18819, hlam, p18832_0]
                          · have p18832_0 := h18832c.1
                            have p18832_1 := h18832c.2.1
                            have p18832_2 := h18832c.2.2.1
                            have p18832_3 := h18832c.2.2.2
                            linarith only [hlam, p18832_0]
                          · have p18832_0 := h18832c.1
                            have p18832_1 := h18832c.2.1
                            have p18832_2 := h18832c.2.2.1
                            have p18832_3 := h18832c.2.2.2
                            rcases p18832_3 (m.d 0 1) (by simp) with h19121 | h19121
                            · linarith only [h16915, h19121, hlam]
                            · linarith only [h18815, h19121, hlam]
                          · have p18832_0 := h18832c.1
                            have p18832_1 := h18832c.2.1
                            have p18832_2 := h18832c.2.2.1
                            have p18832_3 := h18832c.2.2.2
                            linarith only [h18815, hlam, p18832_0]
                          · have p18832_0 := h18832c.1
                            have p18832_1 := h18832c.2.1
                            have p18832_2 := h18832c.2.2.1
                            have p18832_3 := h18832c.2.2.2
                            linarith only [h18818, hlam, p18832_1]
                          · have p18832_0 := h18832c.1
                            have p18832_1 := h18832c.2.1
                            have p18832_2 := h18832c.2.2.1
                            have p18832_3 := h18832c.2.2.2
                            linarith only [h18820, hlam, p18832_0]
                          · have p18832_0 := h18832c.1
                            have p18832_1 := h18832c.2.1
                            have p18832_2 := h18832c.2.2.1
                            have p18832_3 := h18832c.2.2.2
                            linarith only [h18821, hlam, p18832_1]
                          · have p18832_0 := h18832c.1
                            have p18832_1 := h18832c.2.1
                            have p18832_2 := h18832c.2.2.1
                            have p18832_3 := h18832c.2.2.2
                            linarith only [hlam, p18832_0]
                        · rcases h0bigk with h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c
                          · have p19129_0 := h19129c.1
                            have p19129_1 := h19129c.2.1
                            have p19129_2 := h19129c.2.2.1
                            have p19129_3 := h19129c.2.2.2
                            linarith only [hlam, p19129_0]
                          · have p19129_0 := h19129c.1
                            have p19129_1 := h19129c.2.1
                            have p19129_2 := h19129c.2.2.1
                            have p19129_3 := h19129c.2.2.2
                            linarith only [h0, hlam, p19129_1]
                          · have p19129_0 := h19129c.1
                            have p19129_1 := h19129c.2.1
                            have p19129_2 := h19129c.2.2.1
                            have p19129_3 := h19129c.2.2.2
                            linarith only [h14396, hlam, p19129_0]
                          · have p19129_0 := h19129c.1
                            have p19129_1 := h19129c.2.1
                            have p19129_2 := h19129c.2.2.1
                            have p19129_3 := h19129c.2.2.2
                            linarith only [h16915, hlam, p19129_1]
                          · have p19129_0 := h19129c.1
                            have p19129_1 := h19129c.2.1
                            have p19129_2 := h19129c.2.2.1
                            have p19129_3 := h19129c.2.2.2
                            linarith only [h0, h18815, h18824, h18830, h18831, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19129_1]
                          · have p19129_0 := h19129c.1
                            have p19129_1 := h19129c.2.1
                            have p19129_2 := h19129c.2.2.1
                            have p19129_3 := h19129c.2.2.2
                            linarith only [h0, h18815, h18824, h18830, h18831, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19129_1]
                          · have p19129_0 := h19129c.1
                            have p19129_1 := h19129c.2.1
                            have p19129_2 := h19129c.2.2.1
                            have p19129_3 := h19129c.2.2.2
                            linarith only [hlam, p19129_0]
                          · have p19129_0 := h19129c.1
                            have p19129_1 := h19129c.2.1
                            have p19129_2 := h19129c.2.2.1
                            have p19129_3 := h19129c.2.2.2
                            linarith only [h0, h14396, h18815, h18824, h18830, h18831, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19129_1]
                          · have p19129_0 := h19129c.1
                            have p19129_1 := h19129c.2.1
                            have p19129_2 := h19129c.2.2.1
                            have p19129_3 := h19129c.2.2.2
                            linarith only [h0, h16915, h18815, h18824, h18830, h18831, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19129_1]
                          · have p19129_0 := h19129c.1
                            have p19129_1 := h19129c.2.1
                            have p19129_2 := h19129c.2.2.1
                            have p19129_3 := h19129c.2.2.2
                            rcases p19129_3 (m.d 0 1) (by simp) with h19139 | h19139
                            · linarith only [h0, h19139, hlam]
                            · linarith only [h18815, h19139, hlam]
                          · have p19129_0 := h19129c.1
                            have p19129_1 := h19129c.2.1
                            have p19129_2 := h19129c.2.2.1
                            have p19129_3 := h19129c.2.2.2
                            linarith only [h18815, h18824, h18830, h18831, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p19129_1]
                          · have p19129_0 := h19129c.1
                            have p19129_1 := h19129c.2.1
                            have p19129_2 := h19129c.2.2.1
                            have p19129_3 := h19129c.2.2.2
                            linarith only [h18816, hlam, p19129_1]
                          · have p19129_0 := h19129c.1
                            have p19129_1 := h19129c.2.1
                            have p19129_2 := h19129c.2.2.1
                            have p19129_3 := h19129c.2.2.2
                            linarith only [hlam, p19129_0]
                          · have p19129_0 := h19129c.1
                            have p19129_1 := h19129c.2.1
                            have p19129_2 := h19129c.2.2.1
                            have p19129_3 := h19129c.2.2.2
                            linarith only [h14396, h16915, h18815, h18822, h18824, h18830, h18831, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19129_1]
                          · have p19129_0 := h19129c.1
                            have p19129_1 := h19129c.2.1
                            have p19129_2 := h19129c.2.2.1
                            have p19129_3 := h19129c.2.2.2
                            rcases p19129_3 (m.d 0 1) (by simp) with h19146 | h19146
                            · linarith only [h14396, h19146, hlam]
                            · linarith only [h18815, h19146, hlam]
                          · have p19129_0 := h19129c.1
                            have p19129_1 := h19129c.2.1
                            have p19129_2 := h19129c.2.2.1
                            have p19129_3 := h19129c.2.2.2
                            linarith only [h18815, h18824, h18830, h18831, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p19129_1]
                          · have p19129_0 := h19129c.1
                            have p19129_1 := h19129c.2.1
                            have p19129_2 := h19129c.2.2.1
                            have p19129_3 := h19129c.2.2.2
                            linarith only [h18817, hlam, p19129_0]
                          · have p19129_0 := h19129c.1
                            have p19129_1 := h19129c.2.1
                            have p19129_2 := h19129c.2.2.1
                            have p19129_3 := h19129c.2.2.2
                            linarith only [h18819, hlam, p19129_0]
                          · have p19129_0 := h19129c.1
                            have p19129_1 := h19129c.2.1
                            have p19129_2 := h19129c.2.2.1
                            have p19129_3 := h19129c.2.2.2
                            linarith only [hlam, p19129_0]
                          · have p19129_0 := h19129c.1
                            have p19129_1 := h19129c.2.1
                            have p19129_2 := h19129c.2.2.1
                            have p19129_3 := h19129c.2.2.2
                            rcases p19129_3 (m.d 0 1) (by simp) with h19153 | h19153
                            · linarith only [h16915, h19153, hlam]
                            · linarith only [h18815, h19153, hlam]
                          · have p19129_0 := h19129c.1
                            have p19129_1 := h19129c.2.1
                            have p19129_2 := h19129c.2.2.1
                            have p19129_3 := h19129c.2.2.2
                            linarith only [h18815, hlam, p19129_0]
                          · have p19129_0 := h19129c.1
                            have p19129_1 := h19129c.2.1
                            have p19129_2 := h19129c.2.2.1
                            have p19129_3 := h19129c.2.2.2
                            linarith only [h18818, hlam, p19129_1]
                          · have p19129_0 := h19129c.1
                            have p19129_1 := h19129c.2.1
                            have p19129_2 := h19129c.2.2.1
                            have p19129_3 := h19129c.2.2.2
                            linarith only [h18820, hlam, p19129_0]
                          · have p19129_0 := h19129c.1
                            have p19129_1 := h19129c.2.1
                            have p19129_2 := h19129c.2.2.1
                            have p19129_3 := h19129c.2.2.2
                            linarith only [h18821, hlam, p19129_1]
                          · have p19129_0 := h19129c.1
                            have p19129_1 := h19129c.2.1
                            have p19129_2 := h19129c.2.2.1
                            have p19129_3 := h19129c.2.2.2
                            linarith only [hlam, p19129_0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h19161 | h19161
                        · linarith only [h0, h18816, h18828, h18830, h19161, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases h0bigk with h19163c | h19163c | h19163c | h19163c | h19163c | h19163c | h19163c | h19163c | h19163c | h19163c | h19163c | h19163c | h19163c | h19163c | h19163c | h19163c | h19163c | h19163c | h19163c | h19163c | h19163c | h19163c | h19163c | h19163c | h19163c
                          · have p19163_0 := h19163c.1
                            have p19163_1 := h19163c.2.1
                            have p19163_2 := h19163c.2.2.1
                            have p19163_3 := h19163c.2.2.2
                            linarith only [hlam, p19163_0]
                          · have p19163_0 := h19163c.1
                            have p19163_1 := h19163c.2.1
                            have p19163_2 := h19163c.2.2.1
                            have p19163_3 := h19163c.2.2.2
                            linarith only [h0, hlam, p19163_1]
                          · have p19163_0 := h19163c.1
                            have p19163_1 := h19163c.2.1
                            have p19163_2 := h19163c.2.2.1
                            have p19163_3 := h19163c.2.2.2
                            linarith only [h14396, hlam, p19163_0]
                          · have p19163_0 := h19163c.1
                            have p19163_1 := h19163c.2.1
                            have p19163_2 := h19163c.2.2.1
                            have p19163_3 := h19163c.2.2.2
                            linarith only [h16915, hlam, p19163_1]
                          · have p19163_0 := h19163c.1
                            have p19163_1 := h19163c.2.1
                            have p19163_2 := h19163c.2.2.1
                            have p19163_3 := h19163c.2.2.2
                            linarith only [h16915, h18815, h18822, h18825, h18827, h18828, h18830, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19163_1]
                          · have p19163_0 := h19163c.1
                            have p19163_1 := h19163c.2.1
                            have p19163_2 := h19163c.2.2.1
                            have p19163_3 := h19163c.2.2.2
                            linarith only [h0, h18815, h18827, h18828, h18830, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19163_1]
                          · have p19163_0 := h19163c.1
                            have p19163_1 := h19163c.2.1
                            have p19163_2 := h19163c.2.2.1
                            have p19163_3 := h19163c.2.2.2
                            linarith only [hlam, p19163_0]
                          · have p19163_0 := h19163c.1
                            have p19163_1 := h19163c.2.1
                            have p19163_2 := h19163c.2.2.1
                            have p19163_3 := h19163c.2.2.2
                            linarith only [h0, h14396, h18815, h18827, h18828, h18830, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19163_1]
                          · have p19163_0 := h19163c.1
                            have p19163_1 := h19163c.2.1
                            have p19163_2 := h19163c.2.2.1
                            have p19163_3 := h19163c.2.2.2
                            linarith only [h0, h16915, h18815, h18827, h18828, h18830, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19163_1]
                          · have p19163_0 := h19163c.1
                            have p19163_1 := h19163c.2.1
                            have p19163_2 := h19163c.2.2.1
                            have p19163_3 := h19163c.2.2.2
                            rcases p19163_3 (m.d 0 1) (by simp) with h19173 | h19173
                            · linarith only [h0, h19173, hlam]
                            · linarith only [h18815, h19173, hlam]
                          · have p19163_0 := h19163c.1
                            have p19163_1 := h19163c.2.1
                            have p19163_2 := h19163c.2.2.1
                            have p19163_3 := h19163c.2.2.2
                            linarith only [h18815, h18827, h18828, h18830, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p19163_1]
                          · have p19163_0 := h19163c.1
                            have p19163_1 := h19163c.2.1
                            have p19163_2 := h19163c.2.2.1
                            have p19163_3 := h19163c.2.2.2
                            linarith only [h18816, hlam, p19163_1]
                          · have p19163_0 := h19163c.1
                            have p19163_1 := h19163c.2.1
                            have p19163_2 := h19163c.2.2.1
                            have p19163_3 := h19163c.2.2.2
                            linarith only [hlam, p19163_0]
                          · have p19163_0 := h19163c.1
                            have p19163_1 := h19163c.2.1
                            have p19163_2 := h19163c.2.2.1
                            have p19163_3 := h19163c.2.2.2
                            linarith only [h14396, h16915, h18815, h18822, h18827, h18828, h18830, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19163_1]
                          · have p19163_0 := h19163c.1
                            have p19163_1 := h19163c.2.1
                            have p19163_2 := h19163c.2.2.1
                            have p19163_3 := h19163c.2.2.2
                            rcases p19163_3 (m.d 0 1) (by simp) with h19180 | h19180
                            · linarith only [h14396, h19180, hlam]
                            · linarith only [h18815, h19180, hlam]
                          · have p19163_0 := h19163c.1
                            have p19163_1 := h19163c.2.1
                            have p19163_2 := h19163c.2.2.1
                            have p19163_3 := h19163c.2.2.2
                            linarith only [h18815, h18827, h18828, h18830, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p19163_1]
                          · have p19163_0 := h19163c.1
                            have p19163_1 := h19163c.2.1
                            have p19163_2 := h19163c.2.2.1
                            have p19163_3 := h19163c.2.2.2
                            linarith only [h18817, hlam, p19163_0]
                          · have p19163_0 := h19163c.1
                            have p19163_1 := h19163c.2.1
                            have p19163_2 := h19163c.2.2.1
                            have p19163_3 := h19163c.2.2.2
                            linarith only [h18819, hlam, p19163_0]
                          · have p19163_0 := h19163c.1
                            have p19163_1 := h19163c.2.1
                            have p19163_2 := h19163c.2.2.1
                            have p19163_3 := h19163c.2.2.2
                            linarith only [hlam, p19163_0]
                          · have p19163_0 := h19163c.1
                            have p19163_1 := h19163c.2.1
                            have p19163_2 := h19163c.2.2.1
                            have p19163_3 := h19163c.2.2.2
                            rcases p19163_3 (m.d 0 1) (by simp) with h19187 | h19187
                            · linarith only [h16915, h19187, hlam]
                            · linarith only [h18815, h19187, hlam]
                          · have p19163_0 := h19163c.1
                            have p19163_1 := h19163c.2.1
                            have p19163_2 := h19163c.2.2.1
                            have p19163_3 := h19163c.2.2.2
                            linarith only [h18815, hlam, p19163_0]
                          · have p19163_0 := h19163c.1
                            have p19163_1 := h19163c.2.1
                            have p19163_2 := h19163c.2.2.1
                            have p19163_3 := h19163c.2.2.2
                            linarith only [h18818, hlam, p19163_1]
                          · have p19163_0 := h19163c.1
                            have p19163_1 := h19163c.2.1
                            have p19163_2 := h19163c.2.2.1
                            have p19163_3 := h19163c.2.2.2
                            linarith only [h18820, hlam, p19163_0]
                          · have p19163_0 := h19163c.1
                            have p19163_1 := h19163c.2.1
                            have p19163_2 := h19163c.2.2.1
                            have p19163_3 := h19163c.2.2.2
                            linarith only [h18821, hlam, p19163_1]
                          · have p19163_0 := h19163c.1
                            have p19163_1 := h19163c.2.1
                            have p19163_2 := h19163c.2.2.1
                            have p19163_3 := h19163c.2.2.2
                            linarith only [hlam, p19163_0]
                    · linarith only [h16915, h18815, h18822, h18825, h18826, h18828, h18829, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h19196 | h19196
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h19197 | h19197
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h19198 | h19198
                        · rcases h0bigk with h19199c | h19199c | h19199c | h19199c | h19199c | h19199c | h19199c | h19199c | h19199c | h19199c | h19199c | h19199c | h19199c | h19199c | h19199c | h19199c | h19199c | h19199c | h19199c | h19199c | h19199c | h19199c | h19199c | h19199c | h19199c
                          · have p19199_0 := h19199c.1
                            have p19199_1 := h19199c.2.1
                            have p19199_2 := h19199c.2.2.1
                            have p19199_3 := h19199c.2.2.2
                            linarith only [hlam, p19199_0]
                          · have p19199_0 := h19199c.1
                            have p19199_1 := h19199c.2.1
                            have p19199_2 := h19199c.2.2.1
                            have p19199_3 := h19199c.2.2.2
                            linarith only [h0, hlam, p19199_1]
                          · have p19199_0 := h19199c.1
                            have p19199_1 := h19199c.2.1
                            have p19199_2 := h19199c.2.2.1
                            have p19199_3 := h19199c.2.2.2
                            linarith only [h14396, hlam, p19199_0]
                          · have p19199_0 := h19199c.1
                            have p19199_1 := h19199c.2.1
                            have p19199_2 := h19199c.2.2.1
                            have p19199_3 := h19199c.2.2.2
                            linarith only [h16915, hlam, p19199_1]
                          · have p19199_0 := h19199c.1
                            have p19199_1 := h19199c.2.1
                            have p19199_2 := h19199c.2.2.1
                            have p19199_3 := h19199c.2.2.2
                            rcases p19199_3 (m.d 0 1) (by simp) with h19204 | h19204
                            · rcases p19199_3 (m.d 0 2) (by simp) with h19205 | h19205
                              · rcases p19199_3 (m.d 0 3) (by simp) with h19206 | h19206
                                · rcases p19199_3 (m.d 0 4) (by simp) with h19207 | h19207
                                  · rcases p19199_3 (m.d 0 5) (by simp) with h19208 | h19208
                                    · linarith only [h18815, h19208, hlam]
                                    · rcases h2bigk with h19210c | h19210c | h19210c | h19210c | h19210c | h19210c | h19210c | h19210c | h19210c | h19210c | h19210c | h19210c | h19210c | h19210c | h19210c | h19210c | h19210c | h19210c | h19210c | h19210c | h19210c | h19210c | h19210c | h19210c | h19210c
                                      · have p19210_0 := h19210c.1
                                        have p19210_1 := h19210c.2.1
                                        have p19210_2 := h19210c.2.2.1
                                        have p19210_3 := h19210c.2.2.2
                                        linarith only [hlam, p19210_0]
                                      · have p19210_0 := h19210c.1
                                        have p19210_1 := h19210c.2.1
                                        have p19210_2 := h19210c.2.2.1
                                        have p19210_3 := h19210c.2.2.2
                                        linarith only [h0, hlam, p19210_1]
                                      · have p19210_0 := h19210c.1
                                        have p19210_1 := h19210c.2.1
                                        have p19210_2 := h19210c.2.2.1
                                        have p19210_3 := h19210c.2.2.2
                                        rcases p19210_3 (m.d 0 2) (by simp) with h19213 | h19213
                                        · rcases p19210_3 (m.d 1 2) (by simp) with h19214 | h19214
                                          · rcases p19210_3 (m.d 2 3) (by simp) with h19215 | h19215
                                            · linarith only [h19215, hlam, p19210_0]
                                            · rcases p19210_3 (m.d 2 4) (by simp) with h19217 | h19217
                                              · linarith only [h18817, h19217, hlam]
                                              · linarith only [h18828, h19217, hlam]
                                          · linarith only [h18822, h19214, hlam]
                                        · linarith only [h19213, hlam, p19210_0]
                                      · have p19210_0 := h19210c.1
                                        have p19210_1 := h19210c.2.1
                                        have p19210_2 := h19210c.2.2.1
                                        have p19210_3 := h19210c.2.2.2
                                        rcases p19210_3 (m.d 0 2) (by simp) with h19222 | h19222
                                        · rcases p19210_3 (m.d 1 2) (by simp) with h19223 | h19223
                                          · rcases p19210_3 (m.d 2 3) (by simp) with h19224 | h19224
                                            · linarith only [h18816, h19224, hlam]
                                            · rcases p19210_3 (m.d 2 4) (by simp) with h19226 | h19226
                                              · linarith only [h19226, hlam, p19210_0]
                                              · rcases p19210_3 (m.d 2 5) (by simp) with h19228 | h19228
                                                · linarith only [h18818, h19228, hlam]
                                                · rcases h3bigk with h19230c | h19230c | h19230c | h19230c | h19230c | h19230c | h19230c | h19230c | h19230c | h19230c | h19230c | h19230c | h19230c | h19230c | h19230c | h19230c | h19230c | h19230c | h19230c | h19230c | h19230c | h19230c | h19230c | h19230c | h19230c
                                                  · have p19230_0 := h19230c.1
                                                    have p19230_1 := h19230c.2.1
                                                    have p19230_2 := h19230c.2.2.1
                                                    have p19230_3 := h19230c.2.2.2
                                                    linarith only [hlam, p19230_0]
                                                  · have p19230_0 := h19230c.1
                                                    have p19230_1 := h19230c.2.1
                                                    have p19230_2 := h19230c.2.2.1
                                                    have p19230_3 := h19230c.2.2.2
                                                    linarith only [h14396, hlam, p19230_1]
                                                  · have p19230_0 := h19230c.1
                                                    have p19230_1 := h19230c.2.1
                                                    have p19230_2 := h19230c.2.2.1
                                                    have p19230_3 := h19230c.2.2.2
                                                    linarith only [h14396, h18822, h19196, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p19230_1]
                                                  · have p19230_0 := h19230c.1
                                                    have p19230_1 := h19230c.2.1
                                                    have p19230_2 := h19230c.2.2.1
                                                    have p19230_3 := h19230c.2.2.2
                                                    linarith only [h14396, h18822, h18828, h19196, h19198, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19230_1]
                                                  · have p19230_0 := h19230c.1
                                                    have p19230_1 := h19230c.2.1
                                                    have p19230_2 := h19230c.2.2.1
                                                    have p19230_3 := h19230c.2.2.2
                                                    rcases p19230_3 (m.d 0 3) (by simp) with h19235 | h19235
                                                    · rcases p19230_3 (m.d 1 3) (by simp) with h19236 | h19236
                                                      · rcases p19230_3 (m.d 2 3) (by simp) with h19237 | h19237
                                                        · linarith only [h18816, h19237, hlam]
                                                        · linarith only [h19196, h19237, hlam]
                                                      · linarith only [h18826, h19236, hlam]
                                                    · linarith only [h19235, hlam, p19230_0]
                                                  · have p19230_0 := h19230c.1
                                                    have p19230_1 := h19230c.2.1
                                                    have p19230_2 := h19230c.2.2.1
                                                    have p19230_3 := h19230c.2.2.2
                                                    linarith only [h14396, h18822, hc01, hc12, hlam, hphi, p19230_1]
                                                  · have p19230_0 := h19230c.1
                                                    have p19230_1 := h19230c.2.1
                                                    have p19230_2 := h19230c.2.2.1
                                                    have p19230_3 := h19230c.2.2.2
                                                    linarith only [hlam, p19230_0]
                                                  · have p19230_0 := h19230c.1
                                                    have p19230_1 := h19230c.2.1
                                                    have p19230_2 := h19230c.2.2.1
                                                    have p19230_3 := h19230c.2.2.2
                                                    linarith only [h18822, h19196, h19198, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19230_1]
                                                  · have p19230_0 := h19230c.1
                                                    have p19230_1 := h19230c.2.1
                                                    have p19230_2 := h19230c.2.2.1
                                                    have p19230_3 := h19230c.2.2.2
                                                    linarith only [h18822, h18828, h19196, h19198, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19230_1]
                                                  · have p19230_0 := h19230c.1
                                                    have p19230_1 := h19230c.2.1
                                                    have p19230_2 := h19230c.2.2.1
                                                    have p19230_3 := h19230c.2.2.2
                                                    rcases p19230_3 (m.d 0 3) (by simp) with h19246 | h19246
                                                    · linarith only [h14396, h19246, hlam]
                                                    · linarith only [h18820, h19246, hlam]
                                                  · have p19230_0 := h19230c.1
                                                    have p19230_1 := h19230c.2.1
                                                    have p19230_2 := h19230c.2.2.1
                                                    have p19230_3 := h19230c.2.2.2
                                                    linarith only [h18816, hlam, p19230_0]
                                                  · have p19230_0 := h19230c.1
                                                    have p19230_1 := h19230c.2.1
                                                    have p19230_2 := h19230c.2.2.1
                                                    have p19230_3 := h19230c.2.2.2
                                                    linarith only [h18822, hlam, p19230_0]
                                                  · have p19230_0 := h19230c.1
                                                    have p19230_1 := h19230c.2.1
                                                    have p19230_2 := h19230c.2.2.1
                                                    have p19230_3 := h19230c.2.2.2
                                                    linarith only [hlam, p19230_0]
                                                  · have p19230_0 := h19230c.1
                                                    have p19230_1 := h19230c.2.1
                                                    have p19230_2 := h19230c.2.2.1
                                                    have p19230_3 := h19230c.2.2.2
                                                    linarith only [h18828, hlam, p19230_0]
                                                  · have p19230_0 := h19230c.1
                                                    have p19230_1 := h19230c.2.1
                                                    have p19230_2 := h19230c.2.2.1
                                                    have p19230_3 := h19230c.2.2.2
                                                    linarith only [h18819, h18828, h19198, hc03, hc45, hlam, hphi, ht0b, ht5b, p19230_1]
                                                  · have p19230_0 := h19230c.1
                                                    have p19230_1 := h19230c.2.1
                                                    have p19230_2 := h19230c.2.2.1
                                                    have p19230_3 := h19230c.2.2.2
                                                    linarith only [h18819, hlam, p19230_0]
                                                  · have p19230_0 := h19230c.1
                                                    have p19230_1 := h19230c.2.1
                                                    have p19230_2 := h19230c.2.2.1
                                                    have p19230_3 := h19230c.2.2.2
                                                    linarith only [h18825, hlam, p19230_0]
                                                  · have p19230_0 := h19230c.1
                                                    have p19230_1 := h19230c.2.1
                                                    have p19230_2 := h19230c.2.2.1
                                                    have p19230_3 := h19230c.2.2.2
                                                    linarith only [h18819, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19230_1]
                                                  · have p19230_0 := h19230c.1
                                                    have p19230_1 := h19230c.2.1
                                                    have p19230_2 := h19230c.2.2.1
                                                    have p19230_3 := h19230c.2.2.2
                                                    linarith only [hlam, p19230_0]
                                                  · have p19230_0 := h19230c.1
                                                    have p19230_1 := h19230c.2.1
                                                    have p19230_2 := h19230c.2.2.1
                                                    have p19230_3 := h19230c.2.2.2
                                                    linarith only [h14396, h18819, h18822, h19198, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19230_1]
                                                  · have p19230_0 := h19230c.1
                                                    have p19230_1 := h19230c.2.1
                                                    have p19230_2 := h19230c.2.2.1
                                                    have p19230_3 := h19230c.2.2.2
                                                    linarith only [h18820, hlam, p19230_0]
                                                  · have p19230_0 := h19230c.1
                                                    have p19230_1 := h19230c.2.1
                                                    have p19230_2 := h19230c.2.2.1
                                                    have p19230_3 := h19230c.2.2.2
                                                    linarith only [h18826, hlam, p19230_0]
                                                  · have p19230_0 := h19230c.1
                                                    have p19230_1 := h19230c.2.1
                                                    have p19230_2 := h19230c.2.2.1
                                                    have p19230_3 := h19230c.2.2.2
                                                    linarith only [h19196, hlam, p19230_0]
                                                  · have p19230_0 := h19230c.1
                                                    have p19230_1 := h19230c.2.1
                                                    have p19230_2 := h19230c.2.2.1
                                                    have p19230_3 := h19230c.2.2.2
                                                    linarith only [h19198, hlam, p19230_0]
                                                  · have p19230_0 := h19230c.1
                                                    have p19230_1 := h19230c.2.1
                                                    have p19230_2 := h19230c.2.2.1
                                                    have p19230_3 := h19230c.2.2.2
                                                    linarith only [hlam, p19230_0]
                                          · linarith only [h18823, h19223, hlam]
                                        · linarith only [h19222, hlam, p19210_0]
                                      · have p19210_0 := h19210c.1
                                        have p19210_1 := h19210c.2.1
                                        have p19210_2 := h19210c.2.2.1
                                        have p19210_3 := h19210c.2.2.2
                                        rcases p19210_3 (m.d 0 2) (by simp) with h19266 | h19266
                                        · rcases p19210_3 (m.d 1 2) (by simp) with h19267 | h19267
                                          · rcases p19210_3 (m.d 2 3) (by simp) with h19268 | h19268
                                            · linarith only [h18816, h19268, hlam]
                                            · linarith only [h19196, h19268, hlam]
                                          · linarith only [h18824, h19267, hlam]
                                        · linarith only [h19266, hlam, p19210_0]
                                      · have p19210_0 := h19210c.1
                                        have p19210_1 := h19210c.2.1
                                        have p19210_2 := h19210c.2.2.1
                                        have p19210_3 := h19210c.2.2.2
                                        linarith only [h18816, h18819, h18828, h19196, h19198, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19210_1]
                                      · have p19210_0 := h19210c.1
                                        have p19210_1 := h19210c.2.1
                                        have p19210_2 := h19210c.2.2.1
                                        have p19210_3 := h19210c.2.2.2
                                        linarith only [hlam, p19210_0]
                                      · have p19210_0 := h19210c.1
                                        have p19210_1 := h19210c.2.1
                                        have p19210_2 := h19210c.2.2.1
                                        have p19210_3 := h19210c.2.2.2
                                        rcases p19210_3 (m.d 0 2) (by simp) with h19275 | h19275
                                        · linarith only [h0, h19275, hlam]
                                        · linarith only [h18816, h19275, hlam]
                                      · have p19210_0 := h19210c.1
                                        have p19210_1 := h19210c.2.1
                                        have p19210_2 := h19210c.2.2.1
                                        have p19210_3 := h19210c.2.2.2
                                        rcases p19210_3 (m.d 0 2) (by simp) with h19278 | h19278
                                        · linarith only [h0, h19278, hlam]
                                        · linarith only [h18817, h19278, hlam]
                                      · have p19210_0 := h19210c.1
                                        have p19210_1 := h19210c.2.1
                                        have p19210_2 := h19210c.2.2.1
                                        have p19210_3 := h19210c.2.2.2
                                        linarith only [h0, h18815, h18824, hlam, p19199_1, p19210_2]
                                      · have p19210_0 := h19210c.1
                                        have p19210_1 := h19210c.2.1
                                        have p19210_2 := h19210c.2.2.1
                                        have p19210_3 := h19210c.2.2.2
                                        linarith only [h18816, hlam, p19210_0]
                                      · have p19210_0 := h19210c.1
                                        have p19210_1 := h19210c.2.1
                                        have p19210_2 := h19210c.2.2.1
                                        have p19210_3 := h19210c.2.2.2
                                        linarith only [h18822, hlam, p19210_0]
                                      · have p19210_0 := h19210c.1
                                        have p19210_1 := h19210c.2.1
                                        have p19210_2 := h19210c.2.2.1
                                        have p19210_3 := h19210c.2.2.2
                                        linarith only [hlam, p19210_0]
                                      · have p19210_0 := h19210c.1
                                        have p19210_1 := h19210c.2.1
                                        have p19210_2 := h19210c.2.2.1
                                        have p19210_3 := h19210c.2.2.2
                                        linarith only [h18828, hlam, p19210_0]
                                      · have p19210_0 := h19210c.1
                                        have p19210_1 := h19210c.2.1
                                        have p19210_2 := h19210c.2.2.1
                                        have p19210_3 := h19210c.2.2.2
                                        linarith only [h18816, h18819, h18828, hc02, hc25, hlam, hphi, ht0b, ht5b, p19210_1]
                                      · have p19210_0 := h19210c.1
                                        have p19210_1 := h19210c.2.1
                                        have p19210_2 := h19210c.2.2.1
                                        have p19210_3 := h19210c.2.2.2
                                        linarith only [h18817, hlam, p19210_0]
                                      · have p19210_0 := h19210c.1
                                        have p19210_1 := h19210c.2.1
                                        have p19210_2 := h19210c.2.2.1
                                        have p19210_3 := h19210c.2.2.2
                                        linarith only [h18823, hlam, p19210_0]
                                      · have p19210_0 := h19210c.1
                                        have p19210_1 := h19210c.2.1
                                        have p19210_2 := h19210c.2.2.1
                                        have p19210_3 := h19210c.2.2.2
                                        linarith only [h0, h18817, h19196, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p19210_1]
                                      · have p19210_0 := h19210c.1
                                        have p19210_1 := h19210c.2.1
                                        have p19210_2 := h19210c.2.2.1
                                        have p19210_3 := h19210c.2.2.2
                                        linarith only [hlam, p19210_0]
                                      · have p19210_0 := h19210c.1
                                        have p19210_1 := h19210c.2.1
                                        have p19210_2 := h19210c.2.2.1
                                        have p19210_3 := h19210c.2.2.2
                                        rcases p19210_3 (m.d 0 2) (by simp) with h19291 | h19291
                                        · rcases p19210_3 (m.d 1 2) (by simp) with h19292 | h19292
                                          · rcases p19210_3 (m.d 2 3) (by simp) with h19293 | h19293
                                            · linarith only [h18828, h19293, hlam]
                                            · linarith only [h19196, h19293, hlam]
                                          · linarith only [h18824, h19292, hlam]
                                        · linarith only [h18818, h19291, hlam]
                                      · have p19210_0 := h19210c.1
                                        have p19210_1 := h19210c.2.1
                                        have p19210_2 := h19210c.2.2.1
                                        have p19210_3 := h19210c.2.2.2
                                        linarith only [h18818, hlam, p19210_0]
                                      · have p19210_0 := h19210c.1
                                        have p19210_1 := h19210c.2.1
                                        have p19210_2 := h19210c.2.2.1
                                        have p19210_3 := h19210c.2.2.2
                                        linarith only [h18824, hlam, p19210_0]
                                      · have p19210_0 := h19210c.1
                                        have p19210_1 := h19210c.2.1
                                        have p19210_2 := h19210c.2.2.1
                                        have p19210_3 := h19210c.2.2.2
                                        linarith only [h19196, hlam, p19210_1]
                                      · have p19210_0 := h19210c.1
                                        have p19210_1 := h19210c.2.1
                                        have p19210_2 := h19210c.2.2.1
                                        have p19210_3 := h19210c.2.2.2
                                        linarith only [h19197, hlam, p19210_0]
                                      · have p19210_0 := h19210c.1
                                        have p19210_1 := h19210c.2.1
                                        have p19210_2 := h19210c.2.2.1
                                        have p19210_3 := h19210c.2.2.2
                                        linarith only [hlam, p19210_0]
                                  · linarith only [h18821, h19207, hlam]
                                · linarith only [h18820, h19206, hlam]
                              · linarith only [h18818, h19205, hlam]
                            · linarith only [h18815, h19204, hlam]
                          · have p19199_0 := h19199c.1
                            have p19199_1 := h19199c.2.1
                            have p19199_2 := h19199c.2.2.1
                            have p19199_3 := h19199c.2.2.2
                            rcases p19199_3 (m.d 0 1) (by simp) with h19307 | h19307
                            · linarith only [h0, h19307, hlam]
                            · rcases p19199_3 (m.d 0 2) (by simp) with h19309 | h19309
                              · rcases p19199_3 (m.d 0 3) (by simp) with h19310 | h19310
                                · linarith only [h18816, h19310, hlam]
                                · linarith only [h14396, h19310, hlam]
                              · linarith only [h0, h19309, hlam]
                          · have p19199_0 := h19199c.1
                            have p19199_1 := h19199c.2.1
                            have p19199_2 := h19199c.2.2.1
                            have p19199_3 := h19199c.2.2.2
                            linarith only [hlam, p19199_0]
                          · have p19199_0 := h19199c.1
                            have p19199_1 := h19199c.2.1
                            have p19199_2 := h19199c.2.2.1
                            have p19199_3 := h19199c.2.2.2
                            linarith only [h0, h18819, h18828, h19196, h19198, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19199_1]
                          · have p19199_0 := h19199c.1
                            have p19199_1 := h19199c.2.1
                            have p19199_2 := h19199c.2.2.1
                            have p19199_3 := h19199c.2.2.2
                            linarith only [h0, h18819, h18828, h19196, h19198, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19199_1]
                          · have p19199_0 := h19199c.1
                            have p19199_1 := h19199c.2.1
                            have p19199_2 := h19199c.2.2.1
                            have p19199_3 := h19199c.2.2.2
                            rcases p19199_3 (m.d 0 1) (by simp) with h19317 | h19317
                            · linarith only [h0, h19317, hlam]
                            · linarith only [h18815, h19317, hlam]
                          · have p19199_0 := h19199c.1
                            have p19199_1 := h19199c.2.1
                            have p19199_2 := h19199c.2.2.1
                            have p19199_3 := h19199c.2.2.2
                            rcases p19199_3 (m.d 0 1) (by simp) with h19320 | h19320
                            · linarith only [h14396, h19320, hlam]
                            · rcases p19199_3 (m.d 0 2) (by simp) with h19322 | h19322
                              · rcases p19199_3 (m.d 0 3) (by simp) with h19323 | h19323
                                · rcases p19199_3 (m.d 0 4) (by simp) with h19324 | h19324
                                  · linarith only [h18819, h19324, hlam]
                                  · linarith only [h16915, h19324, hlam]
                                · linarith only [h14396, h19323, hlam]
                              · linarith only [h0, h19322, hlam]
                          · have p19199_0 := h19199c.1
                            have p19199_1 := h19199c.2.1
                            have p19199_2 := h19199c.2.2.1
                            have p19199_3 := h19199c.2.2.2
                            linarith only [h18816, hlam, p19199_1]
                          · have p19199_0 := h19199c.1
                            have p19199_1 := h19199c.2.1
                            have p19199_2 := h19199c.2.2.1
                            have p19199_3 := h19199c.2.2.2
                            linarith only [hlam, p19199_0]
                          · have p19199_0 := h19199c.1
                            have p19199_1 := h19199c.2.1
                            have p19199_2 := h19199c.2.2.1
                            have p19199_3 := h19199c.2.2.2
                            linarith only [h18819, h18828, h19196, h19198, hc03, hc45, hlam, hphi, ht0b, ht5b, p19199_1]
                          · have p19199_0 := h19199c.1
                            have p19199_1 := h19199c.2.1
                            have p19199_2 := h19199c.2.2.1
                            have p19199_3 := h19199c.2.2.2
                            rcases p19199_3 (m.d 0 1) (by simp) with h19332 | h19332
                            · linarith only [h14396, h19332, hlam]
                            · linarith only [h18815, h19332, hlam]
                          · have p19199_0 := h19199c.1
                            have p19199_1 := h19199c.2.1
                            have p19199_2 := h19199c.2.2.1
                            have p19199_3 := h19199c.2.2.2
                            rcases p19199_3 (m.d 0 1) (by simp) with h19335 | h19335
                            · linarith only [h16915, h19335, hlam]
                            · rcases p19199_3 (m.d 0 2) (by simp) with h19337 | h19337
                              · rcases p19199_3 (m.d 0 3) (by simp) with h19338 | h19338
                                · rcases p19199_3 (m.d 0 4) (by simp) with h19339 | h19339
                                  · rcases p19199_3 (m.d 0 5) (by simp) with h19340 | h19340
                                    · linarith only [h18821, h19340, hlam]
                                    · rcases h2bigk with h19342c | h19342c | h19342c | h19342c | h19342c | h19342c | h19342c | h19342c | h19342c | h19342c | h19342c | h19342c | h19342c | h19342c | h19342c | h19342c | h19342c | h19342c | h19342c | h19342c | h19342c | h19342c | h19342c | h19342c | h19342c
                                      · have p19342_0 := h19342c.1
                                        have p19342_1 := h19342c.2.1
                                        have p19342_2 := h19342c.2.2.1
                                        have p19342_3 := h19342c.2.2.2
                                        linarith only [hlam, p19342_0]
                                      · have p19342_0 := h19342c.1
                                        have p19342_1 := h19342c.2.1
                                        have p19342_2 := h19342c.2.2.1
                                        have p19342_3 := h19342c.2.2.2
                                        linarith only [h0, hlam, p19342_1]
                                      · have p19342_0 := h19342c.1
                                        have p19342_1 := h19342c.2.1
                                        have p19342_2 := h19342c.2.2.1
                                        have p19342_3 := h19342c.2.2.2
                                        rcases p19342_3 (m.d 0 2) (by simp) with h19345 | h19345
                                        · rcases p19342_3 (m.d 1 2) (by simp) with h19346 | h19346
                                          · rcases p19342_3 (m.d 2 3) (by simp) with h19347 | h19347
                                            · linarith only [h19347, hlam, p19342_0]
                                            · rcases p19342_3 (m.d 2 4) (by simp) with h19349 | h19349
                                              · linarith only [h18817, h19349, hlam]
                                              · linarith only [h18828, h19349, hlam]
                                          · linarith only [h18822, h19346, hlam]
                                        · linarith only [h19345, hlam, p19342_0]
                                      · have p19342_0 := h19342c.1
                                        have p19342_1 := h19342c.2.1
                                        have p19342_2 := h19342c.2.2.1
                                        have p19342_3 := h19342c.2.2.2
                                        rcases p19342_3 (m.d 0 2) (by simp) with h19354 | h19354
                                        · rcases p19342_3 (m.d 1 2) (by simp) with h19355 | h19355
                                          · rcases p19342_3 (m.d 2 3) (by simp) with h19356 | h19356
                                            · linarith only [h18816, h19356, hlam]
                                            · rcases p19342_3 (m.d 2 4) (by simp) with h19358 | h19358
                                              · linarith only [h19358, hlam, p19342_0]
                                              · rcases p19342_3 (m.d 2 5) (by simp) with h19360 | h19360
                                                · linarith only [h18818, h19360, hlam]
                                                · rcases h3bigk with h19362c | h19362c | h19362c | h19362c | h19362c | h19362c | h19362c | h19362c | h19362c | h19362c | h19362c | h19362c | h19362c | h19362c | h19362c | h19362c | h19362c | h19362c | h19362c | h19362c | h19362c | h19362c | h19362c | h19362c | h19362c
                                                  · have p19362_0 := h19362c.1
                                                    have p19362_1 := h19362c.2.1
                                                    have p19362_2 := h19362c.2.2.1
                                                    have p19362_3 := h19362c.2.2.2
                                                    linarith only [hlam, p19362_0]
                                                  · have p19362_0 := h19362c.1
                                                    have p19362_1 := h19362c.2.1
                                                    have p19362_2 := h19362c.2.2.1
                                                    have p19362_3 := h19362c.2.2.2
                                                    linarith only [h14396, hlam, p19362_1]
                                                  · have p19362_0 := h19362c.1
                                                    have p19362_1 := h19362c.2.1
                                                    have p19362_2 := h19362c.2.2.1
                                                    have p19362_3 := h19362c.2.2.2
                                                    linarith only [h14396, h18822, h19196, h19198, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19362_1]
                                                  · have p19362_0 := h19362c.1
                                                    have p19362_1 := h19362c.2.1
                                                    have p19362_2 := h19362c.2.2.1
                                                    have p19362_3 := h19362c.2.2.2
                                                    linarith only [h14396, h18822, h18828, h19196, h19198, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19362_1]
                                                  · have p19362_0 := h19362c.1
                                                    have p19362_1 := h19362c.2.1
                                                    have p19362_2 := h19362c.2.2.1
                                                    have p19362_3 := h19362c.2.2.2
                                                    rcases p19362_3 (m.d 0 3) (by simp) with h19367 | h19367
                                                    · rcases p19362_3 (m.d 1 3) (by simp) with h19368 | h19368
                                                      · rcases p19362_3 (m.d 2 3) (by simp) with h19369 | h19369
                                                        · linarith only [h18816, h19369, hlam]
                                                        · linarith only [h19196, h19369, hlam]
                                                      · linarith only [h18826, h19368, hlam]
                                                    · linarith only [h19367, hlam, p19362_0]
                                                  · have p19362_0 := h19362c.1
                                                    have p19362_1 := h19362c.2.1
                                                    have p19362_2 := h19362c.2.2.1
                                                    have p19362_3 := h19362c.2.2.2
                                                    linarith only [h14396, h18815, h18822, h18824, h19196, h19198, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19362_1]
                                                  · have p19362_0 := h19362c.1
                                                    have p19362_1 := h19362c.2.1
                                                    have p19362_2 := h19362c.2.2.1
                                                    have p19362_3 := h19362c.2.2.2
                                                    linarith only [hlam, p19362_0]
                                                  · have p19362_0 := h19362c.1
                                                    have p19362_1 := h19362c.2.1
                                                    have p19362_2 := h19362c.2.2.1
                                                    have p19362_3 := h19362c.2.2.2
                                                    linarith only [h18822, h19196, h19198, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19362_1]
                                                  · have p19362_0 := h19362c.1
                                                    have p19362_1 := h19362c.2.1
                                                    have p19362_2 := h19362c.2.2.1
                                                    have p19362_3 := h19362c.2.2.2
                                                    linarith only [h18822, h18828, h19196, h19198, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19362_1]
                                                  · have p19362_0 := h19362c.1
                                                    have p19362_1 := h19362c.2.1
                                                    have p19362_2 := h19362c.2.2.1
                                                    have p19362_3 := h19362c.2.2.2
                                                    rcases p19362_3 (m.d 0 3) (by simp) with h19378 | h19378
                                                    · linarith only [h14396, h19378, hlam]
                                                    · linarith only [h18820, h19378, hlam]
                                                  · have p19362_0 := h19362c.1
                                                    have p19362_1 := h19362c.2.1
                                                    have p19362_2 := h19362c.2.2.1
                                                    have p19362_3 := h19362c.2.2.2
                                                    linarith only [h18816, hlam, p19362_0]
                                                  · have p19362_0 := h19362c.1
                                                    have p19362_1 := h19362c.2.1
                                                    have p19362_2 := h19362c.2.2.1
                                                    have p19362_3 := h19362c.2.2.2
                                                    linarith only [h18822, hlam, p19362_0]
                                                  · have p19362_0 := h19362c.1
                                                    have p19362_1 := h19362c.2.1
                                                    have p19362_2 := h19362c.2.2.1
                                                    have p19362_3 := h19362c.2.2.2
                                                    linarith only [hlam, p19362_0]
                                                  · have p19362_0 := h19362c.1
                                                    have p19362_1 := h19362c.2.1
                                                    have p19362_2 := h19362c.2.2.1
                                                    have p19362_3 := h19362c.2.2.2
                                                    linarith only [h18828, hlam, p19362_0]
                                                  · have p19362_0 := h19362c.1
                                                    have p19362_1 := h19362c.2.1
                                                    have p19362_2 := h19362c.2.2.1
                                                    have p19362_3 := h19362c.2.2.2
                                                    linarith only [h18828, h19198, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p19362_1]
                                                  · have p19362_0 := h19362c.1
                                                    have p19362_1 := h19362c.2.1
                                                    have p19362_2 := h19362c.2.2.1
                                                    have p19362_3 := h19362c.2.2.2
                                                    linarith only [h18819, hlam, p19362_0]
                                                  · have p19362_0 := h19362c.1
                                                    have p19362_1 := h19362c.2.1
                                                    have p19362_2 := h19362c.2.2.1
                                                    have p19362_3 := h19362c.2.2.2
                                                    linarith only [h18825, hlam, p19362_0]
                                                  · have p19362_0 := h19362c.1
                                                    have p19362_1 := h19362c.2.1
                                                    have p19362_2 := h19362c.2.2.1
                                                    have p19362_3 := h19362c.2.2.2
                                                    linarith only [hc23, hc34, hlam, hphi, p19362_1]
                                                  · have p19362_0 := h19362c.1
                                                    have p19362_1 := h19362c.2.1
                                                    have p19362_2 := h19362c.2.2.1
                                                    have p19362_3 := h19362c.2.2.2
                                                    linarith only [hlam, p19362_0]
                                                  · have p19362_0 := h19362c.1
                                                    have p19362_1 := h19362c.2.1
                                                    have p19362_2 := h19362c.2.2.1
                                                    have p19362_3 := h19362c.2.2.2
                                                    linarith only [h14396, h18819, h18822, h19198, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19362_1]
                                                  · have p19362_0 := h19362c.1
                                                    have p19362_1 := h19362c.2.1
                                                    have p19362_2 := h19362c.2.2.1
                                                    have p19362_3 := h19362c.2.2.2
                                                    linarith only [h18820, hlam, p19362_0]
                                                  · have p19362_0 := h19362c.1
                                                    have p19362_1 := h19362c.2.1
                                                    have p19362_2 := h19362c.2.2.1
                                                    have p19362_3 := h19362c.2.2.2
                                                    linarith only [h18826, hlam, p19362_0]
                                                  · have p19362_0 := h19362c.1
                                                    have p19362_1 := h19362c.2.1
                                                    have p19362_2 := h19362c.2.2.1
                                                    have p19362_3 := h19362c.2.2.2
                                                    linarith only [h19196, hlam, p19362_0]
                                                  · have p19362_0 := h19362c.1
                                                    have p19362_1 := h19362c.2.1
                                                    have p19362_2 := h19362c.2.2.1
                                                    have p19362_3 := h19362c.2.2.2
                                                    linarith only [h19198, hlam, p19362_0]
                                                  · have p19362_0 := h19362c.1
                                                    have p19362_1 := h19362c.2.1
                                                    have p19362_2 := h19362c.2.2.1
                                                    have p19362_3 := h19362c.2.2.2
                                                    linarith only [hlam, p19362_0]
                                          · linarith only [h18823, h19355, hlam]
                                        · linarith only [h19354, hlam, p19342_0]
                                      · have p19342_0 := h19342c.1
                                        have p19342_1 := h19342c.2.1
                                        have p19342_2 := h19342c.2.2.1
                                        have p19342_3 := h19342c.2.2.2
                                        linarith only [h18815, h18817, h18824, hlam, p19199_1, p19342_2]
                                      · have p19342_0 := h19342c.1
                                        have p19342_1 := h19342c.2.1
                                        have p19342_2 := h19342c.2.2.1
                                        have p19342_3 := h19342c.2.2.2
                                        linarith only [h18816, h19196, h19198, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19342_1]
                                      · have p19342_0 := h19342c.1
                                        have p19342_1 := h19342c.2.1
                                        have p19342_2 := h19342c.2.2.1
                                        have p19342_3 := h19342c.2.2.2
                                        linarith only [hlam, p19342_0]
                                      · have p19342_0 := h19342c.1
                                        have p19342_1 := h19342c.2.1
                                        have p19342_2 := h19342c.2.2.1
                                        have p19342_3 := h19342c.2.2.2
                                        rcases p19342_3 (m.d 0 2) (by simp) with h19401 | h19401
                                        · linarith only [h0, h19401, hlam]
                                        · linarith only [h18816, h19401, hlam]
                                      · have p19342_0 := h19342c.1
                                        have p19342_1 := h19342c.2.1
                                        have p19342_2 := h19342c.2.2.1
                                        have p19342_3 := h19342c.2.2.2
                                        rcases p19342_3 (m.d 0 2) (by simp) with h19404 | h19404
                                        · linarith only [h0, h19404, hlam]
                                        · linarith only [h18817, h19404, hlam]
                                      · have p19342_0 := h19342c.1
                                        have p19342_1 := h19342c.2.1
                                        have p19342_2 := h19342c.2.2.1
                                        have p19342_3 := h19342c.2.2.2
                                        linarith only [h0, h18815, h18816, h18819, h18824, hlam, p19199_1, p19342_2]
                                      · have p19342_0 := h19342c.1
                                        have p19342_1 := h19342c.2.1
                                        have p19342_2 := h19342c.2.2.1
                                        have p19342_3 := h19342c.2.2.2
                                        linarith only [h18816, hlam, p19342_0]
                                      · have p19342_0 := h19342c.1
                                        have p19342_1 := h19342c.2.1
                                        have p19342_2 := h19342c.2.2.1
                                        have p19342_3 := h19342c.2.2.2
                                        linarith only [h18822, hlam, p19342_0]
                                      · have p19342_0 := h19342c.1
                                        have p19342_1 := h19342c.2.1
                                        have p19342_2 := h19342c.2.2.1
                                        have p19342_3 := h19342c.2.2.2
                                        linarith only [hlam, p19342_0]
                                      · have p19342_0 := h19342c.1
                                        have p19342_1 := h19342c.2.1
                                        have p19342_2 := h19342c.2.2.1
                                        have p19342_3 := h19342c.2.2.2
                                        linarith only [h18828, hlam, p19342_0]
                                      · have p19342_0 := h19342c.1
                                        have p19342_1 := h19342c.2.1
                                        have p19342_2 := h19342c.2.2.1
                                        have p19342_3 := h19342c.2.2.2
                                        linarith only [h18816, h18819, h18828, h19196, h19198, hc02, hc45, hlam, hphi, ht0b, ht5b, p19342_1]
                                      · have p19342_0 := h19342c.1
                                        have p19342_1 := h19342c.2.1
                                        have p19342_2 := h19342c.2.2.1
                                        have p19342_3 := h19342c.2.2.2
                                        linarith only [h18817, hlam, p19342_0]
                                      · have p19342_0 := h19342c.1
                                        have p19342_1 := h19342c.2.1
                                        have p19342_2 := h19342c.2.2.1
                                        have p19342_3 := h19342c.2.2.2
                                        linarith only [h18823, hlam, p19342_0]
                                      · have p19342_0 := h19342c.1
                                        have p19342_1 := h19342c.2.1
                                        have p19342_2 := h19342c.2.2.1
                                        have p19342_3 := h19342c.2.2.2
                                        linarith only [h0, h18816, h18819, h18828, h19196, h19198, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19342_1]
                                      · have p19342_0 := h19342c.1
                                        have p19342_1 := h19342c.2.1
                                        have p19342_2 := h19342c.2.2.1
                                        have p19342_3 := h19342c.2.2.2
                                        linarith only [hlam, p19342_0]
                                      · have p19342_0 := h19342c.1
                                        have p19342_1 := h19342c.2.1
                                        have p19342_2 := h19342c.2.2.1
                                        have p19342_3 := h19342c.2.2.2
                                        rcases p19342_3 (m.d 0 2) (by simp) with h19417 | h19417
                                        · rcases p19342_3 (m.d 1 2) (by simp) with h19418 | h19418
                                          · rcases p19342_3 (m.d 2 3) (by simp) with h19419 | h19419
                                            · linarith only [h18828, h19419, hlam]
                                            · linarith only [h19196, h19419, hlam]
                                          · linarith only [h18824, h19418, hlam]
                                        · linarith only [h18818, h19417, hlam]
                                      · have p19342_0 := h19342c.1
                                        have p19342_1 := h19342c.2.1
                                        have p19342_2 := h19342c.2.2.1
                                        have p19342_3 := h19342c.2.2.2
                                        linarith only [h18818, hlam, p19342_0]
                                      · have p19342_0 := h19342c.1
                                        have p19342_1 := h19342c.2.1
                                        have p19342_2 := h19342c.2.2.1
                                        have p19342_3 := h19342c.2.2.2
                                        linarith only [h18824, hlam, p19342_0]
                                      · have p19342_0 := h19342c.1
                                        have p19342_1 := h19342c.2.1
                                        have p19342_2 := h19342c.2.2.1
                                        have p19342_3 := h19342c.2.2.2
                                        linarith only [h19196, hlam, p19342_1]
                                      · have p19342_0 := h19342c.1
                                        have p19342_1 := h19342c.2.1
                                        have p19342_2 := h19342c.2.2.1
                                        have p19342_3 := h19342c.2.2.2
                                        linarith only [h19197, hlam, p19342_0]
                                      · have p19342_0 := h19342c.1
                                        have p19342_1 := h19342c.2.1
                                        have p19342_2 := h19342c.2.2.1
                                        have p19342_3 := h19342c.2.2.2
                                        linarith only [hlam, p19342_0]
                                  · linarith only [h16915, h19339, hlam]
                                · linarith only [h14396, h19338, hlam]
                              · linarith only [h0, h19337, hlam]
                          · have p19199_0 := h19199c.1
                            have p19199_1 := h19199c.2.1
                            have p19199_2 := h19199c.2.2.1
                            have p19199_3 := h19199c.2.2.2
                            linarith only [h18817, hlam, p19199_0]
                          · have p19199_0 := h19199c.1
                            have p19199_1 := h19199c.2.1
                            have p19199_2 := h19199c.2.2.1
                            have p19199_3 := h19199c.2.2.2
                            linarith only [h18819, hlam, p19199_0]
                          · have p19199_0 := h19199c.1
                            have p19199_1 := h19199c.2.1
                            have p19199_2 := h19199c.2.2.1
                            have p19199_3 := h19199c.2.2.2
                            linarith only [hlam, p19199_0]
                          · have p19199_0 := h19199c.1
                            have p19199_1 := h19199c.2.1
                            have p19199_2 := h19199c.2.2.1
                            have p19199_3 := h19199c.2.2.2
                            rcases p19199_3 (m.d 0 1) (by simp) with h19435 | h19435
                            · linarith only [h16915, h19435, hlam]
                            · linarith only [h18815, h19435, hlam]
                          · have p19199_0 := h19199c.1
                            have p19199_1 := h19199c.2.1
                            have p19199_2 := h19199c.2.2.1
                            have p19199_3 := h19199c.2.2.2
                            linarith only [h18815, hlam, p19199_0]
                          · have p19199_0 := h19199c.1
                            have p19199_1 := h19199c.2.1
                            have p19199_2 := h19199c.2.2.1
                            have p19199_3 := h19199c.2.2.2
                            linarith only [h18818, hlam, p19199_1]
                          · have p19199_0 := h19199c.1
                            have p19199_1 := h19199c.2.1
                            have p19199_2 := h19199c.2.2.1
                            have p19199_3 := h19199c.2.2.2
                            linarith only [h18820, hlam, p19199_0]
                          · have p19199_0 := h19199c.1
                            have p19199_1 := h19199c.2.1
                            have p19199_2 := h19199c.2.2.1
                            have p19199_3 := h19199c.2.2.2
                            linarith only [h18821, hlam, p19199_1]
                          · have p19199_0 := h19199c.1
                            have p19199_1 := h19199c.2.1
                            have p19199_2 := h19199c.2.2.1
                            have p19199_3 := h19199c.2.2.2
                            linarith only [hlam, p19199_0]
                        · linarith only [h18815, h18827, h18828, h19196, h19198, hc01, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h16915, h18815, h18822, h18825, h18827, h18828, h19196, h19197, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h19445 | h19445
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h19446 | h19446
                        · rcases h0bigk with h19447c | h19447c | h19447c | h19447c | h19447c | h19447c | h19447c | h19447c | h19447c | h19447c | h19447c | h19447c | h19447c | h19447c | h19447c | h19447c | h19447c | h19447c | h19447c | h19447c | h19447c | h19447c | h19447c | h19447c | h19447c
                          · have p19447_0 := h19447c.1
                            have p19447_1 := h19447c.2.1
                            have p19447_2 := h19447c.2.2.1
                            have p19447_3 := h19447c.2.2.2
                            linarith only [hlam, p19447_0]
                          · have p19447_0 := h19447c.1
                            have p19447_1 := h19447c.2.1
                            have p19447_2 := h19447c.2.2.1
                            have p19447_3 := h19447c.2.2.2
                            linarith only [h0, hlam, p19447_1]
                          · have p19447_0 := h19447c.1
                            have p19447_1 := h19447c.2.1
                            have p19447_2 := h19447c.2.2.1
                            have p19447_3 := h19447c.2.2.2
                            linarith only [h14396, hlam, p19447_0]
                          · have p19447_0 := h19447c.1
                            have p19447_1 := h19447c.2.1
                            have p19447_2 := h19447c.2.2.1
                            have p19447_3 := h19447c.2.2.2
                            linarith only [h16915, hlam, p19447_1]
                          · have p19447_0 := h19447c.1
                            have p19447_1 := h19447c.2.1
                            have p19447_2 := h19447c.2.2.1
                            have p19447_3 := h19447c.2.2.2
                            linarith only [h16915, h18815, h18822, h18825, h18826, h19196, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p19447_1]
                          · have p19447_0 := h19447c.1
                            have p19447_1 := h19447c.2.1
                            have p19447_2 := h19447c.2.2.1
                            have p19447_3 := h19447c.2.2.2
                            linarith only [h18815, h18826, h19196, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19447_1]
                          · have p19447_0 := h19447c.1
                            have p19447_1 := h19447c.2.1
                            have p19447_2 := h19447c.2.2.1
                            have p19447_3 := h19447c.2.2.2
                            linarith only [hlam, p19447_0]
                          · have p19447_0 := h19447c.1
                            have p19447_1 := h19447c.2.1
                            have p19447_2 := h19447c.2.2.1
                            have p19447_3 := h19447c.2.2.2
                            linarith only [h0, h14396, h18815, h18826, h19196, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p19447_1]
                          · have p19447_0 := h19447c.1
                            have p19447_1 := h19447c.2.1
                            have p19447_2 := h19447c.2.2.1
                            have p19447_3 := h19447c.2.2.2
                            linarith only [h0, h16915, h18815, h18826, h19196, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p19447_1]
                          · have p19447_0 := h19447c.1
                            have p19447_1 := h19447c.2.1
                            have p19447_2 := h19447c.2.2.1
                            have p19447_3 := h19447c.2.2.2
                            rcases p19447_3 (m.d 0 1) (by simp) with h19457 | h19457
                            · linarith only [h0, h19457, hlam]
                            · linarith only [h18815, h19457, hlam]
                          · have p19447_0 := h19447c.1
                            have p19447_1 := h19447c.2.1
                            have p19447_2 := h19447c.2.2.1
                            have p19447_3 := h19447c.2.2.2
                            linarith only [h18815, h18826, h19196, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19447_1]
                          · have p19447_0 := h19447c.1
                            have p19447_1 := h19447c.2.1
                            have p19447_2 := h19447c.2.2.1
                            have p19447_3 := h19447c.2.2.2
                            linarith only [h18816, hlam, p19447_1]
                          · have p19447_0 := h19447c.1
                            have p19447_1 := h19447c.2.1
                            have p19447_2 := h19447c.2.2.1
                            have p19447_3 := h19447c.2.2.2
                            linarith only [hlam, p19447_0]
                          · have p19447_0 := h19447c.1
                            have p19447_1 := h19447c.2.1
                            have p19447_2 := h19447c.2.2.1
                            have p19447_3 := h19447c.2.2.2
                            linarith only [h14396, h16915, h18815, h18822, h18826, h19196, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p19447_1]
                          · have p19447_0 := h19447c.1
                            have p19447_1 := h19447c.2.1
                            have p19447_2 := h19447c.2.2.1
                            have p19447_3 := h19447c.2.2.2
                            rcases p19447_3 (m.d 0 1) (by simp) with h19464 | h19464
                            · linarith only [h14396, h19464, hlam]
                            · linarith only [h18815, h19464, hlam]
                          · have p19447_0 := h19447c.1
                            have p19447_1 := h19447c.2.1
                            have p19447_2 := h19447c.2.2.1
                            have p19447_3 := h19447c.2.2.2
                            linarith only [h18815, h18826, h19196, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19447_1]
                          · have p19447_0 := h19447c.1
                            have p19447_1 := h19447c.2.1
                            have p19447_2 := h19447c.2.2.1
                            have p19447_3 := h19447c.2.2.2
                            linarith only [h18817, hlam, p19447_0]
                          · have p19447_0 := h19447c.1
                            have p19447_1 := h19447c.2.1
                            have p19447_2 := h19447c.2.2.1
                            have p19447_3 := h19447c.2.2.2
                            linarith only [h18819, hlam, p19447_0]
                          · have p19447_0 := h19447c.1
                            have p19447_1 := h19447c.2.1
                            have p19447_2 := h19447c.2.2.1
                            have p19447_3 := h19447c.2.2.2
                            linarith only [hlam, p19447_0]
                          · have p19447_0 := h19447c.1
                            have p19447_1 := h19447c.2.1
                            have p19447_2 := h19447c.2.2.1
                            have p19447_3 := h19447c.2.2.2
                            rcases p19447_3 (m.d 0 1) (by simp) with h19471 | h19471
                            · linarith only [h16915, h19471, hlam]
                            · linarith only [h18815, h19471, hlam]
                          · have p19447_0 := h19447c.1
                            have p19447_1 := h19447c.2.1
                            have p19447_2 := h19447c.2.2.1
                            have p19447_3 := h19447c.2.2.2
                            linarith only [h18815, hlam, p19447_0]
                          · have p19447_0 := h19447c.1
                            have p19447_1 := h19447c.2.1
                            have p19447_2 := h19447c.2.2.1
                            have p19447_3 := h19447c.2.2.2
                            linarith only [h18818, hlam, p19447_1]
                          · have p19447_0 := h19447c.1
                            have p19447_1 := h19447c.2.1
                            have p19447_2 := h19447c.2.2.1
                            have p19447_3 := h19447c.2.2.2
                            linarith only [h18820, hlam, p19447_0]
                          · have p19447_0 := h19447c.1
                            have p19447_1 := h19447c.2.1
                            have p19447_2 := h19447c.2.2.1
                            have p19447_3 := h19447c.2.2.2
                            linarith only [h18821, hlam, p19447_1]
                          · have p19447_0 := h19447c.1
                            have p19447_1 := h19447c.2.1
                            have p19447_2 := h19447c.2.2.1
                            have p19447_3 := h19447c.2.2.2
                            linarith only [hlam, p19447_0]
                        · linarith only [h0, h18817, h18828, h19445, h19446, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h19480 | h19480
                        · rcases h0bigk with h19481c | h19481c | h19481c | h19481c | h19481c | h19481c | h19481c | h19481c | h19481c | h19481c | h19481c | h19481c | h19481c | h19481c | h19481c | h19481c | h19481c | h19481c | h19481c | h19481c | h19481c | h19481c | h19481c | h19481c | h19481c
                          · have p19481_0 := h19481c.1
                            have p19481_1 := h19481c.2.1
                            have p19481_2 := h19481c.2.2.1
                            have p19481_3 := h19481c.2.2.2
                            linarith only [hlam, p19481_0]
                          · have p19481_0 := h19481c.1
                            have p19481_1 := h19481c.2.1
                            have p19481_2 := h19481c.2.2.1
                            have p19481_3 := h19481c.2.2.2
                            linarith only [h0, hlam, p19481_1]
                          · have p19481_0 := h19481c.1
                            have p19481_1 := h19481c.2.1
                            have p19481_2 := h19481c.2.2.1
                            have p19481_3 := h19481c.2.2.2
                            linarith only [h14396, hlam, p19481_0]
                          · have p19481_0 := h19481c.1
                            have p19481_1 := h19481c.2.1
                            have p19481_2 := h19481c.2.2.1
                            have p19481_3 := h19481c.2.2.2
                            linarith only [h16915, hlam, p19481_1]
                          · have p19481_0 := h19481c.1
                            have p19481_1 := h19481c.2.1
                            have p19481_2 := h19481c.2.2.1
                            have p19481_3 := h19481c.2.2.2
                            linarith only [h0, h18815, h18826, h18828, h19445, h19480, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p19481_1]
                          · have p19481_0 := h19481c.1
                            have p19481_1 := h19481c.2.1
                            have p19481_2 := h19481c.2.2.1
                            have p19481_3 := h19481c.2.2.2
                            linarith only [h0, h18815, h18826, h18828, h19445, h19480, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p19481_1]
                          · have p19481_0 := h19481c.1
                            have p19481_1 := h19481c.2.1
                            have p19481_2 := h19481c.2.2.1
                            have p19481_3 := h19481c.2.2.2
                            linarith only [hlam, p19481_0]
                          · have p19481_0 := h19481c.1
                            have p19481_1 := h19481c.2.1
                            have p19481_2 := h19481c.2.2.1
                            have p19481_3 := h19481c.2.2.2
                            linarith only [h0, h14396, h18815, h18826, h18828, h19445, h19480, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p19481_1]
                          · have p19481_0 := h19481c.1
                            have p19481_1 := h19481c.2.1
                            have p19481_2 := h19481c.2.2.1
                            have p19481_3 := h19481c.2.2.2
                            linarith only [h0, h16915, h18815, h18826, h18828, h19445, h19480, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p19481_1]
                          · have p19481_0 := h19481c.1
                            have p19481_1 := h19481c.2.1
                            have p19481_2 := h19481c.2.2.1
                            have p19481_3 := h19481c.2.2.2
                            rcases p19481_3 (m.d 0 1) (by simp) with h19491 | h19491
                            · linarith only [h0, h19491, hlam]
                            · linarith only [h18815, h19491, hlam]
                          · have p19481_0 := h19481c.1
                            have p19481_1 := h19481c.2.1
                            have p19481_2 := h19481c.2.2.1
                            have p19481_3 := h19481c.2.2.2
                            linarith only [h18815, h18826, h18828, h19445, h19480, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19481_1]
                          · have p19481_0 := h19481c.1
                            have p19481_1 := h19481c.2.1
                            have p19481_2 := h19481c.2.2.1
                            have p19481_3 := h19481c.2.2.2
                            linarith only [h18816, hlam, p19481_1]
                          · have p19481_0 := h19481c.1
                            have p19481_1 := h19481c.2.1
                            have p19481_2 := h19481c.2.2.1
                            have p19481_3 := h19481c.2.2.2
                            linarith only [hlam, p19481_0]
                          · have p19481_0 := h19481c.1
                            have p19481_1 := h19481c.2.1
                            have p19481_2 := h19481c.2.2.1
                            have p19481_3 := h19481c.2.2.2
                            linarith only [h14396, h16915, h18815, h18822, h18826, h18828, h19445, h19480, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p19481_1]
                          · have p19481_0 := h19481c.1
                            have p19481_1 := h19481c.2.1
                            have p19481_2 := h19481c.2.2.1
                            have p19481_3 := h19481c.2.2.2
                            rcases p19481_3 (m.d 0 1) (by simp) with h19498 | h19498
                            · linarith only [h14396, h19498, hlam]
                            · linarith only [h18815, h19498, hlam]
                          · have p19481_0 := h19481c.1
                            have p19481_1 := h19481c.2.1
                            have p19481_2 := h19481c.2.2.1
                            have p19481_3 := h19481c.2.2.2
                            linarith only [h18815, h18826, h18828, h19445, h19480, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19481_1]
                          · have p19481_0 := h19481c.1
                            have p19481_1 := h19481c.2.1
                            have p19481_2 := h19481c.2.2.1
                            have p19481_3 := h19481c.2.2.2
                            linarith only [h18817, hlam, p19481_0]
                          · have p19481_0 := h19481c.1
                            have p19481_1 := h19481c.2.1
                            have p19481_2 := h19481c.2.2.1
                            have p19481_3 := h19481c.2.2.2
                            linarith only [h18819, hlam, p19481_0]
                          · have p19481_0 := h19481c.1
                            have p19481_1 := h19481c.2.1
                            have p19481_2 := h19481c.2.2.1
                            have p19481_3 := h19481c.2.2.2
                            linarith only [hlam, p19481_0]
                          · have p19481_0 := h19481c.1
                            have p19481_1 := h19481c.2.1
                            have p19481_2 := h19481c.2.2.1
                            have p19481_3 := h19481c.2.2.2
                            rcases p19481_3 (m.d 0 1) (by simp) with h19505 | h19505
                            · linarith only [h16915, h19505, hlam]
                            · linarith only [h18815, h19505, hlam]
                          · have p19481_0 := h19481c.1
                            have p19481_1 := h19481c.2.1
                            have p19481_2 := h19481c.2.2.1
                            have p19481_3 := h19481c.2.2.2
                            linarith only [h18815, hlam, p19481_0]
                          · have p19481_0 := h19481c.1
                            have p19481_1 := h19481c.2.1
                            have p19481_2 := h19481c.2.2.1
                            have p19481_3 := h19481c.2.2.2
                            linarith only [h18818, hlam, p19481_1]
                          · have p19481_0 := h19481c.1
                            have p19481_1 := h19481c.2.1
                            have p19481_2 := h19481c.2.2.1
                            have p19481_3 := h19481c.2.2.2
                            linarith only [h18820, hlam, p19481_0]
                          · have p19481_0 := h19481c.1
                            have p19481_1 := h19481c.2.1
                            have p19481_2 := h19481c.2.2.1
                            have p19481_3 := h19481c.2.2.2
                            linarith only [h18821, hlam, p19481_1]
                          · have p19481_0 := h19481c.1
                            have p19481_1 := h19481c.2.1
                            have p19481_2 := h19481c.2.2.1
                            have p19481_3 := h19481c.2.2.2
                            linarith only [hlam, p19481_0]
                        · linarith only [h16915, h18815, h18822, h18825, h18827, h18828, h19480, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h16915, h18821, h18827, hlam]
              · linarith only [h14396, h18820, h18826, hlam]
            · linarith only [h14396, h18819, h18825, hlam]
          · linarith only [h0, h18818, h18824, hlam]
        · linarith only [h0, h18817, h18823, hlam]
      · linarith only [h0, h18816, h18822, hlam]
    · linarith only [h16915, h18815, h18821, hlam]
  · linarith only [h16915, h18815, h18819, h18820, hlam]

end R2N4
