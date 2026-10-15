import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_21S19

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5244000 in
set_option maxHeartbeats 5244000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s7_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3473 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4044 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4238 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4335 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4336 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4337 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h4339 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h2bigk := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h3473 := hg3473
  have h4044 := hg4044
  have h4238 := hg4238
  rcases m.htr 1 2 3 (by decide) (by decide) with h4840 | h4840
  · rcases m.htr 1 2 4 (by decide) (by decide) with h4841 | h4841
    · rcases m.htr 1 2 5 (by decide) (by decide) with h4842 | h4842
      · rcases m.htr 1 3 4 (by decide) (by decide) with h4843 | h4843
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4844 | h4844
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4845 | h4845
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4846 | h4846
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4847 | h4847
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4848 | h4848
                  · linarith only [h4336, h4339, h4848, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4850 | h4850
                    · linarith only [h4336, h4339, h4846, h4850, hlam]
                    · rcases h1bigk with h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c
                      · have p4852_0 := h4852c.1
                        have p4852_1 := h4852c.2.1
                        have p4852_2 := h4852c.2.2.1
                        have p4852_3 := h4852c.2.2.2
                        linarith only [hlam, p4852_0]
                      · have p4852_0 := h4852c.1
                        have p4852_1 := h4852c.2.1
                        have p4852_2 := h4852c.2.2.1
                        have p4852_3 := h4852c.2.2.2
                        linarith only [h0, hlam, p4852_0]
                      · have p4852_0 := h4852c.1
                        have p4852_1 := h4852c.2.1
                        have p4852_2 := h4852c.2.2.1
                        have p4852_3 := h4852c.2.2.2
                        linarith only [h3473, hlam, p4852_0]
                      · have p4852_0 := h4852c.1
                        have p4852_1 := h4852c.2.1
                        have p4852_2 := h4852c.2.2.1
                        have p4852_3 := h4852c.2.2.2
                        linarith only [h4044, hlam, p4852_0]
                      · have p4852_0 := h4852c.1
                        have p4852_1 := h4852c.2.1
                        have p4852_2 := h4852c.2.2.1
                        have p4852_3 := h4852c.2.2.2
                        linarith only [h4238, hlam, p4852_0]
                      · have p4852_0 := h4852c.1
                        have p4852_1 := h4852c.2.1
                        have p4852_2 := h4852c.2.2.1
                        have p4852_3 := h4852c.2.2.2
                        rcases p4852_3 (m.d 0 1) (by simp) with h4858 | h4858
                        · linarith only [h4858, hlam, p4852_0]
                        · rcases p4852_3 (m.d 1 2) (by simp) with h4860 | h4860
                          · rcases p4852_3 (m.d 1 3) (by simp) with h4861 | h4861
                            · linarith only [h4840, h4861, hlam]
                            · linarith only [h3473, h4861, hlam]
                          · linarith only [h4860, hlam, p4852_0]
                      · have p4852_0 := h4852c.1
                        have p4852_1 := h4852c.2.1
                        have p4852_2 := h4852c.2.2.1
                        have p4852_3 := h4852c.2.2.2
                        linarith only [hlam, p4852_0]
                      · have p4852_0 := h4852c.1
                        have p4852_1 := h4852c.2.1
                        have p4852_2 := h4852c.2.2.1
                        have p4852_3 := h4852c.2.2.2
                        linarith only [h3473, hc01, hc12, hlam, hphi, p4852_1]
                      · have p4852_0 := h4852c.1
                        have p4852_1 := h4852c.2.1
                        have p4852_2 := h4852c.2.2.1
                        have p4852_3 := h4852c.2.2.2
                        linarith only [h4044, hc01, hc12, hlam, hphi, p4852_1]
                      · have p4852_0 := h4852c.1
                        have p4852_1 := h4852c.2.1
                        have p4852_2 := h4852c.2.2.1
                        have p4852_3 := h4852c.2.2.2
                        linarith only [h4238, hc01, hc12, hlam, hphi, p4852_1]
                      · have p4852_0 := h4852c.1
                        have p4852_1 := h4852c.2.1
                        have p4852_2 := h4852c.2.2.1
                        have p4852_3 := h4852c.2.2.2
                        rcases p4852_3 (m.d 0 1) (by simp) with h4869 | h4869
                        · linarith only [h4869, hlam, p4852_0]
                        · rcases p4852_3 (m.d 1 2) (by simp) with h4871 | h4871
                          · rcases p4852_3 (m.d 1 3) (by simp) with h4872 | h4872
                            · rcases p4852_3 (m.d 1 4) (by simp) with h4873 | h4873
                              · linarith only [h4843, h4873, hlam]
                              · linarith only [h4044, h4873, hlam]
                            · linarith only [h4872, hlam, p4852_0]
                          · linarith only [h0, h4871, hlam]
                      · have p4852_0 := h4852c.1
                        have p4852_1 := h4852c.2.1
                        have p4852_2 := h4852c.2.2.1
                        have p4852_3 := h4852c.2.2.2
                        linarith only [h4840, hlam, p4852_0]
                      · have p4852_0 := h4852c.1
                        have p4852_1 := h4852c.2.1
                        have p4852_2 := h4852c.2.2.1
                        have p4852_3 := h4852c.2.2.2
                        linarith only [hlam, p4852_0]
                      · have p4852_0 := h4852c.1
                        have p4852_1 := h4852c.2.1
                        have p4852_2 := h4852c.2.2.1
                        have p4852_3 := h4852c.2.2.2
                        linarith only [h4336, h4339, h4845, h4846, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p4852_1, u4ehi3]
                      · have p4852_0 := h4852c.1
                        have p4852_1 := h4852c.2.1
                        have p4852_2 := h4852c.2.2.1
                        have p4852_3 := h4852c.2.2.2
                        linarith only [h4336, h4339, h4840, h4845, h4846, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4852_1, u4ehi3]
                      · have p4852_0 := h4852c.1
                        have p4852_1 := h4852c.2.1
                        have p4852_2 := h4852c.2.2.1
                        have p4852_3 := h4852c.2.2.2
                        rcases p4852_3 (m.d 0 1) (by simp) with h4882 | h4882
                        · linarith only [h4882, hlam, p4852_0]
                        · rcases p4852_3 (m.d 1 2) (by simp) with h4884 | h4884
                          · rcases p4852_3 (m.d 1 3) (by simp) with h4885 | h4885
                            · rcases p4852_3 (m.d 1 4) (by simp) with h4886 | h4886
                              · rcases p4852_3 (m.d 1 5) (by simp) with h4887 | h4887
                                · linarith only [h4845, h4887, hlam]
                                · linarith only [h4238, h4887, hlam]
                              · linarith only [h4886, hlam, p4852_0]
                            · linarith only [h3473, h4885, hlam]
                          · linarith only [h0, h4884, hlam]
                      · have p4852_0 := h4852c.1
                        have p4852_1 := h4852c.2.1
                        have p4852_2 := h4852c.2.2.1
                        have p4852_3 := h4852c.2.2.2
                        linarith only [h4841, hlam, p4852_0]
                      · have p4852_0 := h4852c.1
                        have p4852_1 := h4852c.2.1
                        have p4852_2 := h4852c.2.2.1
                        have p4852_3 := h4852c.2.2.2
                        linarith only [h4843, hlam, p4852_1]
                      · have p4852_0 := h4852c.1
                        have p4852_1 := h4852c.2.1
                        have p4852_2 := h4852c.2.2.1
                        have p4852_3 := h4852c.2.2.2
                        linarith only [hlam, p4852_0]
                      · have p4852_0 := h4852c.1
                        have p4852_1 := h4852c.2.1
                        have p4852_2 := h4852c.2.2.1
                        have p4852_3 := h4852c.2.2.2
                        linarith only [h4336, h4339, h4845, h4846, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p4852_1, u4ehi3]
                      · have p4852_0 := h4852c.1
                        have p4852_1 := h4852c.2.1
                        have p4852_2 := h4852c.2.2.1
                        have p4852_3 := h4852c.2.2.2
                        rcases p4852_3 (m.d 0 1) (by simp) with h4897 | h4897
                        · linarith only [h4897, hlam, p4852_0]
                        · rcases p4852_3 (m.d 1 2) (by simp) with h4899 | h4899
                          · rcases p4852_3 (m.d 1 3) (by simp) with h4900 | h4900
                            · rcases p4852_3 (m.d 1 4) (by simp) with h4901 | h4901
                              · rcases p4852_3 (m.d 1 5) (by simp) with h4902 | h4902
                                · rcases h2bigk with h4903c | h4903c | h4903c | h4903c | h4903c | h4903c | h4903c | h4903c | h4903c | h4903c | h4903c | h4903c | h4903c | h4903c | h4903c | h4903c | h4903c | h4903c | h4903c | h4903c | h4903c | h4903c | h4903c | h4903c | h4903c
                                  · have p4903_0 := h4903c.1
                                    have p4903_1 := h4903c.2.1
                                    have p4903_2 := h4903c.2.2.1
                                    have p4903_3 := h4903c.2.2.2
                                    linarith only [hlam, p4903_0]
                                  · have p4903_0 := h4903c.1
                                    have p4903_1 := h4903c.2.1
                                    have p4903_2 := h4903c.2.2.1
                                    have p4903_3 := h4903c.2.2.2
                                    linarith only [h0, hlam, p4903_0]
                                  · have p4903_0 := h4903c.1
                                    have p4903_1 := h4903c.2.1
                                    have p4903_2 := h4903c.2.2.1
                                    have p4903_3 := h4903c.2.2.2
                                    linarith only [h0, h4847, h4850, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4903_1, u4ehi3]
                                  · have p4903_0 := h4903c.1
                                    have p4903_1 := h4903c.2.1
                                    have p4903_2 := h4903c.2.2.1
                                    have p4903_3 := h4903c.2.2.2
                                    rcases p4903_3 (m.d 0 2) (by simp) with h4907 | h4907
                                    · rcases p4903_3 (m.d 1 2) (by simp) with h4908 | h4908
                                      · rcases p4903_3 (m.d 2 3) (by simp) with h4909 | h4909
                                        · linarith only [h4335, h4909, hlam]
                                        · linarith only [h4846, h4909, hlam]
                                      · linarith only [h4841, h4908, hlam]
                                    · linarith only [h4907, hlam, p4903_0]
                                  · have p4903_0 := h4903c.1
                                    have p4903_1 := h4903c.2.1
                                    have p4903_2 := h4903c.2.2.1
                                    have p4903_3 := h4903c.2.2.2
                                    rcases p4903_3 (m.d 0 2) (by simp) with h4914 | h4914
                                    · rcases p4903_3 (m.d 1 2) (by simp) with h4915 | h4915
                                      · rcases p4903_3 (m.d 2 3) (by simp) with h4916 | h4916
                                        · linarith only [h4335, h4916, hlam]
                                        · linarith only [h4847, h4916, hlam]
                                      · linarith only [h4842, h4915, hlam]
                                    · linarith only [h4914, hlam, p4903_0]
                                  · have p4903_0 := h4903c.1
                                    have p4903_1 := h4903c.2.1
                                    have p4903_2 := h4903c.2.2.1
                                    have p4903_3 := h4903c.2.2.2
                                    linarith only [h4335, h4847, h4850, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4903_1, u4ehi3]
                                  · have p4903_0 := h4903c.1
                                    have p4903_1 := h4903c.2.1
                                    have p4903_2 := h4903c.2.2.1
                                    have p4903_3 := h4903c.2.2.2
                                    linarith only [hlam, p4903_0]
                                  · have p4903_0 := h4903c.1
                                    have p4903_1 := h4903c.2.1
                                    have p4903_2 := h4903c.2.2.1
                                    have p4903_3 := h4903c.2.2.2
                                    linarith only [h4847, h4850, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4903_1, u4ehi3]
                                  · have p4903_0 := h4903c.1
                                    have p4903_1 := h4903c.2.1
                                    have p4903_2 := h4903c.2.2.1
                                    have p4903_3 := h4903c.2.2.2
                                    rcases p4903_3 (m.d 0 2) (by simp) with h4924 | h4924
                                    · linarith only [h0, h4924, hlam]
                                    · linarith only [h4336, h4924, hlam]
                                  · have p4903_0 := h4903c.1
                                    have p4903_1 := h4903c.2.1
                                    have p4903_2 := h4903c.2.2.1
                                    have p4903_3 := h4903c.2.2.2
                                    rcases p4903_3 (m.d 0 2) (by simp) with h4927 | h4927
                                    · linarith only [h0, h4927, hlam]
                                    · linarith only [h4337, h4927, hlam]
                                  · have p4903_0 := h4903c.1
                                    have p4903_1 := h4903c.2.1
                                    have p4903_2 := h4903c.2.2.1
                                    have p4903_3 := h4903c.2.2.2
                                    linarith only [h4335, hlam, p4903_0]
                                  · have p4903_0 := h4903c.1
                                    have p4903_1 := h4903c.2.1
                                    have p4903_2 := h4903c.2.2.1
                                    have p4903_3 := h4903c.2.2.2
                                    linarith only [h4840, hlam, p4903_0]
                                  · have p4903_0 := h4903c.1
                                    have p4903_1 := h4903c.2.1
                                    have p4903_2 := h4903c.2.2.1
                                    have p4903_3 := h4903c.2.2.2
                                    linarith only [hlam, p4903_0]
                                  · have p4903_0 := h4903c.1
                                    have p4903_1 := h4903c.2.1
                                    have p4903_2 := h4903c.2.2.1
                                    have p4903_3 := h4903c.2.2.2
                                    linarith only [h4335, h4846, hc02, hlam, hphi, ht0b, ht45, ht5b, p4903_1, u4ehi3]
                                  · have p4903_0 := h4903c.1
                                    have p4903_1 := h4903c.2.1
                                    have p4903_2 := h4903c.2.2.1
                                    have p4903_3 := h4903c.2.2.2
                                    linarith only [h0, h4335, hc12, hlam, hphi, ht01, ht0b, ht5b, p4903_1, u5ehi2]
                                  · have p4903_0 := h4903c.1
                                    have p4903_1 := h4903c.2.1
                                    have p4903_2 := h4903c.2.2.1
                                    have p4903_3 := h4903c.2.2.2
                                    linarith only [h4336, hlam, p4903_0]
                                  · have p4903_0 := h4903c.1
                                    have p4903_1 := h4903c.2.1
                                    have p4903_2 := h4903c.2.2.1
                                    have p4903_3 := h4903c.2.2.2
                                    linarith only [h4841, hlam, p4903_0]
                                  · have p4903_0 := h4903c.1
                                    have p4903_1 := h4903c.2.1
                                    have p4903_2 := h4903c.2.2.1
                                    have p4903_3 := h4903c.2.2.2
                                    linarith only [h4846, hlam, p4903_0]
                                  · have p4903_0 := h4903c.1
                                    have p4903_1 := h4903c.2.1
                                    have p4903_2 := h4903c.2.2.1
                                    have p4903_3 := h4903c.2.2.2
                                    linarith only [hlam, p4903_0]
                                  · have p4903_0 := h4903c.1
                                    have p4903_1 := h4903c.2.1
                                    have p4903_2 := h4903c.2.2.1
                                    have p4903_3 := h4903c.2.2.2
                                    linarith only [h4848, hlam, p4903_0]
                                  · have p4903_0 := h4903c.1
                                    have p4903_1 := h4903c.2.1
                                    have p4903_2 := h4903c.2.2.1
                                    have p4903_3 := h4903c.2.2.2
                                    linarith only [h4337, hlam, p4903_0]
                                  · have p4903_0 := h4903c.1
                                    have p4903_1 := h4903c.2.1
                                    have p4903_2 := h4903c.2.2.1
                                    have p4903_3 := h4903c.2.2.2
                                    linarith only [h4842, hlam, p4903_0]
                                  · have p4903_0 := h4903c.1
                                    have p4903_1 := h4903c.2.1
                                    have p4903_2 := h4903c.2.2.1
                                    have p4903_3 := h4903c.2.2.2
                                    linarith only [h4847, hlam, p4903_0]
                                  · have p4903_0 := h4903c.1
                                    have p4903_1 := h4903c.2.1
                                    have p4903_2 := h4903c.2.2.1
                                    have p4903_3 := h4903c.2.2.2
                                    linarith only [h0, h4337, h4846, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4903_1, u4ehi3]
                                  · have p4903_0 := h4903c.1
                                    have p4903_1 := h4903c.2.1
                                    have p4903_2 := h4903c.2.2.1
                                    have p4903_3 := h4903c.2.2.2
                                    linarith only [hlam, p4903_0]
                                · linarith only [h4902, hlam, p4852_0]
                              · linarith only [h4044, h4901, hlam]
                            · linarith only [h3473, h4900, hlam]
                          · linarith only [h0, h4899, hlam]
                      · have p4852_0 := h4852c.1
                        have p4852_1 := h4852c.2.1
                        have p4852_2 := h4852c.2.2.1
                        have p4852_3 := h4852c.2.2.2
                        linarith only [h4842, hlam, p4852_0]
                      · have p4852_0 := h4852c.1
                        have p4852_1 := h4852c.2.1
                        have p4852_2 := h4852c.2.2.1
                        have p4852_3 := h4852c.2.2.2
                        linarith only [h4844, hlam, p4852_0]
                      · have p4852_0 := h4852c.1
                        have p4852_1 := h4852c.2.1
                        have p4852_2 := h4852c.2.2.1
                        have p4852_3 := h4852c.2.2.2
                        linarith only [h4845, hlam, p4852_0]
                      · have p4852_0 := h4852c.1
                        have p4852_1 := h4852c.2.1
                        have p4852_2 := h4852c.2.2.1
                        have p4852_3 := h4852c.2.2.2
                        linarith only [hlam, p4852_0]
                · linarith only [h4338, h4339, h4840, h4843, h4845, h4846, h4847, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4954 | h4954
                · linarith only [h4336, h4339, h4840, h4843, h4845, h4846, h4954, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4956 | h4956
                  · linarith only [h4336, h4339, h4956, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4958 | h4958
                    · linarith only [h4339, h4840, h4843, h4958, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                    · rcases h1bigk with h4960c | h4960c | h4960c | h4960c | h4960c | h4960c | h4960c | h4960c | h4960c | h4960c | h4960c | h4960c | h4960c | h4960c | h4960c | h4960c | h4960c | h4960c | h4960c | h4960c | h4960c | h4960c | h4960c | h4960c | h4960c
                      · have p4960_0 := h4960c.1
                        have p4960_1 := h4960c.2.1
                        have p4960_2 := h4960c.2.2.1
                        have p4960_3 := h4960c.2.2.2
                        linarith only [hlam, p4960_0]
                      · have p4960_0 := h4960c.1
                        have p4960_1 := h4960c.2.1
                        have p4960_2 := h4960c.2.2.1
                        have p4960_3 := h4960c.2.2.2
                        linarith only [h0, hlam, p4960_0]
                      · have p4960_0 := h4960c.1
                        have p4960_1 := h4960c.2.1
                        have p4960_2 := h4960c.2.2.1
                        have p4960_3 := h4960c.2.2.2
                        linarith only [h3473, hlam, p4960_0]
                      · have p4960_0 := h4960c.1
                        have p4960_1 := h4960c.2.1
                        have p4960_2 := h4960c.2.2.1
                        have p4960_3 := h4960c.2.2.2
                        linarith only [h4044, hlam, p4960_0]
                      · have p4960_0 := h4960c.1
                        have p4960_1 := h4960c.2.1
                        have p4960_2 := h4960c.2.2.1
                        have p4960_3 := h4960c.2.2.2
                        linarith only [h4238, hlam, p4960_0]
                      · have p4960_0 := h4960c.1
                        have p4960_1 := h4960c.2.1
                        have p4960_2 := h4960c.2.2.1
                        have p4960_3 := h4960c.2.2.2
                        rcases p4960_3 (m.d 0 1) (by simp) with h4966 | h4966
                        · linarith only [h4966, hlam, p4960_0]
                        · rcases p4960_3 (m.d 1 2) (by simp) with h4968 | h4968
                          · rcases p4960_3 (m.d 1 3) (by simp) with h4969 | h4969
                            · linarith only [h4840, h4969, hlam]
                            · linarith only [h3473, h4969, hlam]
                          · linarith only [h4968, hlam, p4960_0]
                      · have p4960_0 := h4960c.1
                        have p4960_1 := h4960c.2.1
                        have p4960_2 := h4960c.2.2.1
                        have p4960_3 := h4960c.2.2.2
                        linarith only [hlam, p4960_0]
                      · have p4960_0 := h4960c.1
                        have p4960_1 := h4960c.2.1
                        have p4960_2 := h4960c.2.2.1
                        have p4960_3 := h4960c.2.2.2
                        linarith only [h4339, h4843, h4845, hc12, hlam, hphi, ht01, ht0b, ht5b, p4960_1, u5ehi0]
                      · have p4960_0 := h4960c.1
                        have p4960_1 := h4960c.2.1
                        have p4960_2 := h4960c.2.2.1
                        have p4960_3 := h4960c.2.2.2
                        linarith only [h4336, h4339, h4845, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4960_1, u4ehi2]
                      · have p4960_0 := h4960c.1
                        have p4960_1 := h4960c.2.1
                        have p4960_2 := h4960c.2.2.1
                        have p4960_3 := h4960c.2.2.2
                        linarith only [h4238, hc01, hc12, hlam, hphi, p4960_1]
                      · have p4960_0 := h4960c.1
                        have p4960_1 := h4960c.2.1
                        have p4960_2 := h4960c.2.2.1
                        have p4960_3 := h4960c.2.2.2
                        rcases p4960_3 (m.d 0 1) (by simp) with h4977 | h4977
                        · linarith only [h4977, hlam, p4960_0]
                        · rcases p4960_3 (m.d 1 2) (by simp) with h4979 | h4979
                          · rcases p4960_3 (m.d 1 3) (by simp) with h4980 | h4980
                            · rcases p4960_3 (m.d 1 4) (by simp) with h4981 | h4981
                              · linarith only [h4843, h4981, hlam]
                              · linarith only [h4044, h4981, hlam]
                            · linarith only [h4980, hlam, p4960_0]
                          · linarith only [h0, h4979, hlam]
                      · have p4960_0 := h4960c.1
                        have p4960_1 := h4960c.2.1
                        have p4960_2 := h4960c.2.2.1
                        have p4960_3 := h4960c.2.2.2
                        linarith only [h4840, hlam, p4960_0]
                      · have p4960_0 := h4960c.1
                        have p4960_1 := h4960c.2.1
                        have p4960_2 := h4960c.2.2.1
                        have p4960_3 := h4960c.2.2.2
                        linarith only [hlam, p4960_0]
                      · have p4960_0 := h4960c.1
                        have p4960_1 := h4960c.2.1
                        have p4960_2 := h4960c.2.2.1
                        have p4960_3 := h4960c.2.2.2
                        linarith only [h4336, h4339, h4845, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p4960_1, u4ehi2]
                      · have p4960_0 := h4960c.1
                        have p4960_1 := h4960c.2.1
                        have p4960_2 := h4960c.2.2.1
                        have p4960_3 := h4960c.2.2.2
                        linarith only [h4336, h4339, h4840, h4845, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4960_1, u4ehi2]
                      · have p4960_0 := h4960c.1
                        have p4960_1 := h4960c.2.1
                        have p4960_2 := h4960c.2.2.1
                        have p4960_3 := h4960c.2.2.2
                        rcases p4960_3 (m.d 0 1) (by simp) with h4990 | h4990
                        · linarith only [h4990, hlam, p4960_0]
                        · rcases p4960_3 (m.d 1 2) (by simp) with h4992 | h4992
                          · rcases p4960_3 (m.d 1 3) (by simp) with h4993 | h4993
                            · rcases p4960_3 (m.d 1 4) (by simp) with h4994 | h4994
                              · rcases p4960_3 (m.d 1 5) (by simp) with h4995 | h4995
                                · linarith only [h4845, h4995, hlam]
                                · linarith only [h4238, h4995, hlam]
                              · linarith only [h4994, hlam, p4960_0]
                            · linarith only [h3473, h4993, hlam]
                          · linarith only [h0, h4992, hlam]
                      · have p4960_0 := h4960c.1
                        have p4960_1 := h4960c.2.1
                        have p4960_2 := h4960c.2.2.1
                        have p4960_3 := h4960c.2.2.2
                        linarith only [h4841, hlam, p4960_0]
                      · have p4960_0 := h4960c.1
                        have p4960_1 := h4960c.2.1
                        have p4960_2 := h4960c.2.2.1
                        have p4960_3 := h4960c.2.2.2
                        linarith only [h4843, hlam, p4960_1]
                      · have p4960_0 := h4960c.1
                        have p4960_1 := h4960c.2.1
                        have p4960_2 := h4960c.2.2.1
                        have p4960_3 := h4960c.2.2.2
                        linarith only [hlam, p4960_0]
                      · have p4960_0 := h4960c.1
                        have p4960_1 := h4960c.2.1
                        have p4960_2 := h4960c.2.2.1
                        have p4960_3 := h4960c.2.2.2
                        linarith only [h4336, h4339, h4845, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p4960_1, u4ehi2]
                      · have p4960_0 := h4960c.1
                        have p4960_1 := h4960c.2.1
                        have p4960_2 := h4960c.2.2.1
                        have p4960_3 := h4960c.2.2.2
                        rcases p4960_3 (m.d 0 1) (by simp) with h5005 | h5005
                        · linarith only [h5005, hlam, p4960_0]
                        · rcases p4960_3 (m.d 1 2) (by simp) with h5007 | h5007
                          · rcases p4960_3 (m.d 1 3) (by simp) with h5008 | h5008
                            · rcases p4960_3 (m.d 1 4) (by simp) with h5009 | h5009
                              · rcases p4960_3 (m.d 1 5) (by simp) with h5010 | h5010
                                · rcases h2bigk with h5011c | h5011c | h5011c | h5011c | h5011c | h5011c | h5011c | h5011c | h5011c | h5011c | h5011c | h5011c | h5011c | h5011c | h5011c | h5011c | h5011c | h5011c | h5011c | h5011c | h5011c | h5011c | h5011c | h5011c | h5011c
                                  · have p5011_0 := h5011c.1
                                    have p5011_1 := h5011c.2.1
                                    have p5011_2 := h5011c.2.2.1
                                    have p5011_3 := h5011c.2.2.2
                                    linarith only [hlam, p5011_0]
                                  · have p5011_0 := h5011c.1
                                    have p5011_1 := h5011c.2.1
                                    have p5011_2 := h5011c.2.2.1
                                    have p5011_3 := h5011c.2.2.2
                                    linarith only [h0, hlam, p5011_0]
                                  · have p5011_0 := h5011c.1
                                    have p5011_1 := h5011c.2.1
                                    have p5011_2 := h5011c.2.2.1
                                    have p5011_3 := h5011c.2.2.2
                                    rcases p5011_3 (m.d 0 2) (by simp) with h5014 | h5014
                                    · rcases p5011_3 (m.d 1 2) (by simp) with h5015 | h5015
                                      · rcases p5011_3 (m.d 2 3) (by simp) with h5016 | h5016
                                        · linarith only [h5016, hlam, p5011_0]
                                        · rcases p5011_3 (m.d 2 4) (by simp) with h5018 | h5018
                                          · linarith only [h4336, h5018, hlam]
                                          · linarith only [h4846, h5018, hlam]
                                      · linarith only [h4840, h5015, hlam]
                                    · linarith only [h5014, hlam, p5011_0]
                                  · have p5011_0 := h5011c.1
                                    have p5011_1 := h5011c.2.1
                                    have p5011_2 := h5011c.2.2.1
                                    have p5011_3 := h5011c.2.2.2
                                    rcases p5011_3 (m.d 0 2) (by simp) with h5023 | h5023
                                    · rcases p5011_3 (m.d 1 2) (by simp) with h5024 | h5024
                                      · rcases p5011_3 (m.d 2 3) (by simp) with h5025 | h5025
                                        · linarith only [h4335, h5025, hlam]
                                        · rcases p5011_3 (m.d 2 4) (by simp) with h5027 | h5027
                                          · linarith only [h5027, hlam, p5011_0]
                                          · rcases p5011_3 (m.d 2 5) (by simp) with h5029 | h5029
                                            · linarith only [h4337, h5029, hlam]
                                            · linarith only [h4956, h5029, hlam]
                                      · linarith only [h4841, h5024, hlam]
                                    · linarith only [h5023, hlam, p5011_0]
                                  · have p5011_0 := h5011c.1
                                    have p5011_1 := h5011c.2.1
                                    have p5011_2 := h5011c.2.2.1
                                    have p5011_3 := h5011c.2.2.2
                                    rcases p5011_3 (m.d 0 2) (by simp) with h5034 | h5034
                                    · rcases p5011_3 (m.d 1 2) (by simp) with h5035 | h5035
                                      · rcases p5011_3 (m.d 2 3) (by simp) with h5036 | h5036
                                        · linarith only [h4335, h5036, hlam]
                                        · rcases p5011_3 (m.d 2 4) (by simp) with h5038 | h5038
                                          · linarith only [h4336, h5038, hlam]
                                          · rcases p5011_3 (m.d 2 5) (by simp) with h5040 | h5040
                                            · linarith only [h5040, hlam, p5011_0]
                                            · rcases h5bigk with h5042c | h5042c | h5042c | h5042c | h5042c | h5042c | h5042c | h5042c | h5042c | h5042c | h5042c | h5042c | h5042c | h5042c | h5042c | h5042c | h5042c | h5042c | h5042c | h5042c | h5042c | h5042c | h5042c | h5042c | h5042c
                                              · have p5042_0 := h5042c.1
                                                have p5042_1 := h5042c.2.1
                                                have p5042_2 := h5042c.2.2.1
                                                have p5042_3 := h5042c.2.2.2
                                                linarith only [hlam, p5042_0]
                                              · have p5042_0 := h5042c.1
                                                have p5042_1 := h5042c.2.1
                                                have p5042_2 := h5042c.2.2.1
                                                have p5042_3 := h5042c.2.2.2
                                                linarith only [h4238, hlam, p5042_1]
                                              · have p5042_0 := h5042c.1
                                                have p5042_1 := h5042c.2.1
                                                have p5042_2 := h5042c.2.2.1
                                                have p5042_3 := h5042c.2.2.2
                                                linarith only [h4339, h4956, hc45, hlam, hphi, p5042_1, u4ehi2]
                                              · have p5042_0 := h5042c.1
                                                have p5042_1 := h5042c.2.1
                                                have p5042_2 := h5042c.2.2.1
                                                have p5042_3 := h5042c.2.2.2
                                                linarith only [h4339, h4954, h4956, hc45, hlam, hphi, p5042_1, u4ehi2]
                                              · have p5042_0 := h5042c.1
                                                have p5042_1 := h5042c.2.1
                                                have p5042_2 := h5042c.2.2.1
                                                have p5042_3 := h5042c.2.2.2
                                                linarith only [h4339, hlam, p5042_0]
                                              · have p5042_0 := h5042c.1
                                                have p5042_1 := h5042c.2.1
                                                have p5042_2 := h5042c.2.2.1
                                                have p5042_3 := h5042c.2.2.2
                                                rcases p5042_3 (m.d 0 5) (by simp) with h5048 | h5048
                                                · linarith only [h4238, h5048, hlam]
                                                · rcases p5042_3 (m.d 1 5) (by simp) with h5050 | h5050
                                                  · rcases p5042_3 (m.d 2 5) (by simp) with h5051 | h5051
                                                    · linarith only [h4842, h5051, hlam]
                                                    · rcases p5042_3 (m.d 3 5) (by simp) with h5053 | h5053
                                                      · linarith only [h4844, h5053, hlam]
                                                      · rcases p5042_3 (m.d 4 5) (by simp) with h5055 | h5055
                                                        · linarith only [h4845, h5055, hlam]
                                                        · linarith only [h4339, h5055, hlam]
                                                  · linarith only [h4238, h5050, hlam]
                                              · have p5042_0 := h5042c.1
                                                have p5042_1 := h5042c.2.1
                                                have p5042_2 := h5042c.2.2.1
                                                have p5042_3 := h5042c.2.2.2
                                                linarith only [hlam, p5042_0]
                                              · have p5042_0 := h5042c.1
                                                have p5042_1 := h5042c.2.1
                                                have p5042_2 := h5042c.2.2.1
                                                have p5042_3 := h5042c.2.2.2
                                                rcases p5042_3 (m.d 0 5) (by simp) with h5060 | h5060
                                                · linarith only [h4238, h5060, hlam]
                                                · linarith only [h4337, h5060, hlam]
                                              · have p5042_0 := h5042c.1
                                                have p5042_1 := h5042c.2.1
                                                have p5042_2 := h5042c.2.2.1
                                                have p5042_3 := h5042c.2.2.2
                                                rcases p5042_3 (m.d 0 5) (by simp) with h5063 | h5063
                                                · linarith only [h4238, h5063, hlam]
                                                · linarith only [h4338, h5063, hlam]
                                              · have p5042_0 := h5042c.1
                                                have p5042_1 := h5042c.2.1
                                                have p5042_2 := h5042c.2.2.1
                                                have p5042_3 := h5042c.2.2.2
                                                linarith only [h4336, h4339, h4840, h4843, h4845, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5042_1, u4ehi2]
                                              · have p5042_0 := h5042c.1
                                                have p5042_1 := h5042c.2.1
                                                have p5042_2 := h5042c.2.2.1
                                                have p5042_3 := h5042c.2.2.2
                                                linarith only [h4337, hlam, p5042_1]
                                              · have p5042_0 := h5042c.1
                                                have p5042_1 := h5042c.2.1
                                                have p5042_2 := h5042c.2.2.1
                                                have p5042_3 := h5042c.2.2.2
                                                linarith only [h4842, hlam, p5042_1]
                                              · have p5042_0 := h5042c.1
                                                have p5042_1 := h5042c.2.1
                                                have p5042_2 := h5042c.2.2.1
                                                have p5042_3 := h5042c.2.2.2
                                                linarith only [hlam, p5042_0]
                                              · have p5042_0 := h5042c.1
                                                have p5042_1 := h5042c.2.1
                                                have p5042_2 := h5042c.2.2.1
                                                have p5042_3 := h5042c.2.2.2
                                                linarith only [h4954, hlam, p5042_1]
                                              · have p5042_0 := h5042c.1
                                                have p5042_1 := h5042c.2.1
                                                have p5042_2 := h5042c.2.2.1
                                                have p5042_3 := h5042c.2.2.2
                                                linarith only [h4956, hlam, p5042_0]
                                              · have p5042_0 := h5042c.1
                                                have p5042_1 := h5042c.2.1
                                                have p5042_2 := h5042c.2.2.1
                                                have p5042_3 := h5042c.2.2.2
                                                linarith only [h4338, hlam, p5042_1]
                                              · have p5042_0 := h5042c.1
                                                have p5042_1 := h5042c.2.1
                                                have p5042_2 := h5042c.2.2.1
                                                have p5042_3 := h5042c.2.2.2
                                                linarith only [h4844, hlam, p5042_1]
                                              · have p5042_0 := h5042c.1
                                                have p5042_1 := h5042c.2.1
                                                have p5042_2 := h5042c.2.2.1
                                                have p5042_3 := h5042c.2.2.2
                                                linarith only [h4338, h4956, hc03, hlam, hphi, ht0b, ht45, ht5b, p5042_1, u4ehi2]
                                              · have p5042_0 := h5042c.1
                                                have p5042_1 := h5042c.2.1
                                                have p5042_2 := h5042c.2.2.1
                                                have p5042_3 := h5042c.2.2.2
                                                linarith only [hlam, p5042_0]
                                              · have p5042_0 := h5042c.1
                                                have p5042_1 := h5042c.2.1
                                                have p5042_2 := h5042c.2.2.1
                                                have p5042_3 := h5042c.2.2.2
                                                linarith only [h4958, hlam, p5042_0]
                                              · have p5042_0 := h5042c.1
                                                have p5042_1 := h5042c.2.1
                                                have p5042_2 := h5042c.2.2.1
                                                have p5042_3 := h5042c.2.2.2
                                                linarith only [h4338, h4846, h4958, hc23, hc45, hlam, hphi, ht34, p5042_1]
                                              · have p5042_0 := h5042c.1
                                                have p5042_1 := h5042c.2.1
                                                have p5042_2 := h5042c.2.2.1
                                                have p5042_3 := h5042c.2.2.2
                                                linarith only [h4845, hlam, p5042_1]
                                              · have p5042_0 := h5042c.1
                                                have p5042_1 := h5042c.2.1
                                                have p5042_2 := h5042c.2.2.1
                                                have p5042_3 := h5042c.2.2.2
                                                linarith only [h4840, h4843, h4845, h4956, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5042_1, u4ehi2]
                                              · have p5042_0 := h5042c.1
                                                have p5042_1 := h5042c.2.1
                                                have p5042_2 := h5042c.2.2.1
                                                have p5042_3 := h5042c.2.2.2
                                                linarith only [h4840, h4843, h4845, h4846, h4958, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5042_1]
                                              · have p5042_0 := h5042c.1
                                                have p5042_1 := h5042c.2.1
                                                have p5042_2 := h5042c.2.2.1
                                                have p5042_3 := h5042c.2.2.2
                                                linarith only [hlam, p5042_0]
                                      · linarith only [h4842, h5035, hlam]
                                    · linarith only [h5034, hlam, p5011_0]
                                  · have p5011_0 := h5011c.1
                                    have p5011_1 := h5011c.2.1
                                    have p5011_2 := h5011c.2.2.1
                                    have p5011_3 := h5011c.2.2.2
                                    linarith only [h4335, h4338, h4846, h4958, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5011_1]
                                  · have p5011_0 := h5011c.1
                                    have p5011_1 := h5011c.2.1
                                    have p5011_2 := h5011c.2.2.1
                                    have p5011_3 := h5011c.2.2.2
                                    linarith only [hlam, p5011_0]
                                  · have p5011_0 := h5011c.1
                                    have p5011_1 := h5011c.2.1
                                    have p5011_2 := h5011c.2.2.1
                                    have p5011_3 := h5011c.2.2.2
                                    linarith only [h4840, h4843, h4845, h4846, h4958, hlam, p5011_2]
                                  · have p5011_0 := h5011c.1
                                    have p5011_1 := h5011c.2.1
                                    have p5011_2 := h5011c.2.2.1
                                    have p5011_3 := h5011c.2.2.2
                                    rcases p5011_3 (m.d 0 2) (by simp) with h5087 | h5087
                                    · linarith only [h0, h5087, hlam]
                                    · linarith only [h4336, h5087, hlam]
                                  · have p5011_0 := h5011c.1
                                    have p5011_1 := h5011c.2.1
                                    have p5011_2 := h5011c.2.2.1
                                    have p5011_3 := h5011c.2.2.2
                                    rcases p5011_3 (m.d 0 2) (by simp) with h5090 | h5090
                                    · linarith only [h0, h5090, hlam]
                                    · linarith only [h4337, h5090, hlam]
                                  · have p5011_0 := h5011c.1
                                    have p5011_1 := h5011c.2.1
                                    have p5011_2 := h5011c.2.2.1
                                    have p5011_3 := h5011c.2.2.2
                                    linarith only [h4335, hlam, p5011_0]
                                  · have p5011_0 := h5011c.1
                                    have p5011_1 := h5011c.2.1
                                    have p5011_2 := h5011c.2.2.1
                                    have p5011_3 := h5011c.2.2.2
                                    linarith only [h4840, hlam, p5011_0]
                                  · have p5011_0 := h5011c.1
                                    have p5011_1 := h5011c.2.1
                                    have p5011_2 := h5011c.2.2.1
                                    have p5011_3 := h5011c.2.2.2
                                    linarith only [hlam, p5011_0]
                                  · have p5011_0 := h5011c.1
                                    have p5011_1 := h5011c.2.1
                                    have p5011_2 := h5011c.2.2.1
                                    have p5011_3 := h5011c.2.2.2
                                    linarith only [h4846, hlam, p5011_1]
                                  · have p5011_0 := h5011c.1
                                    have p5011_1 := h5011c.2.1
                                    have p5011_2 := h5011c.2.2.1
                                    have p5011_3 := h5011c.2.2.2
                                    linarith only [h4954, hlam, p5011_1]
                                  · have p5011_0 := h5011c.1
                                    have p5011_1 := h5011c.2.1
                                    have p5011_2 := h5011c.2.2.1
                                    have p5011_3 := h5011c.2.2.2
                                    linarith only [h4336, hlam, p5011_0]
                                  · have p5011_0 := h5011c.1
                                    have p5011_1 := h5011c.2.1
                                    have p5011_2 := h5011c.2.2.1
                                    have p5011_3 := h5011c.2.2.2
                                    linarith only [h4841, hlam, p5011_0]
                                  · have p5011_0 := h5011c.1
                                    have p5011_1 := h5011c.2.1
                                    have p5011_2 := h5011c.2.2.1
                                    have p5011_3 := h5011c.2.2.2
                                    linarith only [h4336, h4339, h4840, h4843, h4845, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5011_1]
                                  · have p5011_0 := h5011c.1
                                    have p5011_1 := h5011c.2.1
                                    have p5011_2 := h5011c.2.2.1
                                    have p5011_3 := h5011c.2.2.2
                                    linarith only [hlam, p5011_0]
                                  · have p5011_0 := h5011c.1
                                    have p5011_1 := h5011c.2.1
                                    have p5011_2 := h5011c.2.2.1
                                    have p5011_3 := h5011c.2.2.2
                                    linarith only [h4956, hlam, p5011_0]
                                  · have p5011_0 := h5011c.1
                                    have p5011_1 := h5011c.2.1
                                    have p5011_2 := h5011c.2.2.1
                                    have p5011_3 := h5011c.2.2.2
                                    linarith only [h4337, hlam, p5011_0]
                                  · have p5011_0 := h5011c.1
                                    have p5011_1 := h5011c.2.1
                                    have p5011_2 := h5011c.2.2.1
                                    have p5011_3 := h5011c.2.2.2
                                    linarith only [h4842, hlam, p5011_0]
                                  · have p5011_0 := h5011c.1
                                    have p5011_1 := h5011c.2.1
                                    have p5011_2 := h5011c.2.2.1
                                    have p5011_3 := h5011c.2.2.2
                                    rcases p5011_3 (m.d 0 2) (by simp) with h5105 | h5105
                                    · rcases p5011_3 (m.d 1 2) (by simp) with h5106 | h5106
                                      · rcases p5011_3 (m.d 2 3) (by simp) with h5107 | h5107
                                        · linarith only [h4954, h5107, hlam]
                                        · rcases p5011_3 (m.d 2 4) (by simp) with h5109 | h5109
                                          · linarith only [h4956, h5109, hlam]
                                          · linarith only [h4846, h5109, hlam]
                                      · linarith only [h4840, h5106, hlam]
                                    · linarith only [h4335, h5105, hlam]
                                  · have p5011_0 := h5011c.1
                                    have p5011_1 := h5011c.2.1
                                    have p5011_2 := h5011c.2.2.1
                                    have p5011_3 := h5011c.2.2.2
                                    linarith only [h4335, h4338, h4954, hc02, hlam, hphi, ht0b, ht45, ht5b, p5011_1, u4ehi2]
                                  · have p5011_0 := h5011c.1
                                    have p5011_1 := h5011c.2.1
                                    have p5011_2 := h5011c.2.2.1
                                    have p5011_3 := h5011c.2.2.2
                                    linarith only [hlam, p5011_0]
                                · linarith only [h5010, hlam, p4960_0]
                              · linarith only [h4044, h5009, hlam]
                            · linarith only [h3473, h5008, hlam]
                          · linarith only [h0, h5007, hlam]
                      · have p4960_0 := h4960c.1
                        have p4960_1 := h4960c.2.1
                        have p4960_2 := h4960c.2.2.1
                        have p4960_3 := h4960c.2.2.2
                        linarith only [h4842, hlam, p4960_0]
                      · have p4960_0 := h4960c.1
                        have p4960_1 := h4960c.2.1
                        have p4960_2 := h4960c.2.2.1
                        have p4960_3 := h4960c.2.2.2
                        linarith only [h4844, hlam, p4960_0]
                      · have p4960_0 := h4960c.1
                        have p4960_1 := h4960c.2.1
                        have p4960_2 := h4960c.2.2.1
                        have p4960_3 := h4960c.2.2.2
                        linarith only [h4845, hlam, p4960_0]
                      · have p4960_0 := h4960c.1
                        have p4960_1 := h4960c.2.1
                        have p4960_2 := h4960c.2.2.1
                        have p4960_3 := h4960c.2.2.2
                        linarith only [hlam, p4960_0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5124 | h5124
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5125 | h5125
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5126 | h5126
                  · linarith only [h4044, h4845, h5126, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5128 | h5128
                    · linarith only [h4044, h4845, h5124, h5128, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                    · rcases h1bigk with h5130c | h5130c | h5130c | h5130c | h5130c | h5130c | h5130c | h5130c | h5130c | h5130c | h5130c | h5130c | h5130c | h5130c | h5130c | h5130c | h5130c | h5130c | h5130c | h5130c | h5130c | h5130c | h5130c | h5130c | h5130c
                      · have p5130_0 := h5130c.1
                        have p5130_1 := h5130c.2.1
                        have p5130_2 := h5130c.2.2.1
                        have p5130_3 := h5130c.2.2.2
                        linarith only [hlam, p5130_0]
                      · have p5130_0 := h5130c.1
                        have p5130_1 := h5130c.2.1
                        have p5130_2 := h5130c.2.2.1
                        have p5130_3 := h5130c.2.2.2
                        linarith only [h0, hlam, p5130_0]
                      · have p5130_0 := h5130c.1
                        have p5130_1 := h5130c.2.1
                        have p5130_2 := h5130c.2.2.1
                        have p5130_3 := h5130c.2.2.2
                        linarith only [h3473, hlam, p5130_0]
                      · have p5130_0 := h5130c.1
                        have p5130_1 := h5130c.2.1
                        have p5130_2 := h5130c.2.2.1
                        have p5130_3 := h5130c.2.2.2
                        linarith only [h4044, hlam, p5130_0]
                      · have p5130_0 := h5130c.1
                        have p5130_1 := h5130c.2.1
                        have p5130_2 := h5130c.2.2.1
                        have p5130_3 := h5130c.2.2.2
                        linarith only [h4238, hlam, p5130_0]
                      · have p5130_0 := h5130c.1
                        have p5130_1 := h5130c.2.1
                        have p5130_2 := h5130c.2.2.1
                        have p5130_3 := h5130c.2.2.2
                        rcases p5130_3 (m.d 0 1) (by simp) with h5136 | h5136
                        · linarith only [h5136, hlam, p5130_0]
                        · rcases p5130_3 (m.d 1 2) (by simp) with h5138 | h5138
                          · rcases p5130_3 (m.d 1 3) (by simp) with h5139 | h5139
                            · linarith only [h4840, h5139, hlam]
                            · linarith only [h3473, h5139, hlam]
                          · linarith only [h5138, hlam, p5130_0]
                      · have p5130_0 := h5130c.1
                        have p5130_1 := h5130c.2.1
                        have p5130_2 := h5130c.2.2.1
                        have p5130_3 := h5130c.2.2.2
                        linarith only [hlam, p5130_0]
                      · have p5130_0 := h5130c.1
                        have p5130_1 := h5130c.2.1
                        have p5130_2 := h5130c.2.2.1
                        have p5130_3 := h5130c.2.2.2
                        linarith only [h3473, hc01, hc12, hlam, hphi, p5130_1]
                      · have p5130_0 := h5130c.1
                        have p5130_1 := h5130c.2.1
                        have p5130_2 := h5130c.2.2.1
                        have p5130_3 := h5130c.2.2.2
                        linarith only [h4044, hc01, hc12, hlam, hphi, p5130_1]
                      · have p5130_0 := h5130c.1
                        have p5130_1 := h5130c.2.1
                        have p5130_2 := h5130c.2.2.1
                        have p5130_3 := h5130c.2.2.2
                        linarith only [h4238, hc01, hc12, hlam, hphi, p5130_1]
                      · have p5130_0 := h5130c.1
                        have p5130_1 := h5130c.2.1
                        have p5130_2 := h5130c.2.2.1
                        have p5130_3 := h5130c.2.2.2
                        rcases p5130_3 (m.d 0 1) (by simp) with h5147 | h5147
                        · linarith only [h5147, hlam, p5130_0]
                        · rcases p5130_3 (m.d 1 2) (by simp) with h5149 | h5149
                          · rcases p5130_3 (m.d 1 3) (by simp) with h5150 | h5150
                            · rcases p5130_3 (m.d 1 4) (by simp) with h5151 | h5151
                              · linarith only [h4843, h5151, hlam]
                              · linarith only [h4044, h5151, hlam]
                            · linarith only [h5150, hlam, p5130_0]
                          · linarith only [h0, h5149, hlam]
                      · have p5130_0 := h5130c.1
                        have p5130_1 := h5130c.2.1
                        have p5130_2 := h5130c.2.2.1
                        have p5130_3 := h5130c.2.2.2
                        linarith only [h4840, hlam, p5130_0]
                      · have p5130_0 := h5130c.1
                        have p5130_1 := h5130c.2.1
                        have p5130_2 := h5130c.2.2.1
                        have p5130_3 := h5130c.2.2.2
                        linarith only [hlam, p5130_0]
                      · have p5130_0 := h5130c.1
                        have p5130_1 := h5130c.2.1
                        have p5130_2 := h5130c.2.2.1
                        have p5130_3 := h5130c.2.2.2
                        linarith only [h4044, hc01, hc13, hlam, hphi, p5130_1]
                      · have p5130_0 := h5130c.1
                        have p5130_1 := h5130c.2.1
                        have p5130_2 := h5130c.2.2.1
                        have p5130_3 := h5130c.2.2.2
                        linarith only [h4044, h4840, h4845, hc01, hc12, hlam, hphi, p5130_1]
                      · have p5130_0 := h5130c.1
                        have p5130_1 := h5130c.2.1
                        have p5130_2 := h5130c.2.2.1
                        have p5130_3 := h5130c.2.2.2
                        linarith only [h4845, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5130_1]
                      · have p5130_0 := h5130c.1
                        have p5130_1 := h5130c.2.1
                        have p5130_2 := h5130c.2.2.1
                        have p5130_3 := h5130c.2.2.2
                        linarith only [h4841, hlam, p5130_0]
                      · have p5130_0 := h5130c.1
                        have p5130_1 := h5130c.2.1
                        have p5130_2 := h5130c.2.2.1
                        have p5130_3 := h5130c.2.2.2
                        linarith only [h4843, hlam, p5130_1]
                      · have p5130_0 := h5130c.1
                        have p5130_1 := h5130c.2.1
                        have p5130_2 := h5130c.2.2.1
                        have p5130_3 := h5130c.2.2.2
                        linarith only [hlam, p5130_0]
                      · have p5130_0 := h5130c.1
                        have p5130_1 := h5130c.2.1
                        have p5130_2 := h5130c.2.2.1
                        have p5130_3 := h5130c.2.2.2
                        linarith only [h4845, hlam, p5130_1]
                      · have p5130_0 := h5130c.1
                        have p5130_1 := h5130c.2.1
                        have p5130_2 := h5130c.2.2.1
                        have p5130_3 := h5130c.2.2.2
                        rcases p5130_3 (m.d 0 1) (by simp) with h5165 | h5165
                        · linarith only [h5165, hlam, p5130_0]
                        · rcases p5130_3 (m.d 1 2) (by simp) with h5167 | h5167
                          · rcases p5130_3 (m.d 1 3) (by simp) with h5168 | h5168
                            · rcases p5130_3 (m.d 1 4) (by simp) with h5169 | h5169
                              · linarith only [h4845, h5169, hlam]
                              · linarith only [h4044, h5169, hlam]
                            · linarith only [h3473, h5168, hlam]
                          · linarith only [h0, h5167, hlam]
                      · have p5130_0 := h5130c.1
                        have p5130_1 := h5130c.2.1
                        have p5130_2 := h5130c.2.2.1
                        have p5130_3 := h5130c.2.2.2
                        linarith only [h4842, hlam, p5130_0]
                      · have p5130_0 := h5130c.1
                        have p5130_1 := h5130c.2.1
                        have p5130_2 := h5130c.2.2.1
                        have p5130_3 := h5130c.2.2.2
                        linarith only [h4844, hlam, p5130_0]
                      · have p5130_0 := h5130c.1
                        have p5130_1 := h5130c.2.1
                        have p5130_2 := h5130c.2.2.1
                        have p5130_3 := h5130c.2.2.2
                        linarith only [h4044, hc01, hc15, hlam, hphi, p5130_1]
                      · have p5130_0 := h5130c.1
                        have p5130_1 := h5130c.2.1
                        have p5130_2 := h5130c.2.2.1
                        have p5130_3 := h5130c.2.2.2
                        linarith only [hlam, p5130_0]
                · linarith only [h3473, h4338, h4840, h5124, h5125, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5179 | h5179
                · linarith only [h4843, h4845, h5124, h5179, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5181 | h5181
                  · linarith only [h4044, h4845, h5181, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5183 | h5183
                    · linarith only [h4044, h4845, h5183, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases h1bigk with h5185c | h5185c | h5185c | h5185c | h5185c | h5185c | h5185c | h5185c | h5185c | h5185c | h5185c | h5185c | h5185c | h5185c | h5185c | h5185c | h5185c | h5185c | h5185c | h5185c | h5185c | h5185c | h5185c | h5185c | h5185c
                      · have p5185_0 := h5185c.1
                        have p5185_1 := h5185c.2.1
                        have p5185_2 := h5185c.2.2.1
                        have p5185_3 := h5185c.2.2.2
                        linarith only [hlam, p5185_0]
                      · have p5185_0 := h5185c.1
                        have p5185_1 := h5185c.2.1
                        have p5185_2 := h5185c.2.2.1
                        have p5185_3 := h5185c.2.2.2
                        linarith only [h0, hlam, p5185_0]
                      · have p5185_0 := h5185c.1
                        have p5185_1 := h5185c.2.1
                        have p5185_2 := h5185c.2.2.1
                        have p5185_3 := h5185c.2.2.2
                        linarith only [h3473, hlam, p5185_0]
                      · have p5185_0 := h5185c.1
                        have p5185_1 := h5185c.2.1
                        have p5185_2 := h5185c.2.2.1
                        have p5185_3 := h5185c.2.2.2
                        linarith only [h4044, hlam, p5185_0]
                      · have p5185_0 := h5185c.1
                        have p5185_1 := h5185c.2.1
                        have p5185_2 := h5185c.2.2.1
                        have p5185_3 := h5185c.2.2.2
                        linarith only [h4238, hlam, p5185_0]
                      · have p5185_0 := h5185c.1
                        have p5185_1 := h5185c.2.1
                        have p5185_2 := h5185c.2.2.1
                        have p5185_3 := h5185c.2.2.2
                        rcases p5185_3 (m.d 0 1) (by simp) with h5191 | h5191
                        · linarith only [h5191, hlam, p5185_0]
                        · rcases p5185_3 (m.d 1 2) (by simp) with h5193 | h5193
                          · rcases p5185_3 (m.d 1 3) (by simp) with h5194 | h5194
                            · linarith only [h4840, h5194, hlam]
                            · linarith only [h3473, h5194, hlam]
                          · linarith only [h5193, hlam, p5185_0]
                      · have p5185_0 := h5185c.1
                        have p5185_1 := h5185c.2.1
                        have p5185_2 := h5185c.2.2.1
                        have p5185_3 := h5185c.2.2.2
                        linarith only [hlam, p5185_0]
                      · have p5185_0 := h5185c.1
                        have p5185_1 := h5185c.2.1
                        have p5185_2 := h5185c.2.2.1
                        have p5185_3 := h5185c.2.2.2
                        linarith only [h3473, hc01, hc12, hlam, hphi, p5185_1]
                      · have p5185_0 := h5185c.1
                        have p5185_1 := h5185c.2.1
                        have p5185_2 := h5185c.2.2.1
                        have p5185_3 := h5185c.2.2.2
                        linarith only [h4044, hc01, hc12, hlam, hphi, p5185_1]
                      · have p5185_0 := h5185c.1
                        have p5185_1 := h5185c.2.1
                        have p5185_2 := h5185c.2.2.1
                        have p5185_3 := h5185c.2.2.2
                        linarith only [h4238, hc01, hc12, hlam, hphi, p5185_1]
                      · have p5185_0 := h5185c.1
                        have p5185_1 := h5185c.2.1
                        have p5185_2 := h5185c.2.2.1
                        have p5185_3 := h5185c.2.2.2
                        rcases p5185_3 (m.d 0 1) (by simp) with h5202 | h5202
                        · linarith only [h5202, hlam, p5185_0]
                        · rcases p5185_3 (m.d 1 2) (by simp) with h5204 | h5204
                          · rcases p5185_3 (m.d 1 3) (by simp) with h5205 | h5205
                            · rcases p5185_3 (m.d 1 4) (by simp) with h5206 | h5206
                              · linarith only [h4843, h5206, hlam]
                              · linarith only [h4044, h5206, hlam]
                            · linarith only [h5205, hlam, p5185_0]
                          · linarith only [h0, h5204, hlam]
                      · have p5185_0 := h5185c.1
                        have p5185_1 := h5185c.2.1
                        have p5185_2 := h5185c.2.2.1
                        have p5185_3 := h5185c.2.2.2
                        linarith only [h4840, hlam, p5185_0]
                      · have p5185_0 := h5185c.1
                        have p5185_1 := h5185c.2.1
                        have p5185_2 := h5185c.2.2.1
                        have p5185_3 := h5185c.2.2.2
                        linarith only [hlam, p5185_0]
                      · have p5185_0 := h5185c.1
                        have p5185_1 := h5185c.2.1
                        have p5185_2 := h5185c.2.2.1
                        have p5185_3 := h5185c.2.2.2
                        linarith only [h4044, hc01, hc13, hlam, hphi, p5185_1]
                      · have p5185_0 := h5185c.1
                        have p5185_1 := h5185c.2.1
                        have p5185_2 := h5185c.2.2.1
                        have p5185_3 := h5185c.2.2.2
                        linarith only [h4044, h4840, h4845, hc01, hc12, hlam, hphi, p5185_1]
                      · have p5185_0 := h5185c.1
                        have p5185_1 := h5185c.2.1
                        have p5185_2 := h5185c.2.2.1
                        have p5185_3 := h5185c.2.2.2
                        linarith only [h4845, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5185_1]
                      · have p5185_0 := h5185c.1
                        have p5185_1 := h5185c.2.1
                        have p5185_2 := h5185c.2.2.1
                        have p5185_3 := h5185c.2.2.2
                        linarith only [h4841, hlam, p5185_0]
                      · have p5185_0 := h5185c.1
                        have p5185_1 := h5185c.2.1
                        have p5185_2 := h5185c.2.2.1
                        have p5185_3 := h5185c.2.2.2
                        linarith only [h4843, hlam, p5185_1]
                      · have p5185_0 := h5185c.1
                        have p5185_1 := h5185c.2.1
                        have p5185_2 := h5185c.2.2.1
                        have p5185_3 := h5185c.2.2.2
                        linarith only [hlam, p5185_0]
                      · have p5185_0 := h5185c.1
                        have p5185_1 := h5185c.2.1
                        have p5185_2 := h5185c.2.2.1
                        have p5185_3 := h5185c.2.2.2
                        linarith only [h4845, hlam, p5185_1]
                      · have p5185_0 := h5185c.1
                        have p5185_1 := h5185c.2.1
                        have p5185_2 := h5185c.2.2.1
                        have p5185_3 := h5185c.2.2.2
                        rcases p5185_3 (m.d 0 1) (by simp) with h5220 | h5220
                        · linarith only [h5220, hlam, p5185_0]
                        · rcases p5185_3 (m.d 1 2) (by simp) with h5222 | h5222
                          · rcases p5185_3 (m.d 1 3) (by simp) with h5223 | h5223
                            · rcases p5185_3 (m.d 1 4) (by simp) with h5224 | h5224
                              · linarith only [h4845, h5224, hlam]
                              · linarith only [h4044, h5224, hlam]
                            · linarith only [h3473, h5223, hlam]
                          · linarith only [h0, h5222, hlam]
                      · have p5185_0 := h5185c.1
                        have p5185_1 := h5185c.2.1
                        have p5185_2 := h5185c.2.2.1
                        have p5185_3 := h5185c.2.2.2
                        linarith only [h4842, hlam, p5185_0]
                      · have p5185_0 := h5185c.1
                        have p5185_1 := h5185c.2.1
                        have p5185_2 := h5185c.2.2.1
                        have p5185_3 := h5185c.2.2.2
                        linarith only [h4844, hlam, p5185_0]
                      · have p5185_0 := h5185c.1
                        have p5185_1 := h5185c.2.1
                        have p5185_2 := h5185c.2.2.1
                        have p5185_3 := h5185c.2.2.2
                        linarith only [h4044, hc01, hc15, hlam, hphi, p5185_1]
                      · have p5185_0 := h5185c.1
                        have p5185_1 := h5185c.2.1
                        have p5185_2 := h5185c.2.2.1
                        have p5185_3 := h5185c.2.2.2
                        linarith only [hlam, p5185_0]
          · linarith only [h3473, h4338, h4844, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h5234 | h5234
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5235 | h5235
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5236 | h5236
              · linarith only [h3473, h4338, h4843, h5236, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5238 | h5238
                · linarith only [h4336, h4339, h5235, h5236, h5238, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · linarith only [h3473, h4338, h4843, h5238, hc23, hc34, hlam, hphi]
            · linarith only [h4843, h5234, h5235, hlam]
          · linarith only [h3473, h4338, h5234, hlam]
      · linarith only [h0, h4337, h4842, hlam]
    · linarith only [h0, h4336, h4841, hlam]
  · linarith only [h0, h4335, h4840, hlam]

set_option maxHeartbeats 5244000 in
set_option maxHeartbeats 5244000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s7_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3473 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4044 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4238 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4335 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4336 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4337 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h2bigk := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h3473 := hg3473
  have h4044 := hg4044
  have h4238 := hg4238
  rcases m.htr 0 4 5 (by decide) (by decide) with h4339 | h4339
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s7_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg3473 hg4044 hg4238 h4335 h4336 h4337 h4338 h4339
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s7_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg3473 hg4044 hg4238 h4335 h4336 h4337 h4338 h4339

end R2N4
