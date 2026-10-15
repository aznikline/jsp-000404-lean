import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_11S8

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9994000 in
set_option maxHeartbeats 9994000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s6 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s7 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4 h5 h6 h7
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4816 | h4816
    · linarith only [h4816, h6, h7, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4818 | h4818
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4819 | h4819
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4820 | h4820
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4821 | h4821
            · linarith only [h4821, h7, hc13, hlam, hphi, ht01, u0ehi2]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4823 | h4823
              · linarith only [h1, h4816, h4820, h4823, hc03, hlam, hphi, u0ehi3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4825 | h4825
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4826 | h4826
                  · linarith only [h0, h4818, h4826, h7, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4828 | h4828
                    · linarith only [h0, h4, h4816, h4828, hc01, hlam, hphi, u0ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4830 | h4830
                      · linarith only [h4816, h4830, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                      · rcases h2bigk with h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c | h4832c
                        · have p4832_0 := h4832c.1
                          have p4832_1 := h4832c.2.1
                          have p4832_2 := h4832c.2.2.1
                          have p4832_3 := h4832c.2.2.2
                          linarith only [hlam, p4832_0]
                        · have p4832_0 := h4832c.1
                          have p4832_1 := h4832c.2.1
                          have p4832_2 := h4832c.2.2.1
                          have p4832_3 := h4832c.2.2.2
                          linarith only [h0, h4819, h4825, h4826, h4830, h6, h7, hc01, hc34, hc45, hlam, hphi, p4832_1, u0ehi3]
                        · have p4832_0 := h4832c.1
                          have p4832_1 := h4832c.2.1
                          have p4832_2 := h4832c.2.2.1
                          have p4832_3 := h4832c.2.2.2
                          rcases p4832_3 (m.d 0 2) (by simp) with h4835 | h4835
                          · rcases p4832_3 (m.d 1 2) (by simp) with h4836 | h4836
                            · linarith only [h0, h4836, hlam]
                            · linarith only [h4818, h4836, hlam]
                          · linarith only [h4835, hlam, p4832_0]
                        · have p4832_0 := h4832c.1
                          have p4832_1 := h4832c.2.1
                          have p4832_2 := h4832c.2.2.1
                          have p4832_3 := h4832c.2.2.2
                          rcases p4832_3 (m.d 0 2) (by simp) with h4840 | h4840
                          · rcases p4832_3 (m.d 1 2) (by simp) with h4841 | h4841
                            · linarith only [h0, h4841, hlam]
                            · linarith only [h4819, h4825, h4826, h4841, hlam]
                          · linarith only [h4840, hlam, p4832_0]
                        · have p4832_0 := h4832c.1
                          have p4832_1 := h4832c.2.1
                          have p4832_2 := h4832c.2.2.1
                          have p4832_3 := h4832c.2.2.2
                          rcases p4832_3 (m.d 0 2) (by simp) with h4845 | h4845
                          · rcases p4832_3 (m.d 1 2) (by simp) with h4846 | h4846
                            · linarith only [h0, h4846, hlam]
                            · linarith only [h4819, h4846, hlam]
                          · linarith only [h4845, hlam, p4832_0]
                        · have p4832_0 := h4832c.1
                          have p4832_1 := h4832c.2.1
                          have p4832_2 := h4832c.2.2.1
                          have p4832_3 := h4832c.2.2.2
                          linarith only [h0, hlam, p4832_0]
                        · have p4832_0 := h4832c.1
                          have p4832_1 := h4832c.2.1
                          have p4832_2 := h4832c.2.2.1
                          have p4832_3 := h4832c.2.2.2
                          linarith only [hlam, p4832_0]
                        · have p4832_0 := h4832c.1
                          have p4832_1 := h4832c.2.1
                          have p4832_2 := h4832c.2.2.1
                          have p4832_3 := h4832c.2.2.2
                          linarith only [h0, h4825, h4830, h6, h7, hc01, hc34, hc45, hlam, hphi, p4832_1, u0ehi3]
                        · have p4832_0 := h4832c.1
                          have p4832_1 := h4832c.2.1
                          have p4832_2 := h4832c.2.2.1
                          have p4832_3 := h4832c.2.2.2
                          rcases p4832_3 (m.d 0 2) (by simp) with h4853 | h4853
                          · rcases p4832_3 (m.d 1 2) (by simp) with h4854 | h4854
                            · rcases p4832_3 (m.d 2 3) (by simp) with h4855 | h4855
                              · linarith only [h4818, h4855, hlam]
                              · linarith only [h4825, h4855, hlam]
                            · linarith only [h4854, hlam, p4832_0]
                          · linarith only [h4, h4853, hlam]
                        · have p4832_0 := h4832c.1
                          have p4832_1 := h4832c.2.1
                          have p4832_2 := h4832c.2.2.1
                          have p4832_3 := h4832c.2.2.2
                          linarith only [h0, h4825, h4826, h4830, h6, h7, hc01, hc34, hc45, hlam, hphi, p4832_1, u0ehi3]
                        · have p4832_0 := h4832c.1
                          have p4832_1 := h4832c.2.1
                          have p4832_2 := h4832c.2.2.1
                          have p4832_3 := h4832c.2.2.2
                          linarith only [h3, hlam, p4832_0]
                        · have p4832_0 := h4832c.1
                          have p4832_1 := h4832c.2.1
                          have p4832_2 := h4832c.2.2.1
                          have p4832_3 := h4832c.2.2.2
                          linarith only [h4818, hlam, p4832_0]
                        · have p4832_0 := h4832c.1
                          have p4832_1 := h4832c.2.1
                          have p4832_2 := h4832c.2.2.1
                          have p4832_3 := h4832c.2.2.2
                          linarith only [hlam, p4832_0]
                        · have p4832_0 := h4832c.1
                          have p4832_1 := h4832c.2.1
                          have p4832_2 := h4832c.2.2.1
                          have p4832_3 := h4832c.2.2.2
                          linarith only [h3, h4830, h7, hc24, hc45, hlam, hphi, p4832_1]
                        · have p4832_0 := h4832c.1
                          have p4832_1 := h4832c.2.1
                          have p4832_2 := h4832c.2.2.1
                          have p4832_3 := h4832c.2.2.2
                          linarith only [h4826, hlam, p4832_0]
                        · have p4832_0 := h4832c.1
                          have p4832_1 := h4832c.2.1
                          have p4832_2 := h4832c.2.2.1
                          have p4832_3 := h4832c.2.2.2
                          linarith only [h4, hlam, p4832_0]
                        · have p4832_0 := h4832c.1
                          have p4832_1 := h4832c.2.1
                          have p4832_2 := h4832c.2.2.1
                          have p4832_3 := h4832c.2.2.2
                          linarith only [h0, h4, h4819, h4826, h4830, h6, h7, hc01, hc23, hc45, hlam, hphi, ht34, p4832_1, u0ehi3]
                        · have p4832_0 := h4832c.1
                          have p4832_1 := h4832c.2.1
                          have p4832_2 := h4832c.2.2.1
                          have p4832_3 := h4832c.2.2.2
                          linarith only [h4825, hlam, p4832_1]
                        · have p4832_0 := h4832c.1
                          have p4832_1 := h4832c.2.1
                          have p4832_2 := h4832c.2.2.1
                          have p4832_3 := h4832c.2.2.2
                          linarith only [hlam, p4832_0]
                        · have p4832_0 := h4832c.1
                          have p4832_1 := h4832c.2.1
                          have p4832_2 := h4832c.2.2.1
                          have p4832_3 := h4832c.2.2.2
                          linarith only [h4828, hlam, p4832_1]
                        · have p4832_0 := h4832c.1
                          have p4832_1 := h4832c.2.1
                          have p4832_2 := h4832c.2.2.1
                          have p4832_3 := h4832c.2.2.2
                          linarith only [h5, hlam, p4832_0]
                        · have p4832_0 := h4832c.1
                          have p4832_1 := h4832c.2.1
                          have p4832_2 := h4832c.2.2.1
                          have p4832_3 := h4832c.2.2.2
                          linarith only [h4819, hlam, p4832_0]
                        · have p4832_0 := h4832c.1
                          have p4832_1 := h4832c.2.1
                          have p4832_2 := h4832c.2.2.1
                          have p4832_3 := h4832c.2.2.2
                          linarith only [h0, h4819, h4830, h6, h7, hc01, hc23, hc45, hlam, hphi, ht34, p4832_1, u0ehi3]
                        · have p4832_0 := h4832c.1
                          have p4832_1 := h4832c.2.1
                          have p4832_2 := h4832c.2.2.1
                          have p4832_3 := h4832c.2.2.2
                          linarith only [h0, h4819, h4830, h6, h7, hc01, hc24, hc45, hlam, hphi, p4832_1, u0ehi3]
                        · have p4832_0 := h4832c.1
                          have p4832_1 := h4832c.2.1
                          have p4832_2 := h4832c.2.2.1
                          have p4832_3 := h4832c.2.2.2
                          linarith only [hlam, p4832_0]
                · linarith only [h4825, h6, h7, hc23, hc35, hlam, hphi]
          · linarith only [h4820, h6, h7, hc13, hc35, hlam, hphi]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4878 | h4878
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4879 | h4879
            · linarith only [h0, h4818, h4819, h4879, h5, h6, h7, hc01, hlam, hphi, u0ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4881 | h4881
              · linarith only [h0, h4816, h4818, h4819, h4878, h4881, h5, hc01, hlam, hphi, u0ehi3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4883 | h4883
                · linarith only [h0, h4818, h4819, h4883, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h4883, h6, h7, hc23, hc35, hlam, hphi]
          · linarith only [h4878, h6, h7, hc13, hc35, hlam, hphi]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4887 | h4887
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4888 | h4888
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4889 | h4889
            · linarith only [h3, h4818, h4889, h7, hlam]
            · linarith only [h4818, h4887, h4889, hlam]
          · linarith only [h4818, h4888, h6, h7, hc12, hc35, hlam, hphi, ht23]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4893 | h4893
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4894 | h4894
            · linarith only [h4894, h7, hc13, hlam, hphi, ht01, u0ehi2]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4896 | h4896
              · linarith only [h3, h4816, h4818, h4893, h4896, hc03, hlam, hphi, u0ehi3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4898 | h4898
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4899 | h4899
                  · linarith only [h3, h4899, h7, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4901 | h4901
                    · linarith only [h0, h4, h4816, h4901, hc01, hlam, hphi, u0ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4903 | h4903
                      · linarith only [h4816, h4903, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                      · rcases h2bigk with h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [hlam, p4905_0]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          rcases p4905_3 (m.d 0 2) (by simp) with h4907 | h4907
                          · rcases p4905_3 (m.d 1 2) (by simp) with h4908 | h4908
                            · linarith only [h0, h4908, hlam]
                            · rcases p4905_3 (m.d 2 3) (by simp) with h4910 | h4910
                              · linarith only [h3, h4910, hlam]
                              · linarith only [h4818, h4910, hlam]
                          · linarith only [h0, h4907, hlam]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          rcases p4905_3 (m.d 0 2) (by simp) with h4914 | h4914
                          · rcases p4905_3 (m.d 1 2) (by simp) with h4915 | h4915
                            · linarith only [h0, h4915, hlam]
                            · rcases p4905_3 (m.d 2 3) (by simp) with h4917 | h4917
                              · linarith only [h4917, hlam, p4905_0]
                              · rcases p4905_3 (m.d 2 4) (by simp) with h4919 | h4919
                                · linarith only [h4, h4919, hlam]
                                · rcases p4905_3 (m.d 2 5) (by simp) with h4921 | h4921
                                  · linarith only [h4921, h5, hlam]
                                  · linarith only [h4899, h4921, hlam]
                          · linarith only [h4914, hlam, p4905_0]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          rcases p4905_3 (m.d 0 2) (by simp) with h4925 | h4925
                          · rcases p4905_3 (m.d 1 2) (by simp) with h4926 | h4926
                            · linarith only [h0, h4926, hlam]
                            · rcases p4905_3 (m.d 2 3) (by simp) with h4928 | h4928
                              · linarith only [h3, h4928, hlam]
                              · linarith only [h4898, h4928, hlam]
                          · linarith only [h4925, hlam, p4905_0]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          rcases p4905_3 (m.d 0 2) (by simp) with h4932 | h4932
                          · rcases p4905_3 (m.d 1 2) (by simp) with h4933 | h4933
                            · linarith only [h0, h4933, hlam]
                            · rcases p4905_3 (m.d 2 3) (by simp) with h4935 | h4935
                              · linarith only [h3, h4935, hlam]
                              · rcases p4905_3 (m.d 2 4) (by simp) with h4937 | h4937
                                · linarith only [h4, h4937, hlam]
                                · rcases p4905_3 (m.d 2 5) (by simp) with h4939 | h4939
                                  · linarith only [h4939, hlam, p4905_0]
                                  · rcases h3bigk with h4941c | h4941c | h4941c | h4941c | h4941c | h4941c | h4941c | h4941c | h4941c | h4941c | h4941c | h4941c | h4941c | h4941c | h4941c | h4941c | h4941c | h4941c | h4941c | h4941c | h4941c | h4941c | h4941c | h4941c | h4941c
                                    · have p4941_0 := h4941c.1
                                      have p4941_1 := h4941c.2.1
                                      have p4941_2 := h4941c.2.2.1
                                      have p4941_3 := h4941c.2.2.2
                                      linarith only [hlam, p4941_0]
                                    · have p4941_0 := h4941c.1
                                      have p4941_1 := h4941c.2.1
                                      have p4941_2 := h4941c.2.2.1
                                      have p4941_3 := h4941c.2.2.2
                                      linarith only [h4903, h7, hc13, hc45, hlam, hphi, ht34, p4941_1]
                                    · have p4941_0 := h4941c.1
                                      have p4941_1 := h4941c.2.1
                                      have p4941_2 := h4941c.2.2.1
                                      have p4941_3 := h4941c.2.2.2
                                      linarith only [h4818, h4903, h7, hc12, hc45, hlam, hphi, ht23, ht34, p4941_1]
                                    · have p4941_0 := h4941c.1
                                      have p4941_1 := h4941c.2.1
                                      have p4941_2 := h4941c.2.2.1
                                      have p4941_3 := h4941c.2.2.2
                                      linarith only [h4903, h7, hc34, hc45, hlam, hphi, p4941_1]
                                    · have p4941_0 := h4941c.1
                                      have p4941_1 := h4941c.2.1
                                      have p4941_2 := h4941c.2.2.1
                                      have p4941_3 := h4941c.2.2.2
                                      linarith only [h7, hlam, p4941_0]
                                    · have p4941_0 := h4941c.1
                                      have p4941_1 := h4941c.2.1
                                      have p4941_2 := h4941c.2.2.1
                                      have p4941_3 := h4941c.2.2.2
                                      linarith only [h1, hlam, p4941_0]
                                    · have p4941_0 := h4941c.1
                                      have p4941_1 := h4941c.2.1
                                      have p4941_2 := h4941c.2.2.1
                                      have p4941_3 := h4941c.2.2.2
                                      linarith only [hlam, p4941_0]
                                    · have p4941_0 := h4941c.1
                                      have p4941_1 := h4941c.2.1
                                      have p4941_2 := h4941c.2.2.1
                                      have p4941_3 := h4941c.2.2.2
                                      linarith only [h4818, hlam, p4941_1]
                                    · have p4941_0 := h4941c.1
                                      have p4941_1 := h4941c.2.1
                                      have p4941_2 := h4941c.2.2.1
                                      have p4941_3 := h4941c.2.2.2
                                      linarith only [h1, h4903, h7, hc34, hc45, hlam, hphi, p4941_1]
                                    · have p4941_0 := h4941c.1
                                      have p4941_1 := h4941c.2.1
                                      have p4941_2 := h4941c.2.2.1
                                      have p4941_3 := h4941c.2.2.2
                                      linarith only [h4894, hlam, p4941_0]
                                    · have p4941_0 := h4941c.1
                                      have p4941_1 := h4941c.2.1
                                      have p4941_2 := h4941c.2.2.1
                                      have p4941_3 := h4941c.2.2.2
                                      linarith only [h3, hlam, p4941_0]
                                    · have p4941_0 := h4941c.1
                                      have p4941_1 := h4941c.2.1
                                      have p4941_2 := h4941c.2.2.1
                                      have p4941_3 := h4941c.2.2.2
                                      linarith only [h0, h4899, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p4905_1, p4941_1]
                                    · have p4941_0 := h4941c.1
                                      have p4941_1 := h4941c.2.1
                                      have p4941_2 := h4941c.2.2.1
                                      have p4941_3 := h4941c.2.2.2
                                      linarith only [hlam, p4941_0]
                                    · have p4941_0 := h4941c.1
                                      have p4941_1 := h4941c.2.1
                                      have p4941_2 := h4941c.2.2.1
                                      have p4941_3 := h4941c.2.2.2
                                      linarith only [h0, h4899, h4903, h6, h7, hc01, hc34, hc45, hlam, hphi, p4905_1, p4941_1, u0ehi3]
                                    · have p4941_0 := h4941c.1
                                      have p4941_1 := h4941c.2.1
                                      have p4941_2 := h4941c.2.2.1
                                      have p4941_3 := h4941c.2.2.2
                                      linarith only [h4899, hlam, p4941_0]
                                    · have p4941_0 := h4941c.1
                                      have p4941_1 := h4941c.2.1
                                      have p4941_2 := h4941c.2.2.1
                                      have p4941_3 := h4941c.2.2.2
                                      linarith only [h6, hlam, p4941_0]
                                    · have p4941_0 := h4941c.1
                                      have p4941_1 := h4941c.2.1
                                      have p4941_2 := h4941c.2.2.1
                                      have p4941_3 := h4941c.2.2.2
                                      linarith only [h4893, hlam, p4941_0]
                                    · have p4941_0 := h4941c.1
                                      have p4941_1 := h4941c.2.1
                                      have p4941_2 := h4941c.2.2.1
                                      have p4941_3 := h4941c.2.2.2
                                      linarith only [h4898, hlam, p4941_0]
                                    · have p4941_0 := h4941c.1
                                      have p4941_1 := h4941c.2.1
                                      have p4941_2 := h4941c.2.2.1
                                      have p4941_3 := h4941c.2.2.2
                                      linarith only [hlam, p4941_0]
                                    · have p4941_0 := h4941c.1
                                      have p4941_1 := h4941c.2.1
                                      have p4941_2 := h4941c.2.2.1
                                      have p4941_3 := h4941c.2.2.2
                                      linarith only [h4903, hlam, p4941_1]
                                    · have p4941_0 := h4941c.1
                                      have p4941_1 := h4941c.2.1
                                      have p4941_2 := h4941c.2.2.1
                                      have p4941_3 := h4941c.2.2.2
                                      linarith only [h4903, h6, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p4941_1, u0ehi3]
                                    · have p4941_0 := h4941c.1
                                      have p4941_1 := h4941c.2.1
                                      have p4941_2 := h4941c.2.2.1
                                      have p4941_3 := h4941c.2.2.2
                                      linarith only [h4893, h4903, hc34, hc45, hlam, hphi, p4941_1]
                                    · have p4941_0 := h4941c.1
                                      have p4941_1 := h4941c.2.1
                                      have p4941_2 := h4941c.2.2.1
                                      have p4941_3 := h4941c.2.2.2
                                      linarith only [h4818, h4903, hc12, hc45, hlam, hphi, ht23, ht34, p4941_1]
                                    · have p4941_0 := h4941c.1
                                      have p4941_1 := h4941c.2.1
                                      have p4941_2 := h4941c.2.2.1
                                      have p4941_3 := h4941c.2.2.2
                                      rcases p4941_3 (m.d 0 3) (by simp) with h4965 | h4965
                                      · linarith only [h4965, h7, hlam]
                                      · linarith only [h4965, h6, hlam]
                                    · have p4941_0 := h4941c.1
                                      have p4941_1 := h4941c.2.1
                                      have p4941_2 := h4941c.2.2.1
                                      have p4941_3 := h4941c.2.2.2
                                      linarith only [hlam, p4941_0]
                          · linarith only [h4932, hlam, p4905_0]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [h0, hlam, p4905_0]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [hlam, p4905_0]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [h4818, hlam, p4905_0]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [h0, h3, h4818, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p4905_1]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [h4887, hlam, p4905_0]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [h3, hlam, p4905_0]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [h3, h4903, h7, hc12, hc45, hlam, hphi, ht23, ht34, p4905_1]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [hlam, p4905_0]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [h3, h4903, h7, hc24, hc45, hlam, hphi, p4905_1]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [h4899, hlam, p4905_0]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [h4, hlam, p4905_0]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [h4, h4903, h6, h7, hc12, hc45, hlam, hphi, ht23, ht34, p4905_1]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [h4898, hlam, p4905_1]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [hlam, p4905_0]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [h4901, hlam, p4905_1]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [h5, hlam, p4905_0]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          rcases p4905_3 (m.d 0 2) (by simp) with h4986 | h4986
                          · rcases p4905_3 (m.d 1 2) (by simp) with h4987 | h4987
                            · linarith only [h4987, hlam, p4905_0]
                            · rcases p4905_3 (m.d 2 3) (by simp) with h4989 | h4989
                              · linarith only [h4899, h4989, hlam]
                              · linarith only [h4818, h4989, hlam]
                          · linarith only [h0, h4986, hlam]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [h4818, hc12, hc25, hlam, hphi, p4905_1]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          rcases p4905_3 (m.d 0 2) (by simp) with h4994 | h4994
                          · rcases p4905_3 (m.d 1 2) (by simp) with h4995 | h4995
                            · linarith only [h4887, h4995, hlam]
                            · rcases p4905_3 (m.d 2 3) (by simp) with h4997 | h4997
                              · linarith only [h4899, h4997, hlam]
                              · linarith only [h4898, h4997, hlam]
                          · linarith only [h4, h4994, hlam]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [hlam, p4905_0]
                · linarith only [h1, h4818, h4893, h4898, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · linarith only [h4893, h6, h7, hc13, hc35, hlam, hphi]

set_option maxHeartbeats 12210000 in
set_option maxHeartbeats 12210000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s5_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s6 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4 h5 h6

set_option maxHeartbeats 12210000 in
set_option maxHeartbeats 12210000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s5_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h5004 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 0 4 5 (by decide) (by decide) with h5005 | h5005
  · rcases m.htr 1 2 3 (by decide) (by decide) with h5006 | h5006
    · rcases m.htr 1 2 5 (by decide) (by decide) with h5007 | h5007
      · rcases m.htr 1 3 4 (by decide) (by decide) with h5008 | h5008
        · linarith only [h5008, h6, hc13, hlam, hphi, ht01, u0ehi2]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h5010 | h5010
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5011 | h5011
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5012 | h5012
              · linarith only [h5004, h5006, h5012, h6, hc12, hlam, hphi, ht01, u0ehi4]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5014 | h5014
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5015 | h5015
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5016 | h5016
                    · rcases h2bigk with h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c
                      · have p5017_0 := h5017c.1
                        have p5017_1 := h5017c.2.1
                        have p5017_2 := h5017c.2.2.1
                        have p5017_3 := h5017c.2.2.2
                        linarith only [hlam, p5017_0]
                      · have p5017_0 := h5017c.1
                        have p5017_1 := h5017c.2.1
                        have p5017_2 := h5017c.2.2.1
                        have p5017_3 := h5017c.2.2.2
                        linarith only [h0, h5006, h5014, hc01, hc35, hlam, hphi, ht0b, ht5b, p5017_1]
                      · have p5017_0 := h5017c.1
                        have p5017_1 := h5017c.2.1
                        have p5017_2 := h5017c.2.2.1
                        have p5017_3 := h5017c.2.2.2
                        rcases p5017_3 (m.d 0 2) (by simp) with h5020 | h5020
                        · rcases p5017_3 (m.d 1 2) (by simp) with h5021 | h5021
                          · linarith only [h0, h5021, hlam]
                          · linarith only [h5006, h5021, hlam]
                        · linarith only [h5020, hlam, p5017_0]
                      · have p5017_0 := h5017c.1
                        have p5017_1 := h5017c.2.1
                        have p5017_2 := h5017c.2.2.1
                        have p5017_3 := h5017c.2.2.2
                        rcases p5017_3 (m.d 0 2) (by simp) with h5025 | h5025
                        · rcases p5017_3 (m.d 1 2) (by simp) with h5026 | h5026
                          · linarith only [h0, h5026, hlam]
                          · linarith only [h0, h5006, h5014, h5016, h5026, hc01, hc45, hlam, hphi, ht0b, ht5b, p5017_1]
                        · linarith only [h5025, hlam, p5017_0]
                      · have p5017_0 := h5017c.1
                        have p5017_1 := h5017c.2.1
                        have p5017_2 := h5017c.2.2.1
                        have p5017_3 := h5017c.2.2.2
                        rcases p5017_3 (m.d 0 2) (by simp) with h5030 | h5030
                        · rcases p5017_3 (m.d 1 2) (by simp) with h5031 | h5031
                          · linarith only [h0, h5031, hlam]
                          · linarith only [h5007, h5031, hlam]
                        · linarith only [h5030, hlam, p5017_0]
                      · have p5017_0 := h5017c.1
                        have p5017_1 := h5017c.2.1
                        have p5017_2 := h5017c.2.2.1
                        have p5017_3 := h5017c.2.2.2
                        linarith only [h0, hlam, p5017_0]
                      · have p5017_0 := h5017c.1
                        have p5017_1 := h5017c.2.1
                        have p5017_2 := h5017c.2.2.1
                        have p5017_3 := h5017c.2.2.2
                        linarith only [hlam, p5017_0]
                      · have p5017_0 := h5017c.1
                        have p5017_1 := h5017c.2.1
                        have p5017_2 := h5017c.2.2.1
                        have p5017_3 := h5017c.2.2.2
                        linarith only [h0, h5014, h5016, hc01, hc45, hlam, hphi, ht0b, ht5b, p5017_1]
                      · have p5017_0 := h5017c.1
                        have p5017_1 := h5017c.2.1
                        have p5017_2 := h5017c.2.2.1
                        have p5017_3 := h5017c.2.2.2
                        linarith only [h0, h5012, h5014, h5016, hc01, hc45, hlam, hphi, ht0b, ht5b, p5017_1]
                      · have p5017_0 := h5017c.1
                        have p5017_1 := h5017c.2.1
                        have p5017_2 := h5017c.2.2.1
                        have p5017_3 := h5017c.2.2.2
                        rcases p5017_3 (m.d 0 2) (by simp) with h5039 | h5039
                        · rcases p5017_3 (m.d 1 2) (by simp) with h5040 | h5040
                          · rcases p5017_3 (m.d 2 3) (by simp) with h5041 | h5041
                            · linarith only [h5006, h5041, hlam]
                            · linarith only [h5014, h5041, hlam]
                          · linarith only [h5040, hlam, p5017_0]
                        · linarith only [h5, h5039, hlam]
                      · have p5017_0 := h5017c.1
                        have p5017_1 := h5017c.2.1
                        have p5017_2 := h5017c.2.2.1
                        have p5017_3 := h5017c.2.2.2
                        linarith only [h3, hlam, p5017_0]
                      · have p5017_0 := h5017c.1
                        have p5017_1 := h5017c.2.1
                        have p5017_2 := h5017c.2.2.1
                        have p5017_3 := h5017c.2.2.2
                        linarith only [h5006, hlam, p5017_0]
                      · have p5017_0 := h5017c.1
                        have p5017_1 := h5017c.2.1
                        have p5017_2 := h5017c.2.2.1
                        have p5017_3 := h5017c.2.2.2
                        linarith only [hlam, p5017_0]
                      · have p5017_0 := h5017c.1
                        have p5017_1 := h5017c.2.1
                        have p5017_2 := h5017c.2.2.1
                        have p5017_3 := h5017c.2.2.2
                        linarith only [h5012, hlam, p5017_0]
                      · have p5017_0 := h5017c.1
                        have p5017_1 := h5017c.2.1
                        have p5017_2 := h5017c.2.2.1
                        have p5017_3 := h5017c.2.2.2
                        linarith only [h0, h5006, hc01, hc25, hlam, hphi, ht0b, ht5b, p5017_1]
                      · have p5017_0 := h5017c.1
                        have p5017_1 := h5017c.2.1
                        have p5017_2 := h5017c.2.2.1
                        have p5017_3 := h5017c.2.2.2
                        linarith only [h4, hlam, p5017_0]
                      · have p5017_0 := h5017c.1
                        have p5017_1 := h5017c.2.1
                        have p5017_2 := h5017c.2.2.1
                        have p5017_3 := h5017c.2.2.2
                        linarith only [h0, h4, h5006, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5017_1]
                      · have p5017_0 := h5017c.1
                        have p5017_1 := h5017c.2.1
                        have p5017_2 := h5017c.2.2.1
                        have p5017_3 := h5017c.2.2.2
                        linarith only [h0, h4, h5014, h5016, hc01, hc45, hlam, hphi, ht0b, ht5b, p5017_1]
                      · have p5017_0 := h5017c.1
                        have p5017_1 := h5017c.2.1
                        have p5017_2 := h5017c.2.2.1
                        have p5017_3 := h5017c.2.2.2
                        linarith only [hlam, p5017_0]
                      · have p5017_0 := h5017c.1
                        have p5017_1 := h5017c.2.1
                        have p5017_2 := h5017c.2.2.1
                        have p5017_3 := h5017c.2.2.2
                        rcases p5017_3 (m.d 0 2) (by simp) with h5055 | h5055
                        · rcases p5017_3 (m.d 1 2) (by simp) with h5056 | h5056
                          · rcases p5017_3 (m.d 2 3) (by simp) with h5057 | h5057
                            · linarith only [h5012, h5057, hlam]
                            · linarith only [h5014, h5057, hlam]
                          · linarith only [h5007, h5056, hlam]
                        · linarith only [h5, h5055, hlam]
                      · have p5017_0 := h5017c.1
                        have p5017_1 := h5017c.2.1
                        have p5017_2 := h5017c.2.2.1
                        have p5017_3 := h5017c.2.2.2
                        linarith only [h5, hlam, p5017_0]
                      · have p5017_0 := h5017c.1
                        have p5017_1 := h5017c.2.1
                        have p5017_2 := h5017c.2.2.1
                        have p5017_3 := h5017c.2.2.2
                        linarith only [h5007, hlam, p5017_0]
                      · have p5017_0 := h5017c.1
                        have p5017_1 := h5017c.2.1
                        have p5017_2 := h5017c.2.2.1
                        have p5017_3 := h5017c.2.2.2
                        linarith only [h5014, hlam, p5017_1]
                      · have p5017_0 := h5017c.1
                        have p5017_1 := h5017c.2.1
                        have p5017_2 := h5017c.2.2.1
                        have p5017_3 := h5017c.2.2.2
                        linarith only [h5015, hlam, p5017_0]
                      · have p5017_0 := h5017c.1
                        have p5017_1 := h5017c.2.1
                        have p5017_2 := h5017c.2.2.1
                        have p5017_3 := h5017c.2.2.2
                        linarith only [hlam, p5017_0]
                    · linarith only [h5004, h5016, h6, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi4]
                  · linarith only [h5012, h5014, h5015, hlam]
                · linarith only [h5004, h5014, h6, hc23, hc34, hlam, hphi]
            · linarith only [h5008, h5010, h5011, hlam]
          · linarith only [h5004, h5010, h6, hc13, hc34, hlam, hphi]
      · linarith only [h5, h5004, h5006, h5007, h6, hc23, hc34, hlam, hphi]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h5073 | h5073
      · rcases m.htr 1 3 4 (by decide) (by decide) with h5074 | h5074
        · linarith only [h5074, h6, hc13, hlam, hphi, ht01, u0ehi2]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h5076 | h5076
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5077 | h5077
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5078 | h5078
              · linarith only [h3, h5078, h6, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5080 | h5080
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5081 | h5081
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5082 | h5082
                    · rcases h2bigk with h5083c | h5083c | h5083c | h5083c | h5083c | h5083c | h5083c | h5083c | h5083c | h5083c | h5083c | h5083c | h5083c | h5083c | h5083c | h5083c | h5083c | h5083c | h5083c | h5083c | h5083c | h5083c | h5083c | h5083c | h5083c
                      · have p5083_0 := h5083c.1
                        have p5083_1 := h5083c.2.1
                        have p5083_2 := h5083c.2.2.1
                        have p5083_3 := h5083c.2.2.2
                        linarith only [hlam, p5083_0]
                      · have p5083_0 := h5083c.1
                        have p5083_1 := h5083c.2.1
                        have p5083_2 := h5083c.2.2.1
                        have p5083_3 := h5083c.2.2.2
                        rcases p5083_3 (m.d 0 2) (by simp) with h5085 | h5085
                        · rcases p5083_3 (m.d 1 2) (by simp) with h5086 | h5086
                          · linarith only [h0, h5086, hlam]
                          · rcases p5083_3 (m.d 2 3) (by simp) with h5088 | h5088
                            · linarith only [h3, h5088, hlam]
                            · linarith only [h5006, h5088, hlam]
                        · linarith only [h0, h5085, hlam]
                      · have p5083_0 := h5083c.1
                        have p5083_1 := h5083c.2.1
                        have p5083_2 := h5083c.2.2.1
                        have p5083_3 := h5083c.2.2.2
                        linarith only [h0, h5006, h5073, h5080, h5082, hc01, hc45, hlam, hphi, ht0b, ht5b, p5083_1]
                      · have p5083_0 := h5083c.1
                        have p5083_1 := h5083c.2.1
                        have p5083_2 := h5083c.2.2.1
                        have p5083_3 := h5083c.2.2.2
                        linarith only [h0, h5006, h5073, h5078, h5080, h5082, hc01, hc45, hlam, hphi, ht0b, ht5b, p5083_1]
                      · have p5083_0 := h5083c.1
                        have p5083_1 := h5083c.2.1
                        have p5083_2 := h5083c.2.2.1
                        have p5083_3 := h5083c.2.2.2
                        linarith only [h3, h5006, h5073, hlam, p5083_2]
                      · have p5083_0 := h5083c.1
                        have p5083_1 := h5083c.2.1
                        have p5083_2 := h5083c.2.2.1
                        have p5083_3 := h5083c.2.2.2
                        linarith only [h0, hlam, p5083_0]
                      · have p5083_0 := h5083c.1
                        have p5083_1 := h5083c.2.1
                        have p5083_2 := h5083c.2.2.1
                        have p5083_3 := h5083c.2.2.2
                        linarith only [hlam, p5083_0]
                      · have p5083_0 := h5083c.1
                        have p5083_1 := h5083c.2.1
                        have p5083_2 := h5083c.2.2.1
                        have p5083_3 := h5083c.2.2.2
                        linarith only [h5006, hlam, p5083_0]
                      · have p5083_0 := h5083c.1
                        have p5083_1 := h5083c.2.1
                        have p5083_2 := h5083c.2.2.1
                        have p5083_3 := h5083c.2.2.2
                        linarith only [h5006, h5078, hlam, p5083_1]
                      · have p5083_0 := h5083c.1
                        have p5083_1 := h5083c.2.1
                        have p5083_2 := h5083c.2.2.1
                        have p5083_3 := h5083c.2.2.2
                        linarith only [h4, h5006, h5078, h5080, h5082, hc02, hc45, hlam, hphi, ht0b, ht5b, p5083_1]
                      · have p5083_0 := h5083c.1
                        have p5083_1 := h5083c.2.1
                        have p5083_2 := h5083c.2.2.1
                        have p5083_3 := h5083c.2.2.2
                        linarith only [h3, hlam, p5083_0]
                      · have p5083_0 := h5083c.1
                        have p5083_1 := h5083c.2.1
                        have p5083_2 := h5083c.2.2.1
                        have p5083_3 := h5083c.2.2.2
                        linarith only [h3, h6, hc12, hc34, hlam, hphi, ht23, p5083_1]
                      · have p5083_0 := h5083c.1
                        have p5083_1 := h5083c.2.1
                        have p5083_2 := h5083c.2.2.1
                        have p5083_3 := h5083c.2.2.2
                        linarith only [hlam, p5083_0]
                      · have p5083_0 := h5083c.1
                        have p5083_1 := h5083c.2.1
                        have p5083_2 := h5083c.2.2.1
                        have p5083_3 := h5083c.2.2.2
                        linarith only [h5078, hlam, p5083_0]
                      · have p5083_0 := h5083c.1
                        have p5083_1 := h5083c.2.1
                        have p5083_2 := h5083c.2.2.1
                        have p5083_3 := h5083c.2.2.2
                        rcases p5083_3 (m.d 0 2) (by simp) with h5104 | h5104
                        · rcases p5083_3 (m.d 1 2) (by simp) with h5105 | h5105
                          · linarith only [h5006, h5105, hlam]
                          · linarith only [h5073, h5105, hlam]
                        · linarith only [h5, h5104, hlam]
                      · have p5083_0 := h5083c.1
                        have p5083_1 := h5083c.2.1
                        have p5083_2 := h5083c.2.2.1
                        have p5083_3 := h5083c.2.2.2
                        linarith only [h4, hlam, p5083_0]
                      · have p5083_0 := h5083c.1
                        have p5083_1 := h5083c.2.1
                        have p5083_2 := h5083c.2.2.1
                        have p5083_3 := h5083c.2.2.2
                        linarith only [h0, h4, h5073, h5080, h5082, hc01, hc45, hlam, hphi, ht0b, ht5b, p5083_1]
                      · have p5083_0 := h5083c.1
                        have p5083_1 := h5083c.2.1
                        have p5083_2 := h5083c.2.2.1
                        have p5083_3 := h5083c.2.2.2
                        linarith only [h0, h4, h5006, h5073, h5080, h5082, hc01, hc45, hlam, hphi, ht0b, ht5b, p5083_1]
                      · have p5083_0 := h5083c.1
                        have p5083_1 := h5083c.2.1
                        have p5083_2 := h5083c.2.2.1
                        have p5083_3 := h5083c.2.2.2
                        linarith only [hlam, p5083_0]
                      · have p5083_0 := h5083c.1
                        have p5083_1 := h5083c.2.1
                        have p5083_2 := h5083c.2.2.1
                        have p5083_3 := h5083c.2.2.2
                        rcases p5083_3 (m.d 0 2) (by simp) with h5113 | h5113
                        · rcases p5083_3 (m.d 1 2) (by simp) with h5114 | h5114
                          · linarith only [h5006, h5078, h5114, hlam]
                          · linarith only [h5073, h5114, hlam]
                        · linarith only [h5, h5113, hlam]
                      · have p5083_0 := h5083c.1
                        have p5083_1 := h5083c.2.1
                        have p5083_2 := h5083c.2.2.1
                        have p5083_3 := h5083c.2.2.2
                        linarith only [h5, hlam, p5083_0]
                      · have p5083_0 := h5083c.1
                        have p5083_1 := h5083c.2.1
                        have p5083_2 := h5083c.2.2.1
                        have p5083_3 := h5083c.2.2.2
                        linarith only [h5073, hlam, p5083_0]
                      · have p5083_0 := h5083c.1
                        have p5083_1 := h5083c.2.1
                        have p5083_2 := h5083c.2.2.1
                        have p5083_3 := h5083c.2.2.2
                        linarith only [h5080, hlam, p5083_1]
                      · have p5083_0 := h5083c.1
                        have p5083_1 := h5083c.2.1
                        have p5083_2 := h5083c.2.2.1
                        have p5083_3 := h5083c.2.2.2
                        linarith only [h5081, hlam, p5083_0]
                      · have p5083_0 := h5083c.1
                        have p5083_1 := h5083c.2.1
                        have p5083_2 := h5083c.2.2.1
                        have p5083_3 := h5083c.2.2.2
                        linarith only [hlam, p5083_0]
                    · linarith only [h5082, h6, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                  · linarith only [h5006, h5073, h5077, h5078, h5081, hlam]
                · linarith only [h5004, h5006, h5073, h5080, hc03, hc25, hlam, hphi, ht0b, ht5b]
            · linarith only [h5006, h5073, h5074, h5077, hlam]
          · linarith only [h5004, h5006, h5073, h5076, h6, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h5128 | h5128
        · linarith only [h5128, h6, hc13, hlam, hphi, ht01, u0ehi2]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h5130 | h5130
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5131 | h5131
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5132 | h5132
              · linarith only [h3, h5132, h6, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5134 | h5134
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5135 | h5135
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5136 | h5136
                    · rcases h2bigk with h5137c | h5137c | h5137c | h5137c | h5137c | h5137c | h5137c | h5137c | h5137c | h5137c | h5137c | h5137c | h5137c | h5137c | h5137c | h5137c | h5137c | h5137c | h5137c | h5137c | h5137c | h5137c | h5137c | h5137c | h5137c
                      · have p5137_0 := h5137c.1
                        have p5137_1 := h5137c.2.1
                        have p5137_2 := h5137c.2.2.1
                        have p5137_3 := h5137c.2.2.2
                        linarith only [hlam, p5137_0]
                      · have p5137_0 := h5137c.1
                        have p5137_1 := h5137c.2.1
                        have p5137_2 := h5137c.2.2.1
                        have p5137_3 := h5137c.2.2.2
                        rcases p5137_3 (m.d 0 2) (by simp) with h5139 | h5139
                        · rcases p5137_3 (m.d 1 2) (by simp) with h5140 | h5140
                          · linarith only [h0, h5140, hlam]
                          · rcases p5137_3 (m.d 2 3) (by simp) with h5142 | h5142
                            · linarith only [h3, h5142, hlam]
                            · linarith only [h5006, h5142, hlam]
                        · linarith only [h0, h5139, hlam]
                      · have p5137_0 := h5137c.1
                        have p5137_1 := h5137c.2.1
                        have p5137_2 := h5137c.2.2.1
                        have p5137_3 := h5137c.2.2.2
                        rcases p5137_3 (m.d 0 2) (by simp) with h5146 | h5146
                        · rcases p5137_3 (m.d 1 2) (by simp) with h5147 | h5147
                          · linarith only [h0, h5147, hlam]
                          · rcases p5137_3 (m.d 2 3) (by simp) with h5149 | h5149
                            · linarith only [h5149, hlam, p5137_0]
                            · rcases p5137_3 (m.d 2 4) (by simp) with h5151 | h5151
                              · linarith only [h4, h5151, hlam]
                              · linarith only [h5132, h5151, hlam]
                        · linarith only [h5146, hlam, p5137_0]
                      · have p5137_0 := h5137c.1
                        have p5137_1 := h5137c.2.1
                        have p5137_2 := h5137c.2.2.1
                        have p5137_3 := h5137c.2.2.2
                        rcases p5137_3 (m.d 0 2) (by simp) with h5155 | h5155
                        · rcases p5137_3 (m.d 1 2) (by simp) with h5156 | h5156
                          · linarith only [h0, h5156, hlam]
                          · rcases p5137_3 (m.d 2 3) (by simp) with h5158 | h5158
                            · linarith only [h3, h5158, hlam]
                            · rcases p5137_3 (m.d 2 4) (by simp) with h5160 | h5160
                              · linarith only [h5160, hlam, p5137_0]
                              · rcases p5137_3 (m.d 2 5) (by simp) with h5162 | h5162
                                · linarith only [h5, h5162, hlam]
                                · rcases h3bigk with h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c | h5164c
                                  · have p5164_0 := h5164c.1
                                    have p5164_1 := h5164c.2.1
                                    have p5164_2 := h5164c.2.2.1
                                    have p5164_3 := h5164c.2.2.2
                                    linarith only [hlam, p5164_0]
                                  · have p5164_0 := h5164c.1
                                    have p5164_1 := h5164c.2.1
                                    have p5164_2 := h5164c.2.2.1
                                    have p5164_3 := h5164c.2.2.2
                                    linarith only [h6, hc13, hc34, hlam, hphi, p5164_1]
                                  · have p5164_0 := h5164c.1
                                    have p5164_1 := h5164c.2.1
                                    have p5164_2 := h5164c.2.2.1
                                    have p5164_3 := h5164c.2.2.2
                                    linarith only [h6, hc23, hc34, hlam, hphi, p5164_1]
                                  · have p5164_0 := h5164c.1
                                    have p5164_1 := h5164c.2.1
                                    have p5164_2 := h5164c.2.2.1
                                    have p5164_3 := h5164c.2.2.2
                                    linarith only [h6, hlam, p5164_0]
                                  · have p5164_0 := h5164c.1
                                    have p5164_1 := h5164c.2.1
                                    have p5164_2 := h5164c.2.2.1
                                    have p5164_3 := h5164c.2.2.2
                                    rcases p5164_3 (m.d 0 3) (by simp) with h5169 | h5169
                                    · rcases p5164_3 (m.d 1 3) (by simp) with h5170 | h5170
                                      · linarith only [h1, h5170, hlam]
                                      · linarith only [h5130, h5170, hlam]
                                    · linarith only [h5169, hlam, p5164_0]
                                  · have p5164_0 := h5164c.1
                                    have p5164_1 := h5164c.2.1
                                    have p5164_2 := h5164c.2.2.1
                                    have p5164_3 := h5164c.2.2.2
                                    linarith only [h1, hlam, p5164_0]
                                  · have p5164_0 := h5164c.1
                                    have p5164_1 := h5164c.2.1
                                    have p5164_2 := h5164c.2.2.1
                                    have p5164_3 := h5164c.2.2.2
                                    linarith only [hlam, p5164_0]
                                  · have p5164_0 := h5164c.1
                                    have p5164_1 := h5164c.2.1
                                    have p5164_2 := h5164c.2.2.1
                                    have p5164_3 := h5164c.2.2.2
                                    linarith only [h5006, hlam, p5164_1]
                                  · have p5164_0 := h5164c.1
                                    have p5164_1 := h5164c.2.1
                                    have p5164_2 := h5164c.2.2.1
                                    have p5164_3 := h5164c.2.2.2
                                    linarith only [h5128, hlam, p5164_0]
                                  · have p5164_0 := h5164c.1
                                    have p5164_1 := h5164c.2.1
                                    have p5164_2 := h5164c.2.2.1
                                    have p5164_3 := h5164c.2.2.2
                                    linarith only [h0, h5006, h5132, h5136, hc01, hc45, hlam, hphi, ht0b, ht5b, p5137_1, p5164_1]
                                  · have p5164_0 := h5164c.1
                                    have p5164_1 := h5164c.2.1
                                    have p5164_2 := h5164c.2.2.1
                                    have p5164_3 := h5164c.2.2.2
                                    linarith only [h3, hlam, p5164_0]
                                  · have p5164_0 := h5164c.1
                                    have p5164_1 := h5164c.2.1
                                    have p5164_2 := h5164c.2.2.1
                                    have p5164_3 := h5164c.2.2.2
                                    linarith only [h3, h6, hc13, hc34, hlam, hphi, p5164_1]
                                  · have p5164_0 := h5164c.1
                                    have p5164_1 := h5164c.2.1
                                    have p5164_2 := h5164c.2.2.1
                                    have p5164_3 := h5164c.2.2.2
                                    linarith only [hlam, p5164_0]
                                  · have p5164_0 := h5164c.1
                                    have p5164_1 := h5164c.2.1
                                    have p5164_2 := h5164c.2.2.1
                                    have p5164_3 := h5164c.2.2.2
                                    linarith only [h5132, hlam, p5164_0]
                                  · have p5164_0 := h5164c.1
                                    have p5164_1 := h5164c.2.1
                                    have p5164_2 := h5164c.2.2.1
                                    have p5164_3 := h5164c.2.2.2
                                    linarith only [h0, h5132, h5136, hc01, hc45, hlam, hphi, ht0b, ht5b, p5137_1, p5164_1]
                                  · have p5164_0 := h5164c.1
                                    have p5164_1 := h5164c.2.1
                                    have p5164_2 := h5164c.2.2.1
                                    have p5164_3 := h5164c.2.2.2
                                    linarith only [h0, h5006, h5132, hc01, hc12, hc34, hlam, hphi, ht23, p5137_1, p5164_1, u0ehi2]
                                  · have p5164_0 := h5164c.1
                                    have p5164_1 := h5164c.2.1
                                    have p5164_2 := h5164c.2.2.1
                                    have p5164_3 := h5164c.2.2.2
                                    rcases p5164_3 (m.d 0 3) (by simp) with h5185 | h5185
                                    · linarith only [h5185, h6, hlam]
                                    · linarith only [h1, h5185, hlam]
                                  · have p5164_0 := h5164c.1
                                    have p5164_1 := h5164c.2.1
                                    have p5164_2 := h5164c.2.2.1
                                    have p5164_3 := h5164c.2.2.2
                                    linarith only [h5073, h5134, hc12, hc34, hlam, hphi, ht23, p5164_1]
                                  · have p5164_0 := h5164c.1
                                    have p5164_1 := h5164c.2.1
                                    have p5164_2 := h5164c.2.2.1
                                    have p5164_3 := h5164c.2.2.2
                                    linarith only [hlam, p5164_0]
                                  · have p5164_0 := h5164c.1
                                    have p5164_1 := h5164c.2.1
                                    have p5164_2 := h5164c.2.2.1
                                    have p5164_3 := h5164c.2.2.2
                                    rcases p5164_3 (m.d 0 3) (by simp) with h5190 | h5190
                                    · linarith only [h5190, h6, hlam]
                                    · linarith only [h5004, h5190, hlam]
                                  · have p5164_0 := h5164c.1
                                    have p5164_1 := h5164c.2.1
                                    have p5164_2 := h5164c.2.2.1
                                    have p5164_3 := h5164c.2.2.2
                                    linarith only [h5004, hlam, p5164_0]
                                  · have p5164_0 := h5164c.1
                                    have p5164_1 := h5164c.2.1
                                    have p5164_2 := h5164c.2.2.1
                                    have p5164_3 := h5164c.2.2.2
                                    linarith only [h5130, hlam, p5164_0]
                                  · have p5164_0 := h5164c.1
                                    have p5164_1 := h5164c.2.1
                                    have p5164_2 := h5164c.2.2.1
                                    have p5164_3 := h5164c.2.2.2
                                    linarith only [h5134, hlam, p5164_0]
                                  · have p5164_0 := h5164c.1
                                    have p5164_1 := h5164c.2.1
                                    have p5164_2 := h5164c.2.2.1
                                    have p5164_3 := h5164c.2.2.2
                                    linarith only [h5136, hlam, p5164_0]
                                  · have p5164_0 := h5164c.1
                                    have p5164_1 := h5164c.2.1
                                    have p5164_2 := h5164c.2.2.1
                                    have p5164_3 := h5164c.2.2.2
                                    linarith only [hlam, p5164_0]
                        · linarith only [h5155, hlam, p5137_0]
                      · have p5137_0 := h5137c.1
                        have p5137_1 := h5137c.2.1
                        have p5137_2 := h5137c.2.2.1
                        have p5137_3 := h5137c.2.2.2
                        rcases p5137_3 (m.d 0 2) (by simp) with h5199 | h5199
                        · rcases p5137_3 (m.d 1 2) (by simp) with h5200 | h5200
                          · linarith only [h0, h5200, hlam]
                          · rcases p5137_3 (m.d 2 3) (by simp) with h5202 | h5202
                            · linarith only [h3, h5202, hlam]
                            · linarith only [h5134, h5202, hlam]
                        · linarith only [h5199, hlam, p5137_0]
                      · have p5137_0 := h5137c.1
                        have p5137_1 := h5137c.2.1
                        have p5137_2 := h5137c.2.2.1
                        have p5137_3 := h5137c.2.2.2
                        linarith only [h0, hlam, p5137_0]
                      · have p5137_0 := h5137c.1
                        have p5137_1 := h5137c.2.1
                        have p5137_2 := h5137c.2.2.1
                        have p5137_3 := h5137c.2.2.2
                        linarith only [hlam, p5137_0]
                      · have p5137_0 := h5137c.1
                        have p5137_1 := h5137c.2.1
                        have p5137_2 := h5137c.2.2.1
                        have p5137_3 := h5137c.2.2.2
                        linarith only [h5006, hlam, p5137_0]
                      · have p5137_0 := h5137c.1
                        have p5137_1 := h5137c.2.1
                        have p5137_2 := h5137c.2.2.1
                        have p5137_3 := h5137c.2.2.2
                        linarith only [h5073, h5132, h5134, hlam, p5137_1]
                      · have p5137_0 := h5137c.1
                        have p5137_1 := h5137c.2.1
                        have p5137_2 := h5137c.2.2.1
                        have p5137_3 := h5137c.2.2.2
                        linarith only [h5073, hlam, p5137_0]
                      · have p5137_0 := h5137c.1
                        have p5137_1 := h5137c.2.1
                        have p5137_2 := h5137c.2.2.1
                        have p5137_3 := h5137c.2.2.2
                        linarith only [h3, hlam, p5137_0]
                      · have p5137_0 := h5137c.1
                        have p5137_1 := h5137c.2.1
                        have p5137_2 := h5137c.2.2.1
                        have p5137_3 := h5137c.2.2.2
                        linarith only [h3, h6, hc12, hc34, hlam, hphi, ht23, p5137_1]
                      · have p5137_0 := h5137c.1
                        have p5137_1 := h5137c.2.1
                        have p5137_2 := h5137c.2.2.1
                        have p5137_3 := h5137c.2.2.2
                        linarith only [hlam, p5137_0]
                      · have p5137_0 := h5137c.1
                        have p5137_1 := h5137c.2.1
                        have p5137_2 := h5137c.2.2.1
                        have p5137_3 := h5137c.2.2.2
                        linarith only [h5132, hlam, p5137_0]
                      · have p5137_0 := h5137c.1
                        have p5137_1 := h5137c.2.1
                        have p5137_2 := h5137c.2.2.1
                        have p5137_3 := h5137c.2.2.2
                        linarith only [h3, h5073, h6, hc12, hc34, hlam, hphi, ht23, p5137_1]
                      · have p5137_0 := h5137c.1
                        have p5137_1 := h5137c.2.1
                        have p5137_2 := h5137c.2.2.1
                        have p5137_3 := h5137c.2.2.2
                        linarith only [h4, hlam, p5137_0]
                      · have p5137_0 := h5137c.1
                        have p5137_1 := h5137c.2.1
                        have p5137_2 := h5137c.2.2.1
                        have p5137_3 := h5137c.2.2.2
                        rcases p5137_3 (m.d 0 2) (by simp) with h5217 | h5217
                        · rcases p5137_3 (m.d 1 2) (by simp) with h5218 | h5218
                          · linarith only [h5218, hlam, p5137_0]
                          · rcases p5137_3 (m.d 2 3) (by simp) with h5220 | h5220
                            · linarith only [h5132, h5220, hlam]
                            · linarith only [h5006, h5220, hlam]
                        · linarith only [h0, h5217, hlam]
                      · have p5137_0 := h5137c.1
                        have p5137_1 := h5137c.2.1
                        have p5137_2 := h5137c.2.2.1
                        have p5137_3 := h5137c.2.2.2
                        linarith only [h0, h4, h5006, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5137_1]
                      · have p5137_0 := h5137c.1
                        have p5137_1 := h5137c.2.1
                        have p5137_2 := h5137c.2.2.1
                        have p5137_3 := h5137c.2.2.2
                        linarith only [hlam, p5137_0]
                      · have p5137_0 := h5137c.1
                        have p5137_1 := h5137c.2.1
                        have p5137_2 := h5137c.2.2.1
                        have p5137_3 := h5137c.2.2.2
                        linarith only [h0, h4, h5073, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5137_1]
                      · have p5137_0 := h5137c.1
                        have p5137_1 := h5137c.2.1
                        have p5137_2 := h5137c.2.2.1
                        have p5137_3 := h5137c.2.2.2
                        linarith only [h5, hlam, p5137_0]
                      · have p5137_0 := h5137c.1
                        have p5137_1 := h5137c.2.1
                        have p5137_2 := h5137c.2.2.1
                        have p5137_3 := h5137c.2.2.2
                        linarith only [h3, h5134, h6, hc12, hc34, hlam, hphi, ht23, p5137_1]
                      · have p5137_0 := h5137c.1
                        have p5137_1 := h5137c.2.1
                        have p5137_2 := h5137c.2.2.1
                        have p5137_3 := h5137c.2.2.2
                        linarith only [h5134, hlam, p5137_1]
                      · have p5137_0 := h5137c.1
                        have p5137_1 := h5137c.2.1
                        have p5137_2 := h5137c.2.2.1
                        have p5137_3 := h5137c.2.2.2
                        linarith only [h5135, hlam, p5137_0]
                      · have p5137_0 := h5137c.1
                        have p5137_1 := h5137c.2.1
                        have p5137_2 := h5137c.2.2.1
                        have p5137_3 := h5137c.2.2.2
                        linarith only [hlam, p5137_0]
                    · linarith only [h5136, h6, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                  · linarith only [h5006, h5130, h5131, h5132, h5135, hlam]
                · linarith only [h5004, h5006, h5134, h6, hc13, hc34, hlam, hphi]
            · linarith only [h5128, h5130, h5131, hlam]
          · linarith only [h5004, h5130, h6, hc13, hc34, hlam, hphi]
  · linarith only [h5004, h5005, h6, hlam]

end R2N4
