import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 13644000 in
set_option maxHeartbeats 13644000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s6_x1_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4388 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h4905 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h4906 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h4907 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 5 (by decide) (by decide) with h4908 | h4908
  · rcases m.htr 1 3 4 (by decide) (by decide) with h4909 | h4909
    · linarith only [h1, h4909, h7, hlam]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h4911 | h4911
      · linarith only [h1, h4388, h4911, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h4913 | h4913
        · rcases m.htr 2 3 4 (by decide) (by decide) with h4914 | h4914
          · linarith only [h1, h4906, h4914, h7, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h4916 | h4916
            · linarith only [h1, h4388, h4906, h4916, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h4918 | h4918
              · rcases m.htr 3 4 5 (by decide) (by decide) with h4919 | h4919
                · rcases h0bigk with h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c
                  · have p4920_0 := h4920c.1
                    have p4920_1 := h4920c.2.1
                    have p4920_2 := h4920c.2.2.1
                    have p4920_3 := h4920c.2.2.2
                    linarith only [hlam, p4920_0]
                  · have p4920_0 := h4920c.1
                    have p4920_1 := h4920c.2.1
                    have p4920_2 := h4920c.2.2.1
                    have p4920_3 := h4920c.2.2.2
                    linarith only [h0, h4907, h4918, hc01, hc45, hlam, hphi, ht0b, ht5b, p4920_1]
                  · have p4920_0 := h4920c.1
                    have p4920_1 := h4920c.2.1
                    have p4920_2 := h4920c.2.2.1
                    have p4920_3 := h4920c.2.2.2
                    rcases p4920_3 (m.d 0 1) (by simp) with h4923 | h4923
                    · rcases p4920_3 (m.d 0 2) (by simp) with h4924 | h4924
                      · linarith only [h0, h4924, hlam]
                      · linarith only [h4, h4924, hlam]
                    · linarith only [h1, h4923, hlam]
                  · have p4920_0 := h4920c.1
                    have p4920_1 := h4920c.2.1
                    have p4920_2 := h4920c.2.2.1
                    have p4920_3 := h4920c.2.2.2
                    rcases p4920_3 (m.d 0 1) (by simp) with h4928 | h4928
                    · rcases p4920_3 (m.d 0 2) (by simp) with h4929 | h4929
                      · linarith only [h0, h4929, hlam]
                      · linarith only [h4929, h5, hlam]
                    · linarith only [h2, h4928, hlam]
                  · have p4920_0 := h4920c.1
                    have p4920_1 := h4920c.2.1
                    have p4920_2 := h4920c.2.2.1
                    have p4920_3 := h4920c.2.2.2
                    rcases p4920_3 (m.d 0 1) (by simp) with h4933 | h4933
                    · rcases p4920_3 (m.d 0 2) (by simp) with h4934 | h4934
                      · linarith only [h0, h4934, hlam]
                      · linarith only [h4934, h6, hlam]
                    · linarith only [h3, h4933, hlam]
                  · have p4920_0 := h4920c.1
                    have p4920_1 := h4920c.2.1
                    have p4920_2 := h4920c.2.2.1
                    have p4920_3 := h4920c.2.2.2
                    linarith only [h0, hlam, p4920_0]
                  · have p4920_0 := h4920c.1
                    have p4920_1 := h4920c.2.1
                    have p4920_2 := h4920c.2.2.1
                    have p4920_3 := h4920c.2.2.2
                    linarith only [hlam, p4920_0]
                  · have p4920_0 := h4920c.1
                    have p4920_1 := h4920c.2.1
                    have p4920_2 := h4920c.2.2.1
                    have p4920_3 := h4920c.2.2.2
                    rcases p4920_3 (m.d 0 1) (by simp) with h4940 | h4940
                    · rcases p4920_3 (m.d 0 2) (by simp) with h4941 | h4941
                      · rcases p4920_3 (m.d 0 3) (by simp) with h4942 | h4942
                        · linarith only [h4, h4942, hlam]
                        · rcases p4920_3 (m.d 0 4) (by simp) with h4944 | h4944
                          · linarith only [h4944, h5, hlam]
                          · linarith only [h4944, h7, hlam]
                      · linarith only [h4, h4941, hlam]
                    · linarith only [h1, h4940, hlam]
                  · have p4920_0 := h4920c.1
                    have p4920_1 := h4920c.2.1
                    have p4920_2 := h4920c.2.2.1
                    have p4920_3 := h4920c.2.2.2
                    rcases p4920_3 (m.d 0 1) (by simp) with h4949 | h4949
                    · rcases p4920_3 (m.d 0 2) (by simp) with h4950 | h4950
                      · rcases p4920_3 (m.d 0 3) (by simp) with h4951 | h4951
                        · linarith only [h4, h4951, hlam]
                        · rcases p4920_3 (m.d 0 4) (by simp) with h4953 | h4953
                          · linarith only [h4953, h5, hlam]
                          · rcases p4920_3 (m.d 0 5) (by simp) with h4955 | h4955
                            · linarith only [h4955, h6, hlam]
                            · rcases h2bigk with h4957c | h4957c | h4957c | h4957c | h4957c | h4957c | h4957c | h4957c | h4957c | h4957c | h4957c | h4957c | h4957c | h4957c | h4957c | h4957c | h4957c | h4957c | h4957c | h4957c | h4957c | h4957c | h4957c | h4957c | h4957c
                              · have p4957_0 := h4957c.1
                                have p4957_1 := h4957c.2.1
                                have p4957_2 := h4957c.2.2.1
                                have p4957_3 := h4957c.2.2.2
                                linarith only [hlam, p4957_0]
                              · have p4957_0 := h4957c.1
                                have p4957_1 := h4957c.2.1
                                have p4957_2 := h4957c.2.2.1
                                have p4957_3 := h4957c.2.2.2
                                linarith only [h0, h4907, h4918, hc01, hc45, hlam, hphi, ht0b, ht5b, p4957_1]
                              · have p4957_0 := h4957c.1
                                have p4957_1 := h4957c.2.1
                                have p4957_2 := h4957c.2.2.1
                                have p4957_3 := h4957c.2.2.2
                                rcases p4957_3 (m.d 0 2) (by simp) with h4960 | h4960
                                · rcases p4957_3 (m.d 1 2) (by simp) with h4961 | h4961
                                  · linarith only [h0, h4961, hlam]
                                  · linarith only [h4906, h4961, hlam]
                                · linarith only [h4960, hlam, p4957_0]
                              · have p4957_0 := h4957c.1
                                have p4957_1 := h4957c.2.1
                                have p4957_2 := h4957c.2.2.1
                                have p4957_3 := h4957c.2.2.2
                                rcases p4957_3 (m.d 0 2) (by simp) with h4965 | h4965
                                · rcases p4957_3 (m.d 1 2) (by simp) with h4966 | h4966
                                  · linarith only [h0, h4966, hlam]
                                  · linarith only [h4907, h4966, hlam]
                                · linarith only [h4965, hlam, p4957_0]
                              · have p4957_0 := h4957c.1
                                have p4957_1 := h4957c.2.1
                                have p4957_2 := h4957c.2.2.1
                                have p4957_3 := h4957c.2.2.2
                                rcases p4957_3 (m.d 0 2) (by simp) with h4970 | h4970
                                · rcases p4957_3 (m.d 1 2) (by simp) with h4971 | h4971
                                  · linarith only [h0, h4971, hlam]
                                  · linarith only [h4908, h4971, hlam]
                                · linarith only [h4970, hlam, p4957_0]
                              · have p4957_0 := h4957c.1
                                have p4957_1 := h4957c.2.1
                                have p4957_2 := h4957c.2.2.1
                                have p4957_3 := h4957c.2.2.2
                                linarith only [h0, hlam, p4957_0]
                              · have p4957_0 := h4957c.1
                                have p4957_1 := h4957c.2.1
                                have p4957_2 := h4957c.2.2.1
                                have p4957_3 := h4957c.2.2.2
                                linarith only [hlam, p4957_0]
                              · have p4957_0 := h4957c.1
                                have p4957_1 := h4957c.2.1
                                have p4957_2 := h4957c.2.2.1
                                have p4957_3 := h4957c.2.2.2
                                rcases p4957_3 (m.d 0 2) (by simp) with h4977 | h4977
                                · rcases p4957_3 (m.d 1 2) (by simp) with h4978 | h4978
                                  · rcases p4957_3 (m.d 2 3) (by simp) with h4979 | h4979
                                    · linarith only [h4979, hlam, p4957_0]
                                    · rcases p4957_3 (m.d 2 4) (by simp) with h4981 | h4981
                                      · linarith only [h4907, h4981, hlam]
                                      · linarith only [h4914, h4981, hlam]
                                  · linarith only [h4978, hlam, p4957_0]
                                · linarith only [h4, h4977, hlam]
                              · have p4957_0 := h4957c.1
                                have p4957_1 := h4957c.2.1
                                have p4957_2 := h4957c.2.2.1
                                have p4957_3 := h4957c.2.2.2
                                linarith only [h0, h4918, hc01, hc45, hlam, hphi, ht0b, ht5b, p4957_1]
                              · have p4957_0 := h4957c.1
                                have p4957_1 := h4957c.2.1
                                have p4957_2 := h4957c.2.2.1
                                have p4957_3 := h4957c.2.2.2
                                rcases p4957_3 (m.d 0 2) (by simp) with h4987 | h4987
                                · rcases p4957_3 (m.d 1 2) (by simp) with h4988 | h4988
                                  · rcases p4957_3 (m.d 2 3) (by simp) with h4989 | h4989
                                    · linarith only [h4906, h4989, hlam]
                                    · rcases p4957_3 (m.d 2 4) (by simp) with h4991 | h4991
                                      · linarith only [h4907, h4991, hlam]
                                      · linarith only [h4918, h4991, hlam]
                                  · linarith only [h4988, hlam, p4957_0]
                                · linarith only [h4987, h6, hlam]
                              · have p4957_0 := h4957c.1
                                have p4957_1 := h4957c.2.1
                                have p4957_2 := h4957c.2.2.1
                                have p4957_3 := h4957c.2.2.2
                                linarith only [h4, hlam, p4957_0]
                              · have p4957_0 := h4957c.1
                                have p4957_1 := h4957c.2.1
                                have p4957_2 := h4957c.2.2.1
                                have p4957_3 := h4957c.2.2.2
                                linarith only [h4906, hlam, p4957_0]
                              · have p4957_0 := h4957c.1
                                have p4957_1 := h4957c.2.1
                                have p4957_2 := h4957c.2.2.1
                                have p4957_3 := h4957c.2.2.2
                                linarith only [hlam, p4957_0]
                              · have p4957_0 := h4957c.1
                                have p4957_1 := h4957c.2.1
                                have p4957_2 := h4957c.2.2.1
                                have p4957_3 := h4957c.2.2.2
                                linarith only [h4914, hlam, p4957_0]
                              · have p4957_0 := h4957c.1
                                have p4957_1 := h4957c.2.1
                                have p4957_2 := h4957c.2.2.1
                                have p4957_3 := h4957c.2.2.2
                                linarith only [h4916, hlam, p4957_0]
                              · have p4957_0 := h4957c.1
                                have p4957_1 := h4957c.2.1
                                have p4957_2 := h4957c.2.2.1
                                have p4957_3 := h4957c.2.2.2
                                linarith only [h5, hlam, p4957_0]
                              · have p4957_0 := h4957c.1
                                have p4957_1 := h4957c.2.1
                                have p4957_2 := h4957c.2.2.1
                                have p4957_3 := h4957c.2.2.2
                                linarith only [h4907, hlam, p4957_0]
                              · have p4957_0 := h4957c.1
                                have p4957_1 := h4957c.2.1
                                have p4957_2 := h4957c.2.2.1
                                have p4957_3 := h4957c.2.2.2
                                linarith only [h0, h2, h4907, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4920_1, p4957_1]
                              · have p4957_0 := h4957c.1
                                have p4957_1 := h4957c.2.1
                                have p4957_2 := h4957c.2.2.1
                                have p4957_3 := h4957c.2.2.2
                                linarith only [hlam, p4957_0]
                              · have p4957_0 := h4957c.1
                                have p4957_1 := h4957c.2.1
                                have p4957_2 := h4957c.2.2.1
                                have p4957_3 := h4957c.2.2.2
                                linarith only [h0, h2, h4907, hc01, hc25, hlam, hphi, ht0b, ht5b, p4920_1, p4957_1]
                              · have p4957_0 := h4957c.1
                                have p4957_1 := h4957c.2.1
                                have p4957_2 := h4957c.2.2.1
                                have p4957_3 := h4957c.2.2.2
                                linarith only [h6, hlam, p4957_0]
                              · have p4957_0 := h4957c.1
                                have p4957_1 := h4957c.2.1
                                have p4957_2 := h4957c.2.2.1
                                have p4957_3 := h4957c.2.2.2
                                linarith only [h4908, hlam, p4957_0]
                              · have p4957_0 := h4957c.1
                                have p4957_1 := h4957c.2.1
                                have p4957_2 := h4957c.2.2.1
                                have p4957_3 := h4957c.2.2.2
                                linarith only [h0, h4905, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4920_1, p4957_1]
                              · have p4957_0 := h4957c.1
                                have p4957_1 := h4957c.2.1
                                have p4957_2 := h4957c.2.2.1
                                have p4957_3 := h4957c.2.2.2
                                linarith only [h4918, hlam, p4957_0]
                              · have p4957_0 := h4957c.1
                                have p4957_1 := h4957c.2.1
                                have p4957_2 := h4957c.2.2.1
                                have p4957_3 := h4957c.2.2.2
                                linarith only [hlam, p4957_0]
                      · linarith only [h4950, h5, hlam]
                    · linarith only [h2, h4949, hlam]
                  · have p4920_0 := h4920c.1
                    have p4920_1 := h4920c.2.1
                    have p4920_2 := h4920c.2.2.1
                    have p4920_3 := h4920c.2.2.2
                    rcases p4920_3 (m.d 0 1) (by simp) with h5013 | h5013
                    · rcases p4920_3 (m.d 0 2) (by simp) with h5014 | h5014
                      · rcases p4920_3 (m.d 0 3) (by simp) with h5015 | h5015
                        · linarith only [h4, h5015, hlam]
                        · rcases p4920_3 (m.d 0 4) (by simp) with h5017 | h5017
                          · linarith only [h5, h5017, hlam]
                          · linarith only [h4905, h5017, hlam]
                      · linarith only [h5014, h6, hlam]
                    · linarith only [h3, h5013, hlam]
                  · have p4920_0 := h4920c.1
                    have p4920_1 := h4920c.2.1
                    have p4920_2 := h4920c.2.2.1
                    have p4920_3 := h4920c.2.2.2
                    linarith only [h1, hlam, p4920_1]
                  · have p4920_0 := h4920c.1
                    have p4920_1 := h4920c.2.1
                    have p4920_2 := h4920c.2.2.1
                    have p4920_3 := h4920c.2.2.2
                    linarith only [h4, hlam, p4920_1]
                  · have p4920_0 := h4920c.1
                    have p4920_1 := h4920c.2.1
                    have p4920_2 := h4920c.2.2.1
                    have p4920_3 := h4920c.2.2.2
                    linarith only [hlam, p4920_0]
                  · have p4920_0 := h4920c.1
                    have p4920_1 := h4920c.2.1
                    have p4920_2 := h4920c.2.2.1
                    have p4920_3 := h4920c.2.2.2
                    linarith only [h7, hlam, p4920_1]
                  · have p4920_0 := h4920c.1
                    have p4920_1 := h4920c.2.1
                    have p4920_2 := h4920c.2.2.1
                    have p4920_3 := h4920c.2.2.2
                    linarith only [h4388, hlam, p4920_1]
                  · have p4920_0 := h4920c.1
                    have p4920_1 := h4920c.2.1
                    have p4920_2 := h4920c.2.2.1
                    have p4920_3 := h4920c.2.2.2
                    linarith only [h2, hlam, p4920_0]
                  · have p4920_0 := h4920c.1
                    have p4920_1 := h4920c.2.1
                    have p4920_2 := h4920c.2.2.1
                    have p4920_3 := h4920c.2.2.2
                    linarith only [h5, hlam, p4920_0]
                  · have p4920_0 := h4920c.1
                    have p4920_1 := h4920c.2.1
                    have p4920_2 := h4920c.2.2.1
                    have p4920_3 := h4920c.2.2.2
                    rcases p4920_3 (m.d 0 1) (by simp) with h5029 | h5029
                    · rcases p4920_3 (m.d 0 2) (by simp) with h5030 | h5030
                      · rcases p4920_3 (m.d 0 3) (by simp) with h5031 | h5031
                        · linarith only [h5031, h7, hlam]
                        · rcases p4920_3 (m.d 0 4) (by simp) with h5033 | h5033
                          · rcases p4920_3 (m.d 0 5) (by simp) with h5034 | h5034
                            · linarith only [h4905, h5034, hlam]
                            · linarith only [h4388, h5034, hlam]
                          · linarith only [h5033, h7, hlam]
                      · linarith only [h4, h5030, hlam]
                    · linarith only [h1, h5029, hlam]
                  · have p4920_0 := h4920c.1
                    have p4920_1 := h4920c.2.1
                    have p4920_2 := h4920c.2.2.1
                    have p4920_3 := h4920c.2.2.2
                    linarith only [hlam, p4920_0]
                  · have p4920_0 := h4920c.1
                    have p4920_1 := h4920c.2.1
                    have p4920_2 := h4920c.2.2.1
                    have p4920_3 := h4920c.2.2.2
                    rcases p4920_3 (m.d 0 1) (by simp) with h5041 | h5041
                    · rcases p4920_3 (m.d 0 2) (by simp) with h5042 | h5042
                      · rcases p4920_3 (m.d 0 3) (by simp) with h5043 | h5043
                        · linarith only [h5043, h7, hlam]
                        · rcases p4920_3 (m.d 0 4) (by simp) with h5045 | h5045
                          · rcases p4920_3 (m.d 0 5) (by simp) with h5046 | h5046
                            · linarith only [h4905, h5046, hlam]
                            · rcases h2bigk with h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c
                              · have p5048_0 := h5048c.1
                                have p5048_1 := h5048c.2.1
                                have p5048_2 := h5048c.2.2.1
                                have p5048_3 := h5048c.2.2.2
                                linarith only [hlam, p5048_0]
                              · have p5048_0 := h5048c.1
                                have p5048_1 := h5048c.2.1
                                have p5048_2 := h5048c.2.2.1
                                have p5048_3 := h5048c.2.2.2
                                linarith only [h0, h4907, h4918, hc01, hc45, hlam, hphi, ht0b, ht5b, p5048_1]
                              · have p5048_0 := h5048c.1
                                have p5048_1 := h5048c.2.1
                                have p5048_2 := h5048c.2.2.1
                                have p5048_3 := h5048c.2.2.2
                                rcases p5048_3 (m.d 0 2) (by simp) with h5051 | h5051
                                · rcases p5048_3 (m.d 1 2) (by simp) with h5052 | h5052
                                  · linarith only [h0, h5052, hlam]
                                  · linarith only [h4906, h5052, hlam]
                                · linarith only [h5051, hlam, p5048_0]
                              · have p5048_0 := h5048c.1
                                have p5048_1 := h5048c.2.1
                                have p5048_2 := h5048c.2.2.1
                                have p5048_3 := h5048c.2.2.2
                                rcases p5048_3 (m.d 0 2) (by simp) with h5056 | h5056
                                · rcases p5048_3 (m.d 1 2) (by simp) with h5057 | h5057
                                  · linarith only [h0, h5057, hlam]
                                  · linarith only [h4907, h5057, hlam]
                                · linarith only [h5056, hlam, p5048_0]
                              · have p5048_0 := h5048c.1
                                have p5048_1 := h5048c.2.1
                                have p5048_2 := h5048c.2.2.1
                                have p5048_3 := h5048c.2.2.2
                                rcases p5048_3 (m.d 0 2) (by simp) with h5061 | h5061
                                · rcases p5048_3 (m.d 1 2) (by simp) with h5062 | h5062
                                  · linarith only [h0, h5062, hlam]
                                  · linarith only [h4908, h5062, hlam]
                                · linarith only [h5061, hlam, p5048_0]
                              · have p5048_0 := h5048c.1
                                have p5048_1 := h5048c.2.1
                                have p5048_2 := h5048c.2.2.1
                                have p5048_3 := h5048c.2.2.2
                                linarith only [h0, hlam, p5048_0]
                              · have p5048_0 := h5048c.1
                                have p5048_1 := h5048c.2.1
                                have p5048_2 := h5048c.2.2.1
                                have p5048_3 := h5048c.2.2.2
                                linarith only [hlam, p5048_0]
                              · have p5048_0 := h5048c.1
                                have p5048_1 := h5048c.2.1
                                have p5048_2 := h5048c.2.2.1
                                have p5048_3 := h5048c.2.2.2
                                rcases p5048_3 (m.d 0 2) (by simp) with h5068 | h5068
                                · rcases p5048_3 (m.d 1 2) (by simp) with h5069 | h5069
                                  · rcases p5048_3 (m.d 2 3) (by simp) with h5070 | h5070
                                    · linarith only [h5070, hlam, p5048_0]
                                    · rcases p5048_3 (m.d 2 4) (by simp) with h5072 | h5072
                                      · linarith only [h4907, h5072, hlam]
                                      · linarith only [h4914, h5072, hlam]
                                  · linarith only [h5069, hlam, p5048_0]
                                · linarith only [h4, h5068, hlam]
                              · have p5048_0 := h5048c.1
                                have p5048_1 := h5048c.2.1
                                have p5048_2 := h5048c.2.2.1
                                have p5048_3 := h5048c.2.2.2
                                linarith only [h0, h4918, hc01, hc45, hlam, hphi, ht0b, ht5b, p5048_1]
                              · have p5048_0 := h5048c.1
                                have p5048_1 := h5048c.2.1
                                have p5048_2 := h5048c.2.2.1
                                have p5048_3 := h5048c.2.2.2
                                rcases p5048_3 (m.d 0 2) (by simp) with h5078 | h5078
                                · rcases p5048_3 (m.d 1 2) (by simp) with h5079 | h5079
                                  · rcases p5048_3 (m.d 2 3) (by simp) with h5080 | h5080
                                    · linarith only [h4906, h5080, hlam]
                                    · rcases p5048_3 (m.d 2 4) (by simp) with h5082 | h5082
                                      · linarith only [h4907, h5082, hlam]
                                      · linarith only [h4918, h5082, hlam]
                                  · linarith only [h5079, hlam, p5048_0]
                                · linarith only [h5078, h6, hlam]
                              · have p5048_0 := h5048c.1
                                have p5048_1 := h5048c.2.1
                                have p5048_2 := h5048c.2.2.1
                                have p5048_3 := h5048c.2.2.2
                                linarith only [h4, hlam, p5048_0]
                              · have p5048_0 := h5048c.1
                                have p5048_1 := h5048c.2.1
                                have p5048_2 := h5048c.2.2.1
                                have p5048_3 := h5048c.2.2.2
                                linarith only [h4906, hlam, p5048_0]
                              · have p5048_0 := h5048c.1
                                have p5048_1 := h5048c.2.1
                                have p5048_2 := h5048c.2.2.1
                                have p5048_3 := h5048c.2.2.2
                                linarith only [hlam, p5048_0]
                              · have p5048_0 := h5048c.1
                                have p5048_1 := h5048c.2.1
                                have p5048_2 := h5048c.2.2.1
                                have p5048_3 := h5048c.2.2.2
                                linarith only [h4914, hlam, p5048_0]
                              · have p5048_0 := h5048c.1
                                have p5048_1 := h5048c.2.1
                                have p5048_2 := h5048c.2.2.1
                                have p5048_3 := h5048c.2.2.2
                                linarith only [h4916, hlam, p5048_0]
                              · have p5048_0 := h5048c.1
                                have p5048_1 := h5048c.2.1
                                have p5048_2 := h5048c.2.2.1
                                have p5048_3 := h5048c.2.2.2
                                linarith only [h5, hlam, p5048_0]
                              · have p5048_0 := h5048c.1
                                have p5048_1 := h5048c.2.1
                                have p5048_2 := h5048c.2.2.1
                                have p5048_3 := h5048c.2.2.2
                                linarith only [h4907, hlam, p5048_0]
                              · have p5048_0 := h5048c.1
                                have p5048_1 := h5048c.2.1
                                have p5048_2 := h5048c.2.2.1
                                have p5048_3 := h5048c.2.2.2
                                linarith only [h0, h4907, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5048_1]
                              · have p5048_0 := h5048c.1
                                have p5048_1 := h5048c.2.1
                                have p5048_2 := h5048c.2.2.1
                                have p5048_3 := h5048c.2.2.2
                                linarith only [hlam, p5048_0]
                              · have p5048_0 := h5048c.1
                                have p5048_1 := h5048c.2.1
                                have p5048_2 := h5048c.2.2.1
                                have p5048_3 := h5048c.2.2.2
                                linarith only [h0, h4907, hc01, hc25, hlam, hphi, ht0b, ht5b, p5048_1]
                              · have p5048_0 := h5048c.1
                                have p5048_1 := h5048c.2.1
                                have p5048_2 := h5048c.2.2.1
                                have p5048_3 := h5048c.2.2.2
                                linarith only [h6, hlam, p5048_0]
                              · have p5048_0 := h5048c.1
                                have p5048_1 := h5048c.2.1
                                have p5048_2 := h5048c.2.2.1
                                have p5048_3 := h5048c.2.2.2
                                linarith only [h4908, hlam, p5048_0]
                              · have p5048_0 := h5048c.1
                                have p5048_1 := h5048c.2.1
                                have p5048_2 := h5048c.2.2.1
                                have p5048_3 := h5048c.2.2.2
                                linarith only [h6, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4920_1, p5048_1]
                              · have p5048_0 := h5048c.1
                                have p5048_1 := h5048c.2.1
                                have p5048_2 := h5048c.2.2.1
                                have p5048_3 := h5048c.2.2.2
                                linarith only [h4918, hlam, p5048_0]
                              · have p5048_0 := h5048c.1
                                have p5048_1 := h5048c.2.1
                                have p5048_2 := h5048c.2.2.1
                                have p5048_3 := h5048c.2.2.2
                                linarith only [hlam, p5048_0]
                          · linarith only [h4905, h5045, hlam]
                      · linarith only [h5042, h6, hlam]
                    · linarith only [h3, h5041, hlam]
                  · have p4920_0 := h4920c.1
                    have p4920_1 := h4920c.2.1
                    have p4920_2 := h4920c.2.2.1
                    have p4920_3 := h4920c.2.2.2
                    linarith only [h3, hlam, p4920_0]
                  · have p4920_0 := h4920c.1
                    have p4920_1 := h4920c.2.1
                    have p4920_2 := h4920c.2.2.1
                    have p4920_3 := h4920c.2.2.2
                    linarith only [h6, hlam, p4920_1]
                  · have p4920_0 := h4920c.1
                    have p4920_1 := h4920c.2.1
                    have p4920_2 := h4920c.2.2.1
                    have p4920_3 := h4920c.2.2.2
                    rcases p4920_3 (m.d 0 1) (by simp) with h5107 | h5107
                    · rcases p4920_3 (m.d 0 2) (by simp) with h5108 | h5108
                      · rcases p4920_3 (m.d 0 3) (by simp) with h5109 | h5109
                        · linarith only [h4388, h5109, hlam]
                        · rcases p4920_3 (m.d 0 4) (by simp) with h5111 | h5111
                          · rcases p4920_3 (m.d 0 5) (by simp) with h5112 | h5112
                            · rcases h2bigk with h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c | h5113c
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [hlam, p5113_0]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [h0, h4907, h4918, hc01, hc45, hlam, hphi, ht0b, ht5b, p5113_1]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                rcases p5113_3 (m.d 0 2) (by simp) with h5116 | h5116
                                · rcases p5113_3 (m.d 1 2) (by simp) with h5117 | h5117
                                  · linarith only [h0, h5117, hlam]
                                  · linarith only [h4906, h5117, hlam]
                                · linarith only [h5116, hlam, p5113_0]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                rcases p5113_3 (m.d 0 2) (by simp) with h5121 | h5121
                                · rcases p5113_3 (m.d 1 2) (by simp) with h5122 | h5122
                                  · linarith only [h0, h5122, hlam]
                                  · linarith only [h4907, h5122, hlam]
                                · linarith only [h5121, hlam, p5113_0]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                rcases p5113_3 (m.d 0 2) (by simp) with h5126 | h5126
                                · rcases p5113_3 (m.d 1 2) (by simp) with h5127 | h5127
                                  · linarith only [h0, h5127, hlam]
                                  · linarith only [h4908, h5127, hlam]
                                · linarith only [h5126, hlam, p5113_0]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [h0, hlam, p5113_0]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [hlam, p5113_0]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                rcases p5113_3 (m.d 0 2) (by simp) with h5133 | h5133
                                · rcases p5113_3 (m.d 1 2) (by simp) with h5134 | h5134
                                  · rcases p5113_3 (m.d 2 3) (by simp) with h5135 | h5135
                                    · linarith only [h5135, hlam, p5113_0]
                                    · rcases p5113_3 (m.d 2 4) (by simp) with h5137 | h5137
                                      · linarith only [h4907, h5137, hlam]
                                      · linarith only [h4914, h5137, hlam]
                                  · linarith only [h5134, hlam, p5113_0]
                                · linarith only [h4, h5133, hlam]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [h0, h4918, hc01, hc45, hlam, hphi, ht0b, ht5b, p5113_1]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                rcases p5113_3 (m.d 0 2) (by simp) with h5143 | h5143
                                · rcases p5113_3 (m.d 1 2) (by simp) with h5144 | h5144
                                  · rcases p5113_3 (m.d 2 3) (by simp) with h5145 | h5145
                                    · linarith only [h4906, h5145, hlam]
                                    · rcases p5113_3 (m.d 2 4) (by simp) with h5147 | h5147
                                      · linarith only [h4907, h5147, hlam]
                                      · linarith only [h4918, h5147, hlam]
                                  · linarith only [h5144, hlam, p5113_0]
                                · linarith only [h5143, h6, hlam]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [h4, hlam, p5113_0]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [h4906, hlam, p5113_0]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [hlam, p5113_0]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [h4914, hlam, p5113_0]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [h4916, hlam, p5113_0]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [h5, hlam, p5113_0]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [h4907, hlam, p5113_0]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [h0, h4907, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5113_1]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [hlam, p5113_0]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [h0, h4907, hc01, hc25, hlam, hphi, ht0b, ht5b, p5113_1]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [h6, hlam, p5113_0]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [h4908, hlam, p5113_0]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [h0, h4908, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5113_1]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [h4918, hlam, p5113_0]
                              · have p5113_0 := h5113c.1
                                have p5113_1 := h5113c.2.1
                                have p5113_2 := h5113c.2.2.1
                                have p5113_3 := h5113c.2.2.2
                                linarith only [hlam, p5113_0]
                            · linarith only [h4388, h5112, hlam]
                          · linarith only [h5111, h7, hlam]
                      · linarith only [h4, h5108, hlam]
                    · linarith only [h1, h5107, hlam]
                  · have p4920_0 := h4920c.1
                    have p4920_1 := h4920c.2.1
                    have p4920_2 := h4920c.2.2.1
                    have p4920_3 := h4920c.2.2.2
                    linarith only [h4905, hlam, p4920_1]
                  · have p4920_0 := h4920c.1
                    have p4920_1 := h4920c.2.1
                    have p4920_2 := h4920c.2.2.1
                    have p4920_3 := h4920c.2.2.2
                    linarith only [hlam, p4920_0]
                · linarith only [h4905, h4919, h7, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h5174 | h5174
                · rcases h0bigk with h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c
                  · have p5175_0 := h5175c.1
                    have p5175_1 := h5175c.2.1
                    have p5175_2 := h5175c.2.2.1
                    have p5175_3 := h5175c.2.2.2
                    linarith only [hlam, p5175_0]
                  · have p5175_0 := h5175c.1
                    have p5175_1 := h5175c.2.1
                    have p5175_2 := h5175c.2.2.1
                    have p5175_3 := h5175c.2.2.2
                    linarith only [h2, h4913, h4914, h4918, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5175_1]
                  · have p5175_0 := h5175c.1
                    have p5175_1 := h5175c.2.1
                    have p5175_2 := h5175c.2.2.1
                    have p5175_3 := h5175c.2.2.2
                    rcases p5175_3 (m.d 0 1) (by simp) with h5178 | h5178
                    · rcases p5175_3 (m.d 0 2) (by simp) with h5179 | h5179
                      · linarith only [h0, h5179, hlam]
                      · linarith only [h4, h5179, hlam]
                    · linarith only [h1, h5178, hlam]
                  · have p5175_0 := h5175c.1
                    have p5175_1 := h5175c.2.1
                    have p5175_2 := h5175c.2.2.1
                    have p5175_3 := h5175c.2.2.2
                    linarith only [h2, h4913, h4914, h4918, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5175_1]
                  · have p5175_0 := h5175c.1
                    have p5175_1 := h5175c.2.1
                    have p5175_2 := h5175c.2.2.1
                    have p5175_3 := h5175c.2.2.2
                    rcases p5175_3 (m.d 0 1) (by simp) with h5184 | h5184
                    · rcases p5175_3 (m.d 0 2) (by simp) with h5185 | h5185
                      · linarith only [h0, h5185, hlam]
                      · linarith only [h5185, h6, hlam]
                    · linarith only [h3, h5184, hlam]
                  · have p5175_0 := h5175c.1
                    have p5175_1 := h5175c.2.1
                    have p5175_2 := h5175c.2.2.1
                    have p5175_3 := h5175c.2.2.2
                    linarith only [h0, hlam, p5175_0]
                  · have p5175_0 := h5175c.1
                    have p5175_1 := h5175c.2.1
                    have p5175_2 := h5175c.2.2.1
                    have p5175_3 := h5175c.2.2.2
                    linarith only [hlam, p5175_0]
                  · have p5175_0 := h5175c.1
                    have p5175_1 := h5175c.2.1
                    have p5175_2 := h5175c.2.2.1
                    have p5175_3 := h5175c.2.2.2
                    rcases p5175_3 (m.d 0 1) (by simp) with h5191 | h5191
                    · rcases p5175_3 (m.d 0 2) (by simp) with h5192 | h5192
                      · rcases p5175_3 (m.d 0 3) (by simp) with h5193 | h5193
                        · linarith only [h4, h5193, hlam]
                        · rcases p5175_3 (m.d 0 4) (by simp) with h5195 | h5195
                          · linarith only [h5, h5195, hlam]
                          · linarith only [h5195, h7, hlam]
                      · linarith only [h4, h5192, hlam]
                    · linarith only [h1, h5191, hlam]
                  · have p5175_0 := h5175c.1
                    have p5175_1 := h5175c.2.1
                    have p5175_2 := h5175c.2.2.1
                    have p5175_3 := h5175c.2.2.2
                    linarith only [h2, h4913, h4914, h4918, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5175_1]
                  · have p5175_0 := h5175c.1
                    have p5175_1 := h5175c.2.1
                    have p5175_2 := h5175c.2.2.1
                    have p5175_3 := h5175c.2.2.2
                    rcases p5175_3 (m.d 0 1) (by simp) with h5201 | h5201
                    · rcases p5175_3 (m.d 0 2) (by simp) with h5202 | h5202
                      · rcases p5175_3 (m.d 0 3) (by simp) with h5203 | h5203
                        · linarith only [h4, h5203, hlam]
                        · rcases p5175_3 (m.d 0 4) (by simp) with h5205 | h5205
                          · linarith only [h5, h5205, hlam]
                          · linarith only [h4905, h5205, hlam]
                      · linarith only [h5202, h6, hlam]
                    · linarith only [h3, h5201, hlam]
                  · have p5175_0 := h5175c.1
                    have p5175_1 := h5175c.2.1
                    have p5175_2 := h5175c.2.2.1
                    have p5175_3 := h5175c.2.2.2
                    linarith only [h1, hlam, p5175_1]
                  · have p5175_0 := h5175c.1
                    have p5175_1 := h5175c.2.1
                    have p5175_2 := h5175c.2.2.1
                    have p5175_3 := h5175c.2.2.2
                    linarith only [h4, hlam, p5175_1]
                  · have p5175_0 := h5175c.1
                    have p5175_1 := h5175c.2.1
                    have p5175_2 := h5175c.2.2.1
                    have p5175_3 := h5175c.2.2.2
                    linarith only [hlam, p5175_0]
                  · have p5175_0 := h5175c.1
                    have p5175_1 := h5175c.2.1
                    have p5175_2 := h5175c.2.2.1
                    have p5175_3 := h5175c.2.2.2
                    linarith only [h7, hlam, p5175_1]
                  · have p5175_0 := h5175c.1
                    have p5175_1 := h5175c.2.1
                    have p5175_2 := h5175c.2.2.1
                    have p5175_3 := h5175c.2.2.2
                    linarith only [h4388, hlam, p5175_1]
                  · have p5175_0 := h5175c.1
                    have p5175_1 := h5175c.2.1
                    have p5175_2 := h5175c.2.2.1
                    have p5175_3 := h5175c.2.2.2
                    linarith only [h2, hlam, p5175_0]
                  · have p5175_0 := h5175c.1
                    have p5175_1 := h5175c.2.1
                    have p5175_2 := h5175c.2.2.1
                    have p5175_3 := h5175c.2.2.2
                    linarith only [h5, hlam, p5175_0]
                  · have p5175_0 := h5175c.1
                    have p5175_1 := h5175c.2.1
                    have p5175_2 := h5175c.2.2.1
                    have p5175_3 := h5175c.2.2.2
                    rcases p5175_3 (m.d 0 1) (by simp) with h5217 | h5217
                    · rcases p5175_3 (m.d 0 2) (by simp) with h5218 | h5218
                      · rcases p5175_3 (m.d 0 3) (by simp) with h5219 | h5219
                        · linarith only [h5219, h7, hlam]
                        · rcases p5175_3 (m.d 0 4) (by simp) with h5221 | h5221
                          · rcases p5175_3 (m.d 0 5) (by simp) with h5222 | h5222
                            · linarith only [h4905, h5222, hlam]
                            · linarith only [h4388, h5222, hlam]
                          · linarith only [h5221, h7, hlam]
                      · linarith only [h4, h5218, hlam]
                    · linarith only [h1, h5217, hlam]
                  · have p5175_0 := h5175c.1
                    have p5175_1 := h5175c.2.1
                    have p5175_2 := h5175c.2.2.1
                    have p5175_3 := h5175c.2.2.2
                    linarith only [hlam, p5175_0]
                  · have p5175_0 := h5175c.1
                    have p5175_1 := h5175c.2.1
                    have p5175_2 := h5175c.2.2.1
                    have p5175_3 := h5175c.2.2.2
                    linarith only [h4905, h4914, h4918, h7, hc23, hc34, hlam, hphi, p5175_1]
                  · have p5175_0 := h5175c.1
                    have p5175_1 := h5175c.2.1
                    have p5175_2 := h5175c.2.2.1
                    have p5175_3 := h5175c.2.2.2
                    linarith only [h3, hlam, p5175_0]
                  · have p5175_0 := h5175c.1
                    have p5175_1 := h5175c.2.1
                    have p5175_2 := h5175c.2.2.1
                    have p5175_3 := h5175c.2.2.2
                    linarith only [h6, hlam, p5175_1]
                  · have p5175_0 := h5175c.1
                    have p5175_1 := h5175c.2.1
                    have p5175_2 := h5175c.2.2.1
                    have p5175_3 := h5175c.2.2.2
                    rcases p5175_3 (m.d 0 1) (by simp) with h5232 | h5232
                    · rcases p5175_3 (m.d 0 2) (by simp) with h5233 | h5233
                      · rcases p5175_3 (m.d 0 3) (by simp) with h5234 | h5234
                        · linarith only [h4388, h5234, hlam]
                        · rcases p5175_3 (m.d 0 4) (by simp) with h5236 | h5236
                          · rcases p5175_3 (m.d 0 5) (by simp) with h5237 | h5237
                            · rcases h2bigk with h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c | h5238c
                              · have p5238_0 := h5238c.1
                                have p5238_1 := h5238c.2.1
                                have p5238_2 := h5238c.2.2.1
                                have p5238_3 := h5238c.2.2.2
                                linarith only [hlam, p5238_0]
                              · have p5238_0 := h5238c.1
                                have p5238_1 := h5238c.2.1
                                have p5238_2 := h5238c.2.2.1
                                have p5238_3 := h5238c.2.2.2
                                linarith only [h0, h4907, h4913, h4914, h4918, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5238_1]
                              · have p5238_0 := h5238c.1
                                have p5238_1 := h5238c.2.1
                                have p5238_2 := h5238c.2.2.1
                                have p5238_3 := h5238c.2.2.2
                                rcases p5238_3 (m.d 0 2) (by simp) with h5241 | h5241
                                · rcases p5238_3 (m.d 1 2) (by simp) with h5242 | h5242
                                  · linarith only [h0, h5242, hlam]
                                  · linarith only [h4906, h5242, hlam]
                                · linarith only [h5241, hlam, p5238_0]
                              · have p5238_0 := h5238c.1
                                have p5238_1 := h5238c.2.1
                                have p5238_2 := h5238c.2.2.1
                                have p5238_3 := h5238c.2.2.2
                                rcases p5238_3 (m.d 0 2) (by simp) with h5246 | h5246
                                · rcases p5238_3 (m.d 1 2) (by simp) with h5247 | h5247
                                  · linarith only [h0, h5247, hlam]
                                  · linarith only [h4907, h5247, hlam]
                                · linarith only [h5246, hlam, p5238_0]
                              · have p5238_0 := h5238c.1
                                have p5238_1 := h5238c.2.1
                                have p5238_2 := h5238c.2.2.1
                                have p5238_3 := h5238c.2.2.2
                                rcases p5238_3 (m.d 0 2) (by simp) with h5251 | h5251
                                · rcases p5238_3 (m.d 1 2) (by simp) with h5252 | h5252
                                  · linarith only [h0, h5252, hlam]
                                  · linarith only [h4908, h5252, hlam]
                                · linarith only [h5251, hlam, p5238_0]
                              · have p5238_0 := h5238c.1
                                have p5238_1 := h5238c.2.1
                                have p5238_2 := h5238c.2.2.1
                                have p5238_3 := h5238c.2.2.2
                                linarith only [h0, hlam, p5238_0]
                              · have p5238_0 := h5238c.1
                                have p5238_1 := h5238c.2.1
                                have p5238_2 := h5238c.2.2.1
                                have p5238_3 := h5238c.2.2.2
                                linarith only [hlam, p5238_0]
                              · have p5238_0 := h5238c.1
                                have p5238_1 := h5238c.2.1
                                have p5238_2 := h5238c.2.2.1
                                have p5238_3 := h5238c.2.2.2
                                rcases p5238_3 (m.d 0 2) (by simp) with h5258 | h5258
                                · rcases p5238_3 (m.d 1 2) (by simp) with h5259 | h5259
                                  · rcases p5238_3 (m.d 2 3) (by simp) with h5260 | h5260
                                    · linarith only [h5260, hlam, p5238_0]
                                    · rcases p5238_3 (m.d 2 4) (by simp) with h5262 | h5262
                                      · linarith only [h4907, h5262, hlam]
                                      · linarith only [h4914, h5262, hlam]
                                  · linarith only [h5259, hlam, p5238_0]
                                · linarith only [h4, h5258, hlam]
                              · have p5238_0 := h5238c.1
                                have p5238_1 := h5238c.2.1
                                have p5238_2 := h5238c.2.2.1
                                have p5238_3 := h5238c.2.2.2
                                rcases p5238_3 (m.d 0 2) (by simp) with h5267 | h5267
                                · rcases p5238_3 (m.d 1 2) (by simp) with h5268 | h5268
                                  · rcases p5238_3 (m.d 2 3) (by simp) with h5269 | h5269
                                    · linarith only [h4906, h5269, hlam]
                                    · rcases p5238_3 (m.d 2 4) (by simp) with h5271 | h5271
                                      · linarith only [h5271, hlam, p5238_0]
                                      · rcases p5238_3 (m.d 2 5) (by simp) with h5273 | h5273
                                        · linarith only [h4908, h5273, hlam]
                                        · linarith only [h4918, h5273, hlam]
                                  · linarith only [h5268, hlam, p5238_0]
                                · linarith only [h5, h5267, hlam]
                              · have p5238_0 := h5238c.1
                                have p5238_1 := h5238c.2.1
                                have p5238_2 := h5238c.2.2.1
                                have p5238_3 := h5238c.2.2.2
                                rcases p5238_3 (m.d 0 2) (by simp) with h5278 | h5278
                                · rcases p5238_3 (m.d 1 2) (by simp) with h5279 | h5279
                                  · rcases p5238_3 (m.d 2 3) (by simp) with h5280 | h5280
                                    · linarith only [h4906, h5280, hlam]
                                    · rcases p5238_3 (m.d 2 4) (by simp) with h5282 | h5282
                                      · linarith only [h4907, h5282, hlam]
                                      · rcases p5238_3 (m.d 2 5) (by simp) with h5284 | h5284
                                        · linarith only [h5284, hlam, p5238_0]
                                        · rcases h3bigk with h5286c | h5286c | h5286c | h5286c | h5286c | h5286c | h5286c | h5286c | h5286c | h5286c | h5286c | h5286c | h5286c | h5286c | h5286c | h5286c | h5286c | h5286c | h5286c | h5286c | h5286c | h5286c | h5286c | h5286c | h5286c
                                          · have p5286_0 := h5286c.1
                                            have p5286_1 := h5286c.2.1
                                            have p5286_2 := h5286c.2.2.1
                                            have p5286_3 := h5286c.2.2.2
                                            linarith only [hlam, p5286_0]
                                          · have p5286_0 := h5286c.1
                                            have p5286_1 := h5286c.2.1
                                            have p5286_2 := h5286c.2.2.1
                                            have p5286_3 := h5286c.2.2.2
                                            linarith only [h4906, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5175_1, p5286_1]
                                          · have p5286_0 := h5286c.1
                                            have p5286_1 := h5286c.2.1
                                            have p5286_2 := h5286c.2.2.1
                                            have p5286_3 := h5286c.2.2.2
                                            linarith only [h4388, hc23, hc35, hlam, hphi, p5175_1, p5286_1]
                                          · have p5286_0 := h5286c.1
                                            have p5286_1 := h5286c.2.1
                                            have p5286_2 := h5286c.2.2.1
                                            have p5286_3 := h5286c.2.2.2
                                            linarith only [h7, hlam, p5286_0]
                                          · have p5286_0 := h5286c.1
                                            have p5286_1 := h5286c.2.1
                                            have p5286_2 := h5286c.2.2.1
                                            have p5286_3 := h5286c.2.2.2
                                            linarith only [h4388, hlam, p5286_0]
                                          · have p5286_0 := h5286c.1
                                            have p5286_1 := h5286c.2.1
                                            have p5286_2 := h5286c.2.2.1
                                            have p5286_3 := h5286c.2.2.2
                                            linarith only [h1, hlam, p5286_0]
                                          · have p5286_0 := h5286c.1
                                            have p5286_1 := h5286c.2.1
                                            have p5286_2 := h5286c.2.2.1
                                            have p5286_3 := h5286c.2.2.2
                                            linarith only [hlam, p5286_0]
                                          · have p5286_0 := h5286c.1
                                            have p5286_1 := h5286c.2.1
                                            have p5286_2 := h5286c.2.2.1
                                            have p5286_3 := h5286c.2.2.2
                                            linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5286_1]
                                          · have p5286_0 := h5286c.1
                                            have p5286_1 := h5286c.2.1
                                            have p5286_2 := h5286c.2.2.1
                                            have p5286_3 := h5286c.2.2.2
                                            linarith only [h4909, hlam, p5286_0]
                                          · have p5286_0 := h5286c.1
                                            have p5286_1 := h5286c.2.1
                                            have p5286_2 := h5286c.2.2.1
                                            have p5286_3 := h5286c.2.2.2
                                            linarith only [h4911, hlam, p5286_0]
                                          · have p5286_0 := h5286c.1
                                            have p5286_1 := h5286c.2.1
                                            have p5286_2 := h5286c.2.2.1
                                            have p5286_3 := h5286c.2.2.2
                                            linarith only [h4, hlam, p5286_0]
                                          · have p5286_0 := h5286c.1
                                            have p5286_1 := h5286c.2.1
                                            have p5286_2 := h5286c.2.2.1
                                            have p5286_3 := h5286c.2.2.2
                                            linarith only [h4906, hlam, p5286_0]
                                          · have p5286_0 := h5286c.1
                                            have p5286_1 := h5286c.2.1
                                            have p5286_2 := h5286c.2.2.1
                                            have p5286_3 := h5286c.2.2.2
                                            linarith only [hlam, p5286_0]
                                          · have p5286_0 := h5286c.1
                                            have p5286_1 := h5286c.2.1
                                            have p5286_2 := h5286c.2.2.1
                                            have p5286_3 := h5286c.2.2.2
                                            linarith only [h4914, hlam, p5286_0]
                                          · have p5286_0 := h5286c.1
                                            have p5286_1 := h5286c.2.1
                                            have p5286_2 := h5286c.2.2.1
                                            have p5286_3 := h5286c.2.2.2
                                            linarith only [h4916, hlam, p5286_0]
                                          · have p5286_0 := h5286c.1
                                            have p5286_1 := h5286c.2.1
                                            have p5286_2 := h5286c.2.2.1
                                            have p5286_3 := h5286c.2.2.2
                                            linarith only [hc03, hc34, hlam, hphi, p5286_1]
                                          · have p5286_0 := h5286c.1
                                            have p5286_1 := h5286c.2.1
                                            have p5286_2 := h5286c.2.2.1
                                            have p5286_3 := h5286c.2.2.2
                                            linarith only [h4906, hc23, hc34, hlam, hphi, p5286_1]
                                          · have p5286_0 := h5286c.1
                                            have p5286_1 := h5286c.2.1
                                            have p5286_2 := h5286c.2.2.1
                                            have p5286_3 := h5286c.2.2.2
                                            linarith only [hc23, hc34, hlam, hphi, p5286_1]
                                          · have p5286_0 := h5286c.1
                                            have p5286_1 := h5286c.2.1
                                            have p5286_2 := h5286c.2.2.1
                                            have p5286_3 := h5286c.2.2.2
                                            linarith only [hlam, p5286_0]
                                          · have p5286_0 := h5286c.1
                                            have p5286_1 := h5286c.2.1
                                            have p5286_2 := h5286c.2.2.1
                                            have p5286_3 := h5286c.2.2.2
                                            linarith only [h1, h4388, h4906, hc23, hc34, hlam, hphi, p5286_1]
                                          · have p5286_0 := h5286c.1
                                            have p5286_1 := h5286c.2.1
                                            have p5286_2 := h5286c.2.2.1
                                            have p5286_3 := h5286c.2.2.2
                                            linarith only [h1, h4906, hc23, hc35, hlam, hphi, p5286_1]
                                          · have p5286_0 := h5286c.1
                                            have p5286_1 := h5286c.2.1
                                            have p5286_2 := h5286c.2.2.1
                                            have p5286_3 := h5286c.2.2.2
                                            linarith only [h4906, hc23, hc35, hlam, hphi, p5286_1]
                                          · have p5286_0 := h5286c.1
                                            have p5286_1 := h5286c.2.1
                                            have p5286_2 := h5286c.2.2.1
                                            have p5286_3 := h5286c.2.2.2
                                            linarith only [hc23, hc35, hlam, hphi, p5286_1]
                                          · have p5286_0 := h5286c.1
                                            have p5286_1 := h5286c.2.1
                                            have p5286_2 := h5286c.2.2.1
                                            have p5286_3 := h5286c.2.2.2
                                            linarith only [h5174, hlam, p5286_0]
                                          · have p5286_0 := h5286c.1
                                            have p5286_1 := h5286c.2.1
                                            have p5286_2 := h5286c.2.2.1
                                            have p5286_3 := h5286c.2.2.2
                                            linarith only [hlam, p5286_0]
                                  · linarith only [h5279, hlam, p5238_0]
                                · linarith only [h5278, h6, hlam]
                              · have p5238_0 := h5238c.1
                                have p5238_1 := h5238c.2.1
                                have p5238_2 := h5238c.2.2.1
                                have p5238_3 := h5238c.2.2.2
                                linarith only [h4, hlam, p5238_0]
                              · have p5238_0 := h5238c.1
                                have p5238_1 := h5238c.2.1
                                have p5238_2 := h5238c.2.2.1
                                have p5238_3 := h5238c.2.2.2
                                linarith only [h4906, hlam, p5238_0]
                              · have p5238_0 := h5238c.1
                                have p5238_1 := h5238c.2.1
                                have p5238_2 := h5238c.2.2.1
                                have p5238_3 := h5238c.2.2.2
                                linarith only [hlam, p5238_0]
                              · have p5238_0 := h5238c.1
                                have p5238_1 := h5238c.2.1
                                have p5238_2 := h5238c.2.2.1
                                have p5238_3 := h5238c.2.2.2
                                linarith only [h4914, hlam, p5238_0]
                              · have p5238_0 := h5238c.1
                                have p5238_1 := h5238c.2.1
                                have p5238_2 := h5238c.2.2.1
                                have p5238_3 := h5238c.2.2.2
                                linarith only [h4916, hlam, p5238_0]
                              · have p5238_0 := h5238c.1
                                have p5238_1 := h5238c.2.1
                                have p5238_2 := h5238c.2.2.1
                                have p5238_3 := h5238c.2.2.2
                                linarith only [h5, hlam, p5238_0]
                              · have p5238_0 := h5238c.1
                                have p5238_1 := h5238c.2.1
                                have p5238_2 := h5238c.2.2.1
                                have p5238_3 := h5238c.2.2.2
                                linarith only [h4907, hlam, p5238_0]
                              · have p5238_0 := h5238c.1
                                have p5238_1 := h5238c.2.1
                                have p5238_2 := h5238c.2.2.1
                                have p5238_3 := h5238c.2.2.2
                                linarith only [h4913, h4918, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5238_1]
                              · have p5238_0 := h5238c.1
                                have p5238_1 := h5238c.2.1
                                have p5238_2 := h5238c.2.2.1
                                have p5238_3 := h5238c.2.2.2
                                linarith only [hlam, p5238_0]
                              · have p5238_0 := h5238c.1
                                have p5238_1 := h5238c.2.1
                                have p5238_2 := h5238c.2.2.1
                                have p5238_3 := h5238c.2.2.2
                                linarith only [h4918, hlam, p5238_1]
                              · have p5238_0 := h5238c.1
                                have p5238_1 := h5238c.2.1
                                have p5238_2 := h5238c.2.2.1
                                have p5238_3 := h5238c.2.2.2
                                linarith only [h6, hlam, p5238_0]
                              · have p5238_0 := h5238c.1
                                have p5238_1 := h5238c.2.1
                                have p5238_2 := h5238c.2.2.1
                                have p5238_3 := h5238c.2.2.2
                                linarith only [h4908, hlam, p5238_0]
                              · have p5238_0 := h5238c.1
                                have p5238_1 := h5238c.2.1
                                have p5238_2 := h5238c.2.2.1
                                have p5238_3 := h5238c.2.2.2
                                linarith only [h0, h4908, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5238_1]
                              · have p5238_0 := h5238c.1
                                have p5238_1 := h5238c.2.1
                                have p5238_2 := h5238c.2.2.1
                                have p5238_3 := h5238c.2.2.2
                                linarith only [h0, h4907, h4913, h4918, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p5238_1]
                              · have p5238_0 := h5238c.1
                                have p5238_1 := h5238c.2.1
                                have p5238_2 := h5238c.2.2.1
                                have p5238_3 := h5238c.2.2.2
                                linarith only [hlam, p5238_0]
                            · linarith only [h4388, h5237, hlam]
                          · linarith only [h5236, h7, hlam]
                      · linarith only [h4, h5233, hlam]
                    · linarith only [h1, h5232, hlam]
                  · have p5175_0 := h5175c.1
                    have p5175_1 := h5175c.2.1
                    have p5175_2 := h5175c.2.2.1
                    have p5175_3 := h5175c.2.2.2
                    linarith only [h4905, hlam, p5175_1]
                  · have p5175_0 := h5175c.1
                    have p5175_1 := h5175c.2.1
                    have p5175_2 := h5175c.2.2.1
                    have p5175_3 := h5175c.2.2.2
                    linarith only [hlam, p5175_0]
                · linarith only [h2, h4913, h5174, h7, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h5336 | h5336
          · linarith only [h4905, h4906, h4909, h4913, h5336, h7, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5338 | h5338
            · linarith only [h1, h4388, h4906, h5338, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h5340 | h5340
              · linarith only [h0, h4907, h4909, h4913, h5340, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h5342 | h5342
                · rcases h0bigk with h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c
                  · have p5343_0 := h5343c.1
                    have p5343_1 := h5343c.2.1
                    have p5343_2 := h5343c.2.2.1
                    have p5343_3 := h5343c.2.2.2
                    linarith only [hlam, p5343_0]
                  · have p5343_0 := h5343c.1
                    have p5343_1 := h5343c.2.1
                    have p5343_2 := h5343c.2.2.1
                    have p5343_3 := h5343c.2.2.2
                    linarith only [h4905, h4906, h4909, h4913, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5343_1]
                  · have p5343_0 := h5343c.1
                    have p5343_1 := h5343c.2.1
                    have p5343_2 := h5343c.2.2.1
                    have p5343_3 := h5343c.2.2.2
                    rcases p5343_3 (m.d 0 1) (by simp) with h5346 | h5346
                    · rcases p5343_3 (m.d 0 2) (by simp) with h5347 | h5347
                      · linarith only [h0, h5347, hlam]
                      · linarith only [h4, h5347, hlam]
                    · linarith only [h1, h5346, hlam]
                  · have p5343_0 := h5343c.1
                    have p5343_1 := h5343c.2.1
                    have p5343_2 := h5343c.2.2.1
                    have p5343_3 := h5343c.2.2.2
                    linarith only [h4905, h4906, h4909, h4913, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5343_1]
                  · have p5343_0 := h5343c.1
                    have p5343_1 := h5343c.2.1
                    have p5343_2 := h5343c.2.2.1
                    have p5343_3 := h5343c.2.2.2
                    rcases p5343_3 (m.d 0 1) (by simp) with h5352 | h5352
                    · rcases p5343_3 (m.d 0 2) (by simp) with h5353 | h5353
                      · linarith only [h0, h5353, hlam]
                      · linarith only [h5353, h6, hlam]
                    · linarith only [h3, h5352, hlam]
                  · have p5343_0 := h5343c.1
                    have p5343_1 := h5343c.2.1
                    have p5343_2 := h5343c.2.2.1
                    have p5343_3 := h5343c.2.2.2
                    linarith only [h0, hlam, p5343_0]
                  · have p5343_0 := h5343c.1
                    have p5343_1 := h5343c.2.1
                    have p5343_2 := h5343c.2.2.1
                    have p5343_3 := h5343c.2.2.2
                    linarith only [hlam, p5343_0]
                  · have p5343_0 := h5343c.1
                    have p5343_1 := h5343c.2.1
                    have p5343_2 := h5343c.2.2.1
                    have p5343_3 := h5343c.2.2.2
                    rcases p5343_3 (m.d 0 1) (by simp) with h5359 | h5359
                    · rcases p5343_3 (m.d 0 2) (by simp) with h5360 | h5360
                      · rcases p5343_3 (m.d 0 3) (by simp) with h5361 | h5361
                        · linarith only [h4, h5361, hlam]
                        · rcases p5343_3 (m.d 0 4) (by simp) with h5363 | h5363
                          · linarith only [h5, h5363, hlam]
                          · linarith only [h5363, h7, hlam]
                      · linarith only [h4, h5360, hlam]
                    · linarith only [h1, h5359, hlam]
                  · have p5343_0 := h5343c.1
                    have p5343_1 := h5343c.2.1
                    have p5343_2 := h5343c.2.2.1
                    have p5343_3 := h5343c.2.2.2
                    linarith only [h4905, h4906, h4909, h4913, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5343_1]
                  · have p5343_0 := h5343c.1
                    have p5343_1 := h5343c.2.1
                    have p5343_2 := h5343c.2.2.1
                    have p5343_3 := h5343c.2.2.2
                    rcases p5343_3 (m.d 0 1) (by simp) with h5369 | h5369
                    · rcases p5343_3 (m.d 0 2) (by simp) with h5370 | h5370
                      · rcases p5343_3 (m.d 0 3) (by simp) with h5371 | h5371
                        · linarith only [h4, h5371, hlam]
                        · rcases p5343_3 (m.d 0 4) (by simp) with h5373 | h5373
                          · linarith only [h5, h5373, hlam]
                          · linarith only [h4905, h5373, hlam]
                      · linarith only [h5370, h6, hlam]
                    · linarith only [h3, h5369, hlam]
                  · have p5343_0 := h5343c.1
                    have p5343_1 := h5343c.2.1
                    have p5343_2 := h5343c.2.2.1
                    have p5343_3 := h5343c.2.2.2
                    linarith only [h1, hlam, p5343_1]
                  · have p5343_0 := h5343c.1
                    have p5343_1 := h5343c.2.1
                    have p5343_2 := h5343c.2.2.1
                    have p5343_3 := h5343c.2.2.2
                    linarith only [h4, hlam, p5343_1]
                  · have p5343_0 := h5343c.1
                    have p5343_1 := h5343c.2.1
                    have p5343_2 := h5343c.2.2.1
                    have p5343_3 := h5343c.2.2.2
                    linarith only [hlam, p5343_0]
                  · have p5343_0 := h5343c.1
                    have p5343_1 := h5343c.2.1
                    have p5343_2 := h5343c.2.2.1
                    have p5343_3 := h5343c.2.2.2
                    linarith only [h7, hlam, p5343_1]
                  · have p5343_0 := h5343c.1
                    have p5343_1 := h5343c.2.1
                    have p5343_2 := h5343c.2.2.1
                    have p5343_3 := h5343c.2.2.2
                    linarith only [h4388, hlam, p5343_1]
                  · have p5343_0 := h5343c.1
                    have p5343_1 := h5343c.2.1
                    have p5343_2 := h5343c.2.2.1
                    have p5343_3 := h5343c.2.2.2
                    linarith only [h2, hlam, p5343_0]
                  · have p5343_0 := h5343c.1
                    have p5343_1 := h5343c.2.1
                    have p5343_2 := h5343c.2.2.1
                    have p5343_3 := h5343c.2.2.2
                    linarith only [h5, hlam, p5343_0]
                  · have p5343_0 := h5343c.1
                    have p5343_1 := h5343c.2.1
                    have p5343_2 := h5343c.2.2.1
                    have p5343_3 := h5343c.2.2.2
                    rcases p5343_3 (m.d 0 1) (by simp) with h5385 | h5385
                    · rcases p5343_3 (m.d 0 2) (by simp) with h5386 | h5386
                      · rcases p5343_3 (m.d 0 3) (by simp) with h5387 | h5387
                        · linarith only [h5387, h7, hlam]
                        · rcases p5343_3 (m.d 0 4) (by simp) with h5389 | h5389
                          · rcases p5343_3 (m.d 0 5) (by simp) with h5390 | h5390
                            · linarith only [h4905, h5390, hlam]
                            · linarith only [h4388, h5390, hlam]
                          · linarith only [h5389, h7, hlam]
                      · linarith only [h4, h5386, hlam]
                    · linarith only [h1, h5385, hlam]
                  · have p5343_0 := h5343c.1
                    have p5343_1 := h5343c.2.1
                    have p5343_2 := h5343c.2.2.1
                    have p5343_3 := h5343c.2.2.2
                    linarith only [hlam, p5343_0]
                  · have p5343_0 := h5343c.1
                    have p5343_1 := h5343c.2.1
                    have p5343_2 := h5343c.2.2.1
                    have p5343_3 := h5343c.2.2.2
                    linarith only [h4905, h4906, h4909, h4913, h7, hc23, hc34, hlam, hphi, p5343_1]
                  · have p5343_0 := h5343c.1
                    have p5343_1 := h5343c.2.1
                    have p5343_2 := h5343c.2.2.1
                    have p5343_3 := h5343c.2.2.2
                    linarith only [h3, hlam, p5343_0]
                  · have p5343_0 := h5343c.1
                    have p5343_1 := h5343c.2.1
                    have p5343_2 := h5343c.2.2.1
                    have p5343_3 := h5343c.2.2.2
                    linarith only [h6, hlam, p5343_1]
                  · have p5343_0 := h5343c.1
                    have p5343_1 := h5343c.2.1
                    have p5343_2 := h5343c.2.2.1
                    have p5343_3 := h5343c.2.2.2
                    rcases p5343_3 (m.d 0 1) (by simp) with h5400 | h5400
                    · rcases p5343_3 (m.d 0 2) (by simp) with h5401 | h5401
                      · rcases p5343_3 (m.d 0 3) (by simp) with h5402 | h5402
                        · linarith only [h4388, h5402, hlam]
                        · rcases p5343_3 (m.d 0 4) (by simp) with h5404 | h5404
                          · rcases p5343_3 (m.d 0 5) (by simp) with h5405 | h5405
                            · rcases h2bigk with h5406c | h5406c | h5406c | h5406c | h5406c | h5406c | h5406c | h5406c | h5406c | h5406c | h5406c | h5406c | h5406c | h5406c | h5406c | h5406c | h5406c | h5406c | h5406c | h5406c | h5406c | h5406c | h5406c | h5406c | h5406c
                              · have p5406_0 := h5406c.1
                                have p5406_1 := h5406c.2.1
                                have p5406_2 := h5406c.2.2.1
                                have p5406_3 := h5406c.2.2.2
                                linarith only [hlam, p5406_0]
                              · have p5406_0 := h5406c.1
                                have p5406_1 := h5406c.2.1
                                have p5406_2 := h5406c.2.2.1
                                have p5406_3 := h5406c.2.2.2
                                rcases p5406_3 (m.d 0 2) (by simp) with h5408 | h5408
                                · rcases p5406_3 (m.d 1 2) (by simp) with h5409 | h5409
                                  · linarith only [h0, h5409, hlam]
                                  · rcases p5406_3 (m.d 2 3) (by simp) with h5411 | h5411
                                    · linarith only [h4, h5411, hlam]
                                    · rcases p5406_3 (m.d 2 4) (by simp) with h5413 | h5413
                                      · linarith only [h5, h5413, hlam]
                                      · rcases p5406_3 (m.d 2 5) (by simp) with h5415 | h5415
                                        · linarith only [h5415, h6, hlam]
                                        · rcases h3bigk with h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c
                                          · have p5417_0 := h5417c.1
                                            have p5417_1 := h5417c.2.1
                                            have p5417_2 := h5417c.2.2.1
                                            have p5417_3 := h5417c.2.2.2
                                            linarith only [hlam, p5417_0]
                                          · have p5417_0 := h5417c.1
                                            have p5417_1 := h5417c.2.1
                                            have p5417_2 := h5417c.2.2.1
                                            have p5417_3 := h5417c.2.2.2
                                            linarith only [h4906, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5343_1, p5417_1]
                                          · have p5417_0 := h5417c.1
                                            have p5417_1 := h5417c.2.1
                                            have p5417_2 := h5417c.2.2.1
                                            have p5417_3 := h5417c.2.2.2
                                            linarith only [h4388, hc23, hc35, hlam, hphi, p5343_1, p5417_1]
                                          · have p5417_0 := h5417c.1
                                            have p5417_1 := h5417c.2.1
                                            have p5417_2 := h5417c.2.2.1
                                            have p5417_3 := h5417c.2.2.2
                                            linarith only [h7, hlam, p5417_0]
                                          · have p5417_0 := h5417c.1
                                            have p5417_1 := h5417c.2.1
                                            have p5417_2 := h5417c.2.2.1
                                            have p5417_3 := h5417c.2.2.2
                                            linarith only [h4388, hlam, p5417_0]
                                          · have p5417_0 := h5417c.1
                                            have p5417_1 := h5417c.2.1
                                            have p5417_2 := h5417c.2.2.1
                                            have p5417_3 := h5417c.2.2.2
                                            linarith only [h1, hlam, p5417_0]
                                          · have p5417_0 := h5417c.1
                                            have p5417_1 := h5417c.2.1
                                            have p5417_2 := h5417c.2.2.1
                                            have p5417_3 := h5417c.2.2.2
                                            linarith only [hlam, p5417_0]
                                          · have p5417_0 := h5417c.1
                                            have p5417_1 := h5417c.2.1
                                            have p5417_2 := h5417c.2.2.1
                                            have p5417_3 := h5417c.2.2.2
                                            linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5417_1]
                                          · have p5417_0 := h5417c.1
                                            have p5417_1 := h5417c.2.1
                                            have p5417_2 := h5417c.2.2.1
                                            have p5417_3 := h5417c.2.2.2
                                            linarith only [h4909, hlam, p5417_0]
                                          · have p5417_0 := h5417c.1
                                            have p5417_1 := h5417c.2.1
                                            have p5417_2 := h5417c.2.2.1
                                            have p5417_3 := h5417c.2.2.2
                                            linarith only [h4911, hlam, p5417_0]
                                          · have p5417_0 := h5417c.1
                                            have p5417_1 := h5417c.2.1
                                            have p5417_2 := h5417c.2.2.1
                                            have p5417_3 := h5417c.2.2.2
                                            linarith only [h4, hlam, p5417_0]
                                          · have p5417_0 := h5417c.1
                                            have p5417_1 := h5417c.2.1
                                            have p5417_2 := h5417c.2.2.1
                                            have p5417_3 := h5417c.2.2.2
                                            linarith only [h4906, hlam, p5417_0]
                                          · have p5417_0 := h5417c.1
                                            have p5417_1 := h5417c.2.1
                                            have p5417_2 := h5417c.2.2.1
                                            have p5417_3 := h5417c.2.2.2
                                            linarith only [hlam, p5417_0]
                                          · have p5417_0 := h5417c.1
                                            have p5417_1 := h5417c.2.1
                                            have p5417_2 := h5417c.2.2.1
                                            have p5417_3 := h5417c.2.2.2
                                            linarith only [h5336, hlam, p5417_0]
                                          · have p5417_0 := h5417c.1
                                            have p5417_1 := h5417c.2.1
                                            have p5417_2 := h5417c.2.2.1
                                            have p5417_3 := h5417c.2.2.2
                                            linarith only [h5338, hlam, p5417_0]
                                          · have p5417_0 := h5417c.1
                                            have p5417_1 := h5417c.2.1
                                            have p5417_2 := h5417c.2.2.1
                                            have p5417_3 := h5417c.2.2.2
                                            linarith only [hc03, hc34, hlam, hphi, p5417_1]
                                          · have p5417_0 := h5417c.1
                                            have p5417_1 := h5417c.2.1
                                            have p5417_2 := h5417c.2.2.1
                                            have p5417_3 := h5417c.2.2.2
                                            linarith only [h4906, hc23, hc34, hlam, hphi, p5417_1]
                                          · have p5417_0 := h5417c.1
                                            have p5417_1 := h5417c.2.1
                                            have p5417_2 := h5417c.2.2.1
                                            have p5417_3 := h5417c.2.2.2
                                            linarith only [hc23, hc34, hlam, hphi, p5417_1]
                                          · have p5417_0 := h5417c.1
                                            have p5417_1 := h5417c.2.1
                                            have p5417_2 := h5417c.2.2.1
                                            have p5417_3 := h5417c.2.2.2
                                            linarith only [hlam, p5417_0]
                                          · have p5417_0 := h5417c.1
                                            have p5417_1 := h5417c.2.1
                                            have p5417_2 := h5417c.2.2.1
                                            have p5417_3 := h5417c.2.2.2
                                            linarith only [h1, h4388, h4906, hc23, hc34, hlam, hphi, p5417_1]
                                          · have p5417_0 := h5417c.1
                                            have p5417_1 := h5417c.2.1
                                            have p5417_2 := h5417c.2.2.1
                                            have p5417_3 := h5417c.2.2.2
                                            linarith only [h1, h4906, hc23, hc35, hlam, hphi, p5417_1]
                                          · have p5417_0 := h5417c.1
                                            have p5417_1 := h5417c.2.1
                                            have p5417_2 := h5417c.2.2.1
                                            have p5417_3 := h5417c.2.2.2
                                            linarith only [h4906, hc23, hc35, hlam, hphi, p5417_1]
                                          · have p5417_0 := h5417c.1
                                            have p5417_1 := h5417c.2.1
                                            have p5417_2 := h5417c.2.2.1
                                            have p5417_3 := h5417c.2.2.2
                                            linarith only [hc23, hc35, hlam, hphi, p5417_1]
                                          · have p5417_0 := h5417c.1
                                            have p5417_1 := h5417c.2.1
                                            have p5417_2 := h5417c.2.2.1
                                            have p5417_3 := h5417c.2.2.2
                                            linarith only [h5342, hlam, p5417_0]
                                          · have p5417_0 := h5417c.1
                                            have p5417_1 := h5417c.2.1
                                            have p5417_2 := h5417c.2.2.1
                                            have p5417_3 := h5417c.2.2.2
                                            linarith only [hlam, p5417_0]
                                · linarith only [h0, h5408, hlam]
                              · have p5406_0 := h5406c.1
                                have p5406_1 := h5406c.2.1
                                have p5406_2 := h5406c.2.2.1
                                have p5406_3 := h5406c.2.2.2
                                rcases p5406_3 (m.d 0 2) (by simp) with h5444 | h5444
                                · rcases p5406_3 (m.d 1 2) (by simp) with h5445 | h5445
                                  · linarith only [h0, h5445, hlam]
                                  · linarith only [h4906, h5445, hlam]
                                · linarith only [h5444, hlam, p5406_0]
                              · have p5406_0 := h5406c.1
                                have p5406_1 := h5406c.2.1
                                have p5406_2 := h5406c.2.2.1
                                have p5406_3 := h5406c.2.2.2
                                rcases p5406_3 (m.d 0 2) (by simp) with h5449 | h5449
                                · rcases p5406_3 (m.d 1 2) (by simp) with h5450 | h5450
                                  · linarith only [h0, h5450, hlam]
                                  · linarith only [h4907, h5450, hlam]
                                · linarith only [h5449, hlam, p5406_0]
                              · have p5406_0 := h5406c.1
                                have p5406_1 := h5406c.2.1
                                have p5406_2 := h5406c.2.2.1
                                have p5406_3 := h5406c.2.2.2
                                rcases p5406_3 (m.d 0 2) (by simp) with h5454 | h5454
                                · rcases p5406_3 (m.d 1 2) (by simp) with h5455 | h5455
                                  · linarith only [h0, h5455, hlam]
                                  · linarith only [h4908, h5455, hlam]
                                · linarith only [h5454, hlam, p5406_0]
                              · have p5406_0 := h5406c.1
                                have p5406_1 := h5406c.2.1
                                have p5406_2 := h5406c.2.2.1
                                have p5406_3 := h5406c.2.2.2
                                linarith only [h0, hlam, p5406_0]
                              · have p5406_0 := h5406c.1
                                have p5406_1 := h5406c.2.1
                                have p5406_2 := h5406c.2.2.1
                                have p5406_3 := h5406c.2.2.2
                                linarith only [hlam, p5406_0]
                              · have p5406_0 := h5406c.1
                                have p5406_1 := h5406c.2.1
                                have p5406_2 := h5406c.2.2.1
                                have p5406_3 := h5406c.2.2.2
                                rcases p5406_3 (m.d 0 2) (by simp) with h5461 | h5461
                                · rcases p5406_3 (m.d 1 2) (by simp) with h5462 | h5462
                                  · rcases p5406_3 (m.d 2 3) (by simp) with h5463 | h5463
                                    · linarith only [h5463, hlam, p5406_0]
                                    · rcases p5406_3 (m.d 2 4) (by simp) with h5465 | h5465
                                      · linarith only [h4907, h5465, hlam]
                                      · linarith only [h5336, h5465, hlam]
                                  · linarith only [h5462, hlam, p5406_0]
                                · linarith only [h4, h5461, hlam]
                              · have p5406_0 := h5406c.1
                                have p5406_1 := h5406c.2.1
                                have p5406_2 := h5406c.2.2.1
                                have p5406_3 := h5406c.2.2.2
                                rcases p5406_3 (m.d 0 2) (by simp) with h5470 | h5470
                                · rcases p5406_3 (m.d 1 2) (by simp) with h5471 | h5471
                                  · rcases p5406_3 (m.d 2 3) (by simp) with h5472 | h5472
                                    · linarith only [h4906, h5472, hlam]
                                    · rcases p5406_3 (m.d 2 4) (by simp) with h5474 | h5474
                                      · linarith only [h5474, hlam, p5406_0]
                                      · rcases p5406_3 (m.d 2 5) (by simp) with h5476 | h5476
                                        · linarith only [h4908, h5476, hlam]
                                        · linarith only [h5340, h5476, hlam]
                                  · linarith only [h5471, hlam, p5406_0]
                                · linarith only [h5, h5470, hlam]
                              · have p5406_0 := h5406c.1
                                have p5406_1 := h5406c.2.1
                                have p5406_2 := h5406c.2.2.1
                                have p5406_3 := h5406c.2.2.2
                                rcases p5406_3 (m.d 0 2) (by simp) with h5481 | h5481
                                · rcases p5406_3 (m.d 1 2) (by simp) with h5482 | h5482
                                  · rcases p5406_3 (m.d 2 3) (by simp) with h5483 | h5483
                                    · linarith only [h4906, h5483, hlam]
                                    · rcases p5406_3 (m.d 2 4) (by simp) with h5485 | h5485
                                      · linarith only [h4907, h5485, hlam]
                                      · rcases p5406_3 (m.d 2 5) (by simp) with h5487 | h5487
                                        · linarith only [h5487, hlam, p5406_0]
                                        · rcases h3bigk with h5489c | h5489c | h5489c | h5489c | h5489c | h5489c | h5489c | h5489c | h5489c | h5489c | h5489c | h5489c | h5489c | h5489c | h5489c | h5489c | h5489c | h5489c | h5489c | h5489c | h5489c | h5489c | h5489c | h5489c | h5489c
                                          · have p5489_0 := h5489c.1
                                            have p5489_1 := h5489c.2.1
                                            have p5489_2 := h5489c.2.2.1
                                            have p5489_3 := h5489c.2.2.2
                                            linarith only [hlam, p5489_0]
                                          · have p5489_0 := h5489c.1
                                            have p5489_1 := h5489c.2.1
                                            have p5489_2 := h5489c.2.2.1
                                            have p5489_3 := h5489c.2.2.2
                                            linarith only [h4906, h7, hc23, hc34, hlam, hphi, p5489_1]
                                          · have p5489_0 := h5489c.1
                                            have p5489_1 := h5489c.2.1
                                            have p5489_2 := h5489c.2.2.1
                                            have p5489_3 := h5489c.2.2.2
                                            linarith only [h7, hc23, hc34, hlam, hphi, p5489_1]
                                          · have p5489_0 := h5489c.1
                                            have p5489_1 := h5489c.2.1
                                            have p5489_2 := h5489c.2.2.1
                                            have p5489_3 := h5489c.2.2.2
                                            linarith only [h7, hlam, p5489_0]
                                          · have p5489_0 := h5489c.1
                                            have p5489_1 := h5489c.2.1
                                            have p5489_2 := h5489c.2.2.1
                                            have p5489_3 := h5489c.2.2.2
                                            linarith only [h4388, hlam, p5489_0]
                                          · have p5489_0 := h5489c.1
                                            have p5489_1 := h5489c.2.1
                                            have p5489_2 := h5489c.2.2.1
                                            have p5489_3 := h5489c.2.2.2
                                            linarith only [h1, hlam, p5489_0]
                                          · have p5489_0 := h5489c.1
                                            have p5489_1 := h5489c.2.1
                                            have p5489_2 := h5489c.2.2.1
                                            have p5489_3 := h5489c.2.2.2
                                            linarith only [hlam, p5489_0]
                                          · have p5489_0 := h5489c.1
                                            have p5489_1 := h5489c.2.1
                                            have p5489_2 := h5489c.2.2.1
                                            have p5489_3 := h5489c.2.2.2
                                            linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5489_1]
                                          · have p5489_0 := h5489c.1
                                            have p5489_1 := h5489c.2.1
                                            have p5489_2 := h5489c.2.2.1
                                            have p5489_3 := h5489c.2.2.2
                                            linarith only [h4909, hlam, p5489_0]
                                          · have p5489_0 := h5489c.1
                                            have p5489_1 := h5489c.2.1
                                            have p5489_2 := h5489c.2.2.1
                                            have p5489_3 := h5489c.2.2.2
                                            linarith only [h4911, hlam, p5489_0]
                                          · have p5489_0 := h5489c.1
                                            have p5489_1 := h5489c.2.1
                                            have p5489_2 := h5489c.2.2.1
                                            have p5489_3 := h5489c.2.2.2
                                            linarith only [h4, hlam, p5489_0]
                                          · have p5489_0 := h5489c.1
                                            have p5489_1 := h5489c.2.1
                                            have p5489_2 := h5489c.2.2.1
                                            have p5489_3 := h5489c.2.2.2
                                            linarith only [h4906, hlam, p5489_0]
                                          · have p5489_0 := h5489c.1
                                            have p5489_1 := h5489c.2.1
                                            have p5489_2 := h5489c.2.2.1
                                            have p5489_3 := h5489c.2.2.2
                                            linarith only [hlam, p5489_0]
                                          · have p5489_0 := h5489c.1
                                            have p5489_1 := h5489c.2.1
                                            have p5489_2 := h5489c.2.2.1
                                            have p5489_3 := h5489c.2.2.2
                                            linarith only [h5336, hlam, p5489_0]
                                          · have p5489_0 := h5489c.1
                                            have p5489_1 := h5489c.2.1
                                            have p5489_2 := h5489c.2.2.1
                                            have p5489_3 := h5489c.2.2.2
                                            linarith only [h5338, hlam, p5489_0]
                                          · have p5489_0 := h5489c.1
                                            have p5489_1 := h5489c.2.1
                                            have p5489_2 := h5489c.2.2.1
                                            have p5489_3 := h5489c.2.2.2
                                            linarith only [hc03, hc34, hlam, hphi, p5489_1]
                                          · have p5489_0 := h5489c.1
                                            have p5489_1 := h5489c.2.1
                                            have p5489_2 := h5489c.2.2.1
                                            have p5489_3 := h5489c.2.2.2
                                            linarith only [hc13, hc34, hlam, hphi, p5489_1]
                                          · have p5489_0 := h5489c.1
                                            have p5489_1 := h5489c.2.1
                                            have p5489_2 := h5489c.2.2.1
                                            have p5489_3 := h5489c.2.2.2
                                            linarith only [hc23, hc34, hlam, hphi, p5489_1]
                                          · have p5489_0 := h5489c.1
                                            have p5489_1 := h5489c.2.1
                                            have p5489_2 := h5489c.2.2.1
                                            have p5489_3 := h5489c.2.2.2
                                            linarith only [hlam, p5489_0]
                                          · have p5489_0 := h5489c.1
                                            have p5489_1 := h5489c.2.1
                                            have p5489_2 := h5489c.2.2.1
                                            have p5489_3 := h5489c.2.2.2
                                            linarith only [h4388, hc03, hc34, hlam, hphi, p5489_1]
                                          · have p5489_0 := h5489c.1
                                            have p5489_1 := h5489c.2.1
                                            have p5489_2 := h5489c.2.2.1
                                            have p5489_3 := h5489c.2.2.2
                                            linarith only [hc03, hc35, hlam, hphi, p5489_1]
                                          · have p5489_0 := h5489c.1
                                            have p5489_1 := h5489c.2.1
                                            have p5489_2 := h5489c.2.2.1
                                            have p5489_3 := h5489c.2.2.2
                                            linarith only [h4906, hc23, hc35, hlam, hphi, p5489_1]
                                          · have p5489_0 := h5489c.1
                                            have p5489_1 := h5489c.2.1
                                            have p5489_2 := h5489c.2.2.1
                                            have p5489_3 := h5489c.2.2.2
                                            linarith only [hc23, hc35, hlam, hphi, p5489_1]
                                          · have p5489_0 := h5489c.1
                                            have p5489_1 := h5489c.2.1
                                            have p5489_2 := h5489c.2.2.1
                                            have p5489_3 := h5489c.2.2.2
                                            linarith only [h5342, hlam, p5489_0]
                                          · have p5489_0 := h5489c.1
                                            have p5489_1 := h5489c.2.1
                                            have p5489_2 := h5489c.2.2.1
                                            have p5489_3 := h5489c.2.2.2
                                            linarith only [hlam, p5489_0]
                                  · linarith only [h5482, hlam, p5406_0]
                                · linarith only [h5481, h6, hlam]
                              · have p5406_0 := h5406c.1
                                have p5406_1 := h5406c.2.1
                                have p5406_2 := h5406c.2.2.1
                                have p5406_3 := h5406c.2.2.2
                                linarith only [h4, hlam, p5406_0]
                              · have p5406_0 := h5406c.1
                                have p5406_1 := h5406c.2.1
                                have p5406_2 := h5406c.2.2.1
                                have p5406_3 := h5406c.2.2.2
                                linarith only [h4906, hlam, p5406_0]
                              · have p5406_0 := h5406c.1
                                have p5406_1 := h5406c.2.1
                                have p5406_2 := h5406c.2.2.1
                                have p5406_3 := h5406c.2.2.2
                                linarith only [hlam, p5406_0]
                              · have p5406_0 := h5406c.1
                                have p5406_1 := h5406c.2.1
                                have p5406_2 := h5406c.2.2.1
                                have p5406_3 := h5406c.2.2.2
                                linarith only [h5336, hlam, p5406_0]
                              · have p5406_0 := h5406c.1
                                have p5406_1 := h5406c.2.1
                                have p5406_2 := h5406c.2.2.1
                                have p5406_3 := h5406c.2.2.2
                                linarith only [h5338, hlam, p5406_0]
                              · have p5406_0 := h5406c.1
                                have p5406_1 := h5406c.2.1
                                have p5406_2 := h5406c.2.2.1
                                have p5406_3 := h5406c.2.2.2
                                linarith only [h5, hlam, p5406_0]
                              · have p5406_0 := h5406c.1
                                have p5406_1 := h5406c.2.1
                                have p5406_2 := h5406c.2.2.1
                                have p5406_3 := h5406c.2.2.2
                                linarith only [h4907, hlam, p5406_0]
                              · have p5406_0 := h5406c.1
                                have p5406_1 := h5406c.2.1
                                have p5406_2 := h5406c.2.2.1
                                have p5406_3 := h5406c.2.2.2
                                linarith only [h0, h4907, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5406_1]
                              · have p5406_0 := h5406c.1
                                have p5406_1 := h5406c.2.1
                                have p5406_2 := h5406c.2.2.1
                                have p5406_3 := h5406c.2.2.2
                                linarith only [hlam, p5406_0]
                              · have p5406_0 := h5406c.1
                                have p5406_1 := h5406c.2.1
                                have p5406_2 := h5406c.2.2.1
                                have p5406_3 := h5406c.2.2.2
                                linarith only [h5340, hlam, p5406_1]
                              · have p5406_0 := h5406c.1
                                have p5406_1 := h5406c.2.1
                                have p5406_2 := h5406c.2.2.1
                                have p5406_3 := h5406c.2.2.2
                                linarith only [h6, hlam, p5406_0]
                              · have p5406_0 := h5406c.1
                                have p5406_1 := h5406c.2.1
                                have p5406_2 := h5406c.2.2.1
                                have p5406_3 := h5406c.2.2.2
                                linarith only [h4908, hlam, p5406_0]
                              · have p5406_0 := h5406c.1
                                have p5406_1 := h5406c.2.1
                                have p5406_2 := h5406c.2.2.1
                                have p5406_3 := h5406c.2.2.2
                                linarith only [h0, h4908, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5406_1]
                              · have p5406_0 := h5406c.1
                                have p5406_1 := h5406c.2.1
                                have p5406_2 := h5406c.2.2.1
                                have p5406_3 := h5406c.2.2.2
                                linarith only [h0, h4908, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p5406_1]
                              · have p5406_0 := h5406c.1
                                have p5406_1 := h5406c.2.1
                                have p5406_2 := h5406c.2.2.1
                                have p5406_3 := h5406c.2.2.2
                                linarith only [hlam, p5406_0]
                            · linarith only [h4388, h5405, hlam]
                          · linarith only [h5404, h7, hlam]
                      · linarith only [h4, h5401, hlam]
                    · linarith only [h1, h5400, hlam]
                  · have p5343_0 := h5343c.1
                    have p5343_1 := h5343c.2.1
                    have p5343_2 := h5343c.2.2.1
                    have p5343_3 := h5343c.2.2.2
                    linarith only [h4905, hlam, p5343_1]
                  · have p5343_0 := h5343c.1
                    have p5343_1 := h5343c.2.1
                    have p5343_2 := h5343c.2.2.1
                    have p5343_3 := h5343c.2.2.2
                    linarith only [hlam, p5343_0]
                · linarith only [h4905, h5342, h7, hlam]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h5539 | h5539
    · linarith only [h1, h5539, h7, hlam]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h5541 | h5541
      · linarith only [h4388, h4905, h4907, h4908, h5539, h5541, h6, h7, hc03, hc34, hlam, hphi]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h5543 | h5543
        · linarith only [h4907, h4908, h5543, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h5545 | h5545
          · linarith only [h1, h4905, h4906, h5543, h5545, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5547 | h5547
            · linarith only [h4388, h4907, h4908, h5545, h5547, h6, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h5549 | h5549
              · linarith only [h0, h4907, h4908, h5543, h5549, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h4905, h4907, h4908, h5545, h5549, h7, hc23, hc34, hlam, hphi]

end R2N4
